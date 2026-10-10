defmodule Accord.Pass.TLA.BuildActions do
  @moduledoc """
  TLA+ pass: IR + StateSpace → [Action].

  Each protocol transition becomes a TLA+ action. Message types become
  `\\in` preconditions with existential quantification over domains.
  Guard ASTs become enabling conditions via the GuardCompiler. Update
  ASTs become primed variable assignments. UNCHANGED is derived from
  the complement of modified variables.
  """

  alias Accord.IR
  alias Accord.IR.Transition
  alias Accord.Pass.TLA.Expr
  alias Accord.TLA.{Action, ModelConfig, Sessions, StateSpace}
  alias Pentiment.Report

  import Accord.Pass.Helpers, only: [maybe_add_source: 2, maybe_add_span_label: 3]

  @spec run(IR.t(), StateSpace.t(), ModelConfig.t()) ::
          {:ok, [Action.t()]} | {:error, [Pentiment.Report.t()]}
  def run(%IR{} = ir, %StateSpace{} = state_space, %ModelConfig{} = config) do
    all_var_names =
      state_space.variables
      |> Enum.map(& &1.name)
      |> MapSet.new()

    track_names = MapSet.new(ir.tracks, &Atom.to_string(&1.name))

    results =
      ir.states
      # Sorted for deterministic action order (map key order follows
      # atom creation order, which varies between VM runs).
      |> Enum.sort_by(fn {state_name, _state} -> state_name end)
      |> Enum.flat_map(fn {state_name, state} ->
        # Include anystate transitions for non-terminal states.
        transitions =
          if state.terminal do
            state.transitions
          else
            state.transitions ++ ir.anystate
          end

        transition_results =
          Enum.flat_map(transitions, fn transition ->
            build_actions_for_transition(
              ir,
              state_name,
              transition,
              state_space,
              config,
              all_var_names,
              track_names
            )
          end)

        transition_results ++ build_timeout_action(state_name, state, state_space, all_var_names)
      end)

    errors =
      Enum.flat_map(results, fn
        {:error, reports} -> reports
        {:ok, _action} -> []
      end)

    case errors do
      [] -> {:ok, for({:ok, action} <- results, do: action)}
      errors -> {:error, errors}
    end
  end

  defp build_actions_for_transition(
         ir,
         state_name,
         transition,
         state_space,
         config,
         all_var_names,
         track_names
       ) do
    tag = message_tag(transition.message_pattern)
    source = Atom.to_string(state_name)

    # A branching cast routes conditionally: one action per branch, with the
    # branch's `where:` added as a precondition and the branch's target as the
    # next state.
    env = %{
      ir: ir,
      state_space: state_space,
      config: config,
      all_var_names: all_var_names,
      track_names: track_names
    }

    cond do
      transition.kind == :cast and transition.branches != [] ->
        build_cast_branch_actions(env, state_name, transition, tag, source)

      # An event, or a cast that changes state (declares goto/guard/update), is a
      # one-way message with a state transition, guard, and update — the same
      # shape in TLA regardless of direction (the client/server distinction is a
      # runtime-blame concept). A plain cast falls through to the branch builder,
      # which emits it as a stuttering no-op.
      transition.kind == :event or (transition.kind == :cast and transition.to != nil) ->
        [
          build_event_action(env, state_name, transition, tag, source)
        ]

      true ->
        build_branch_actions(env, state_name, transition, tag, source)
    end
  end

  defp build_branch_actions(env, state_name, transition, tag, source) do
    %{ir: ir, state_space: state_space, all_var_names: all_var_names} = env

    # For branching transitions, create one action per branch.
    case transition.branches do
      [] ->
        # Cast — no reply, no branch.
        [
          {:ok,
           build_cast_action(ir, state_name, transition, tag, source, state_space, all_var_names)}
        ]

      branches ->
        # Count branches per target to detect action name collisions.
        target_counts =
          branches
          |> Enum.map(fn b -> resolve_next_state(b.next_state, state_name) end)
          |> Enum.frequencies()

        {actions, _seen} =
          branches
          |> Enum.with_index()
          |> Enum.map_reduce(%{}, fn {branch, b_idx}, seen ->
            target_state = resolve_next_state(branch.next_state, state_name)
            idx = Map.get(seen, target_state, 0)
            seen = Map.put(seen, target_state, idx + 1)

            suffix =
              if Map.fetch!(target_counts, target_state) > 1, do: idx, else: nil

            # The monitor gives a reply to the first branch that accepts it,
            # so this branch runs only when no earlier branch accepts the reply.
            earlier = Enum.take(branches, b_idx)

            action =
              build_call_action(
                env,
                state_name,
                transition,
                {branch, earlier},
                tag,
                source,
                suffix
              )

            {action, seen}
          end)

        actions
    end
  end

  defp build_call_action(env, state_name, transition, {branch, earlier}, tag, source, suffix) do
    %{
      ir: ir,
      state_space: state_space,
      config: config,
      all_var_names: all_var_names,
      track_names: track_names
    } = env

    target_state = resolve_next_state(branch.next_state, state_name)
    target = Atom.to_string(target_state)
    sessions = state_space.sessions

    action_name = build_action_name(tag, source, target, suffix)

    # Build existential variables for message parameters. In a
    # multi-session model the acting session is the first existential;
    # positional bindings (update/constraint params) use the message
    # existentials only.
    {msg_existentials, param_bindings} =
      build_existentials(transition, config)

    # Preconditions.
    preconditions = [~s(#{Sessions.read(sessions, "state")} = "#{source}")]

    # Guard condition.
    guard_result =
      compile_guard(
        ir,
        transition,
        guard_bindings(transition, param_bindings, msg_existentials),
        track_names,
        sessions
      )

    # One existential for each reply position that the update, the
    # `where:`, or an earlier branch reads.
    plan = reply_plan(transition, branch, earlier, config)

    update_bindings =
      param_bindings
      |> Map.merge(update_message_bindings(transition, msg_existentials))
      |> Map.merge(plan.update)

    # Constraint precondition from where clause.
    constraint_result =
      compile_branch_constraint(ir, branch, plan.constraint, track_names, sessions)

    # First-match selection: no earlier branch accepts this reply.
    first_match_result =
      compile_first_match(ir, transition, branch, plan, track_names, sessions)

    # Track updates from update AST.
    track_primed_result =
      build_track_primed(ir, transition, branch, update_bindings, track_names, sessions)

    # Collect errors from every failing site, not just the first.
    errors =
      [guard_result, constraint_result, first_match_result, track_primed_result]
      |> Enum.flat_map(fn
        {:error, reports} -> reports
        {:ok, _} -> []
      end)

    if errors != [] do
      {:error, errors}
    else
      {:ok, guard_precondition} = guard_result
      {:ok, constraint_precondition} = constraint_result
      {:ok, first_match_precondition} = first_match_result
      {:ok, track_primed} = track_primed_result

      existential_vars =
        session_existentials(sessions) ++ msg_existentials ++ plan.existentials

      # Primed assignments.
      primed = %{"state" => Sessions.assign(sessions, "state", ~s("#{target}"))}

      # Correspondence counter updates.
      correspondence_primed =
        build_correspondence_primed(tag, source, target, state_space)

      all_primed =
        primed
        |> Map.merge(track_primed)
        |> Map.merge(correspondence_primed)

      # UNCHANGED: variables not in primed set.
      unchanged =
        all_var_names
        |> MapSet.difference(MapSet.new(Map.keys(all_primed)))
        |> MapSet.to_list()
        |> Enum.sort()

      {:ok,
       %Action{
         name: action_name,
         source_state: source,
         target_state: target,
         message_tag: tag,
         preconditions:
           preconditions ++
             guard_precondition ++ constraint_precondition ++ first_match_precondition,
         existential_vars: existential_vars,
         primed: all_primed,
         unchanged: unchanged,
         comment: "#{tag} from #{source} to #{target}"
       }}
    end
  end

  defp compile_guard(ir, transition, param_bindings, track_names, sessions) do
    case transition.guard do
      %{ast: ast} = guard when not is_nil(ast) ->
        span = Map.get(guard, :span) || transition.span

        case Expr.compile(ast, param_bindings,
               ir: ir,
               code: "E041",
               context: "guard",
               track_names: track_names,
               span: span,
               render_field: Sessions.render_field(sessions)
             ) do
          {:ok, tla} -> {:ok, [tla]}
          {:error, reports} -> {:error, reports}
        end

      _ ->
        {:ok, []}
    end
  end

  # The acting session, existentially quantified (multi-session only).
  defp session_existentials(sessions) do
    if Sessions.multi?(sessions) do
      [{sessions.var, "Sessions"}]
    else
      []
    end
  end

  defp build_cast_action(_ir, _state_name, _transition, tag, source, state_space, all_var_names) do
    # Casts don't change state (stay in same state). With no primed
    # variables the action is a pure stuttering step — semantically a
    # no-op for TLC, kept for spec readability.
    target = source
    sessions = state_space.sessions
    action_name = "Cast#{camelize(tag)}From#{camelize(source)}"

    unchanged = all_var_names |> MapSet.to_list() |> Enum.sort()

    %Action{
      name: action_name,
      source_state: source,
      target_state: target,
      message_tag: tag,
      preconditions: [~s(#{Sessions.read(sessions, "state")} = "#{source}")],
      existential_vars: session_existentials(sessions),
      primed: %{},
      unchanged: unchanged,
      comment: "cast #{tag} in #{source}"
    }
  end

  # A state timeout is an internal action: in the untimed model it may
  # fire whenever the state is occupied. Tracks are untouched.
  defp build_timeout_action(_state_name, %{state_timeout: nil}, _ss, _vars), do: []

  defp build_timeout_action(
         state_name,
         %{state_timeout: {_ms, target_state}},
         state_space,
         all_var_names
       ) do
    sessions = state_space.sessions
    source = Atom.to_string(state_name)
    target = Atom.to_string(target_state)

    primed = %{"state" => Sessions.assign(sessions, "state", ~s("#{target}"))}

    unchanged =
      all_var_names
      |> MapSet.difference(MapSet.new(Map.keys(primed)))
      |> MapSet.to_list()
      |> Enum.sort()

    [
      {:ok,
       %Action{
         name: "After#{camelize(source)}To#{camelize(target)}",
         source_state: source,
         target_state: target,
         message_tag: "__state_timeout__",
         preconditions: [~s(#{Sessions.read(sessions, "state")} = "#{source}")],
         existential_vars: session_existentials(sessions),
         primed: primed,
         unchanged: unchanged,
         internal: true,
         comment: "state timeout: #{source} to #{target}"
       }}
    ]
  end

  # A pushed event is one more action interleaved with client calls —
  # this is where server-push pays off in the model: TLC explores races
  # between requests and pushes that a single-direction model cannot
  # represent. Same shape as a call action minus reply existentials.
  defp build_event_action(env, state_name, transition, tag, source) do
    %{
      ir: ir,
      state_space: state_space,
      config: config,
      all_var_names: all_var_names,
      track_names: track_names
    } = env

    target_state = resolve_next_state(transition.to, state_name)
    target = Atom.to_string(target_state)
    sessions = state_space.sessions
    prefix = if transition.kind == :cast, do: "Cast", else: "Event"
    action_name = "#{prefix}#{camelize(tag)}From#{camelize(source)}To#{camelize(target)}"

    {msg_existentials, param_bindings} = build_existentials(transition, config)
    existential_vars = session_existentials(sessions) ++ msg_existentials

    guard_result =
      compile_guard(
        ir,
        transition,
        guard_bindings(transition, param_bindings, msg_existentials),
        track_names,
        sessions
      )

    # Update values may reference either the declared argument names
    # (param_bindings) or the update fn head's own names (update_bindings).
    update_bindings = update_message_bindings(transition, msg_existentials)

    track_primed_result =
      build_track_primed(
        ir,
        transition,
        nil,
        Map.merge(param_bindings, update_bindings),
        track_names,
        sessions
      )

    errors =
      [guard_result, track_primed_result]
      |> Enum.flat_map(fn
        {:error, reports} -> reports
        {:ok, _} -> []
      end)

    if errors != [] do
      {:error, errors}
    else
      {:ok, guard_precondition} = guard_result
      {:ok, track_primed} = track_primed_result

      correspondence_primed = build_correspondence_primed(tag, source, target, state_space)

      all_primed =
        %{"state" => Sessions.assign(sessions, "state", ~s("#{target}"))}
        |> Map.merge(track_primed)
        |> Map.merge(correspondence_primed)

      unchanged =
        all_var_names
        |> MapSet.difference(MapSet.new(Map.keys(all_primed)))
        |> MapSet.to_list()
        |> Enum.sort()

      {:ok,
       %Action{
         name: action_name,
         source_state: source,
         target_state: target,
         message_tag: tag,
         preconditions:
           [~s(#{Sessions.read(sessions, "state")} = "#{source}")] ++ guard_precondition,
         existential_vars: existential_vars,
         primed: all_primed,
         unchanged: unchanged,
         comment:
           "#{if transition.kind == :cast, do: "client cast", else: "server event"} #{tag} from #{source} to #{target}"
       }}
    end
  end

  # A branching cast: one action per branch. Each shares the message
  # existentials, guard, and update, and adds its own `where:` as a precondition
  # and its own target. Mirrors build_event_action per branch.
  defp build_cast_branch_actions(env, state_name, transition, tag, source) do
    %{
      ir: ir,
      state_space: state_space,
      config: config,
      all_var_names: all_var_names,
      track_names: track_names
    } = env

    sessions = state_space.sessions
    {msg_existentials, param_bindings} = build_existentials(transition, config)
    existential_vars = session_existentials(sessions) ++ msg_existentials

    guard_result =
      compile_guard(
        ir,
        transition,
        guard_bindings(transition, param_bindings, msg_existentials),
        track_names,
        sessions
      )

    update_bindings = update_message_bindings(transition, msg_existentials)
    where_env = {param_bindings, msg_existentials}

    track_primed_result =
      build_track_primed(
        ir,
        transition,
        nil,
        Map.merge(param_bindings, update_bindings),
        track_names,
        sessions
      )

    target_counts =
      transition.branches
      |> Enum.map(&resolve_next_state(&1.next_state, state_name))
      |> Enum.frequencies()

    {actions, _seen} =
      transition.branches
      |> Enum.with_index()
      |> Enum.map_reduce(%{}, fn {branch, b_idx}, seen ->
        target_state = resolve_next_state(branch.next_state, state_name)
        target = Atom.to_string(target_state)
        idx = Map.get(seen, target_state, 0)
        seen = Map.put(seen, target_state, idx + 1)
        suffix = if Map.fetch!(target_counts, target_state) > 1, do: idx, else: nil

        where_result =
          compile_cast_where(ir, transition, branch, where_env, track_names, sessions)

        # The monitor takes the first branch whose `where:` holds, so this
        # branch runs only when no earlier `where:` holds.
        first_match_result =
          transition.branches
          |> Enum.take(b_idx)
          |> compile_cast_first_match(ir, transition, where_env, track_names, sessions)

        errors =
          [guard_result, where_result, first_match_result, track_primed_result]
          |> Enum.flat_map(fn
            {:error, reports} -> reports
            {:ok, _} -> []
          end)

        action =
          if errors != [] do
            {:error, errors}
          else
            {:ok, guard_precondition} = guard_result
            {:ok, where_precondition} = where_result
            {:ok, first_match_precondition} = first_match_result
            {:ok, track_primed} = track_primed_result

            correspondence_primed = build_correspondence_primed(tag, source, target, state_space)

            all_primed =
              %{"state" => Sessions.assign(sessions, "state", ~s("#{target}"))}
              |> Map.merge(track_primed)
              |> Map.merge(correspondence_primed)

            unchanged =
              all_var_names
              |> MapSet.difference(MapSet.new(Map.keys(all_primed)))
              |> MapSet.to_list()
              |> Enum.sort()

            {:ok,
             %Action{
               name: "Cast" <> build_action_name(tag, source, target, suffix),
               source_state: source,
               target_state: target,
               message_tag: tag,
               preconditions:
                 [~s(#{Sessions.read(sessions, "state")} = "#{source}")] ++
                   guard_precondition ++ where_precondition ++ first_match_precondition,
               existential_vars: existential_vars,
               primed: all_primed,
               unchanged: unchanged,
               comment: "client cast #{tag} from #{source} to #{target}"
             }}
          end

        {action, seen}
      end)

    actions
  end

  # Compile a cast branch's `where:` (a `fn message, tracks` predicate) into a TLA
  # precondition, like a guard.
  defp compile_cast_where(
         _ir,
         _transition,
         %{constraint: nil},
         _bindings,
         _track_names,
         _sessions
       ),
       do: {:ok, []}

  defp compile_cast_where(
         ir,
         transition,
         %{constraint: %{ast: ast}} = branch,
         {param_bindings, msg_existentials},
         track_names,
         sessions
       ) do
    span = branch.span || transition.span
    bindings = Map.merge(param_bindings, head_bindings(ast, msg_existentials))

    case Expr.compile(ast, bindings,
           ir: ir,
           code: "E041",
           context: "branch",
           track_names: track_names,
           span: span,
           render_field: Sessions.render_field(sessions)
         ) do
      {:ok, tla} -> {:ok, [tla]}
      {:error, reports} -> {:error, reports}
    end
  end

  # A cast branch runs only when no earlier branch's `where:` holds. An
  # earlier branch without `where:` takes every message, so this branch
  # never runs.
  defp compile_cast_first_match([], _ir, _transition, _env, _track_names, _sessions),
    do: {:ok, []}

  defp compile_cast_first_match(earlier, ir, transition, env, track_names, sessions) do
    results =
      Enum.map(earlier, fn branch ->
        case compile_cast_where(ir, transition, branch, env, track_names, sessions) do
          {:ok, []} -> {:ok, "FALSE"}
          {:ok, [tla]} -> {:ok, "~(#{tla})"}
          error -> error
        end
      end)

    collect_preconditions(results)
  end

  defp collect_preconditions(results) do
    case Enum.flat_map(results, fn
           {:error, reports} -> reports
           {:ok, _} -> []
         end) do
      [] -> {:ok, for({:ok, tla} <- results, do: tla)}
      errors -> {:error, errors}
    end
  end

  # The message names in an update head (`fn message, ...`), bound to the
  # message existentials by position. An ignored position (`_a`) binds
  # nothing, and the names after it keep their own positions.
  defp update_message_bindings(%Transition{update: %{ast: ast}}, existentials)
       when not is_nil(ast),
       do: head_bindings(ast, existentials)

  defp update_message_bindings(_, _), do: %{}

  # The bindings of a guard: the declared argument names, and the names
  # in the guard head at their positions.
  defp guard_bindings(%Transition{guard: %{ast: ast}}, param_bindings, existentials)
       when not is_nil(ast),
       do: Map.merge(param_bindings, head_bindings(ast, existentials))

  defp guard_bindings(_, param_bindings, _), do: param_bindings

  # The names in the message pattern of a fn head (its first argument),
  # bound to the message existentials by position.
  defp head_bindings({:fn, _, [{:->, _, [[msg_pat | _], _body]}]}, existentials) do
    zip_positions(tuple_positions(msg_pat), Enum.map(existentials, &elem(&1, 0)))
  end

  defp head_bindings(_, _), do: %{}

  # The variable names of a tagged tuple pattern, by position after the
  # tag: `{:put, _a, b}` gives `[nil, :b]`. An ignored or non-variable
  # position is nil.
  defp tuple_positions({tag, inner}) when is_atom(tag), do: [var_name(inner)]
  defp tuple_positions({:{}, _meta, [_tag | rest]}), do: Enum.map(rest, &var_name/1)
  defp tuple_positions(_), do: []

  defp var_name({name, meta, ctx}) when is_atom(name) and is_list(meta) and is_atom(ctx) do
    if String.starts_with?(Atom.to_string(name), "_"), do: nil, else: name
  end

  defp var_name(_), do: nil

  defp zip_positions(names, values) do
    names
    |> Enum.zip(values)
    |> Enum.reject(fn {name, _} -> is_nil(name) end)
    |> Map.new()
  end

  defp build_existentials(
         %Transition{
           message_pattern: pattern,
           message_types: types,
           message_arg_names: arg_names
         },
         config
       ) do
    case pattern do
      pat when is_tuple(pat) ->
        args = pat |> Tuple.to_list() |> tl()
        arg_names = arg_names || []

        {vars, bindings} =
          args
          |> Enum.zip(types)
          |> Enum.with_index()
          |> Enum.reduce({[], %{}}, fn {{arg, type}, idx}, {vars_acc, bindings_acc} ->
            # Prefer the declared argument name (from `count :: pos_integer()`) over
            # the pattern position. Guards reference the declared name, not :arg0.
            param_name =
              case Enum.at(arg_names, idx) do
                name when is_binary(name) -> String.to_atom(name)
                _ -> extract_param_name(arg, idx)
              end

            tla_var = "msg_#{param_name}"
            domain = ModelConfig.resolve_domain(config, param_name, type)
            domain_tla = ModelConfig.domain_to_tla(domain)
            {[{tla_var, domain_tla} | vars_acc], Map.put(bindings_acc, param_name, tla_var)}
          end)

        {Enum.reverse(vars), bindings}

      _ ->
        {[], %{}}
    end
  end

  defp extract_param_name(:_, idx), do: :"arg#{idx}"
  defp extract_param_name(name, _idx) when is_atom(name), do: name
  defp extract_param_name(_, idx), do: :"arg#{idx}"

  defp build_track_primed(_ir, %Transition{update: nil}, _branch, _bindings, _track_names, _s),
    do: {:ok, %{}}

  defp build_track_primed(
         ir,
         %Transition{update: %{ast: ast} = update} = transition,
         branch,
         bindings,
         track_names,
         sessions
       )
       when not is_nil(ast) do
    span = Map.get(update, :span) || transition.block_span || transition.span

    # Extract map update key-value pairs from the AST, resolving case and
    # if expressions against the branch's reply type. An update body the
    # extractor cannot understand must be an error: rendering the track as
    # UNCHANGED would make every invariant over it hold vacuously in TLC
    # while failing at runtime.
    case extract_update(ast, branch) do
      :identity ->
        {:ok, %{}}

      {:unsupported, offending} ->
        {:error, [unsupported_update_report(ir, offending, span)]}

      {:ok, update_pairs} ->
        compile_update_pairs(ir, update_pairs, bindings, track_names, span, sessions)
    end
  end

  defp build_track_primed(_, _, _, _, _, _), do: {:ok, %{}}

  @tla_binops ~w(= < > =< >= /= \\/ /\\ => ~>)

  # A primed assignment `x' = value` conflicts with the assignment's own `=`
  # when the value is itself a top-level comparison or boolean expression
  # (e.g. a boolean track set from `tracks.mode == :fast`). Wrap those; leave
  # simple values (a var, a literal, an already-parenthesized arithmetic
  # expression) untouched.
  defp parenthesize_value(value) do
    if top_level_binop?(value), do: "(#{value})", else: value
  end

  defp top_level_binop?(value) do
    value
    |> String.split(" ")
    |> Enum.reduce_while(0, fn token, depth ->
      if depth == 0 and token in @tla_binops do
        {:halt, :found}
      else
        {:cont, depth + paren_delta(token)}
      end
    end)
    |> Kernel.==(:found)
  end

  defp paren_delta(token) do
    opens = token |> String.graphemes() |> Enum.count(&(&1 == "("))
    closes = token |> String.graphemes() |> Enum.count(&(&1 == ")"))
    opens - closes
  end

  defp compile_update_pairs(ir, update_pairs, bindings, track_names, span, sessions) do
    results =
      Enum.map(update_pairs, fn {key, val_ast} ->
        key_str = Atom.to_string(key)

        if MapSet.member?(track_names, key_str) do
          case Expr.compile(val_ast, bindings,
                 ir: ir,
                 code: "E042",
                 context: "update",
                 track_names: track_names,
                 span: span,
                 render_field: Sessions.render_field(sessions)
               ) do
            {:ok, tla_val} ->
              {:ok, {key_str, Sessions.assign(sessions, key_str, parenthesize_value(tla_val))}}

            {:error, reports} ->
              {:error, reports}
          end
        else
          {:error, [Expr.unknown_track_report(key_str, track_names, ir, span, "update")]}
        end
      end)

    errors =
      Enum.flat_map(results, fn
        {:error, reports} -> reports
        {:ok, _} -> []
      end)

    case errors do
      [] -> {:ok, Map.new(for {:ok, pair} <- results, do: pair)}
      errors -> {:error, errors}
    end
  end

  defp unsupported_update_report(ir, offending, span) do
    Report.error(
      "cannot compile update to TLA+: #{Macro.to_string(offending)}\n" <>
        "the affected tracks would be modeled as unchanged, making every " <>
        "invariant over them hold vacuously"
    )
    |> Report.with_code("E042")
    |> Report.with_help(
      "write updates as %{tracks | key: value}, optionally dispatched on the " <>
        "reply via case/if; or compile with tla: :warn to skip verification"
    )
    |> maybe_add_source(ir.source_file)
    |> maybe_add_span_label(span, "in this update")
  end

  # Extracts update pairs from the update fn, resolving reply dispatch
  # against the branch's reply type.
  #
  # Returns `{:ok, pairs}`, `:identity` (the update returns tracks
  # unchanged — a legitimate no-op for this branch), or
  # `{:unsupported, ast}` when the body has a shape the extractor cannot
  # faithfully translate.
  defp extract_update({:fn, _, [{:->, _, [args, body]}]}, branch) do
    # Call updates are `fn msg, reply, tracks`; event updates are
    # `fn msg, tracks` (no reply to dispatch on).
    ctx =
      case length(args) do
        2 -> %{reply_var: nil, tracks_var: fn_arg_var(args, 1)}
        _ -> %{reply_var: fn_arg_var(args, 1), tracks_var: fn_arg_var(args, length(args) - 1)}
      end

    extract_update_body(body, branch, ctx)
  end

  defp extract_update(ast, _branch), do: {:unsupported, ast}

  defp extract_update_body(ast, branch, ctx) do
    case ast do
      # %{var | key: val, ...}
      {:%{}, _, [{:|, _, [_base | updates]}]} ->
        {:ok, pairs_from_keyword(List.flatten(updates))}

      # Bare tracks variable — identity update.
      {var, _, var_ctx} when is_atom(var) and is_atom(var_ctx) ->
        if var == ctx.tracks_var do
          :identity
        else
          {:unsupported, ast}
        end

      # case reply do :ok -> body1; _ -> body2 end
      # Resolvable only when the scrutinee is the reply variable, so the
      # arm can be selected by the branch's reply type. A case on the
      # message, a track, or a nested binding (`case n do ...`) cannot be
      # statically resolved — translating it anyway would silently drop
      # the arms that do not appear to match, so it is an error (E042).
      # Events have no reply (branch is nil) and are never resolvable.
      {:case, _, [scrutinee, [do: clauses]]} ->
        if branch != nil and reply_var?(scrutinee, ctx) do
          resolve_case_for_branch(clauses, branch, ctx)
        else
          {:unsupported, ast}
        end

      # if reply == :ok, do: ..., else: ...
      # Resolvable when the condition compares the reply to a literal.
      {:if, _, [cond_ast, clauses]} ->
        extract_if_update(ast, cond_ast, clauses, branch, ctx)

      # Block — check last expression.
      {:__block__, _, exprs} ->
        extract_update_body(List.last(exprs), branch, ctx)

      _ ->
        {:unsupported, ast}
    end
  end

  defp extract_if_update(ast, cond_ast, clauses, branch, ctx) do
    case resolve_if_condition(cond_ast, branch, ctx) do
      {:resolved, true} ->
        extract_update_body(Keyword.get(clauses, :do), branch, ctx)

      {:resolved, false} ->
        case Keyword.get(clauses, :else) do
          nil -> :identity
          else_body -> extract_update_body(else_body, branch, ctx)
        end

      :unknown ->
        {:unsupported, ast}
    end
  end

  defp fn_arg_var(args, idx) do
    case Enum.at(args, idx) do
      {name, _, ctx} when is_atom(name) and is_atom(ctx) -> name
      _ -> nil
    end
  end

  # Statically resolves an if condition against the branch's reply type.
  # Only literal comparison against the reply variable is resolvable; a
  # condition on tracks depends on runtime state the extractor cannot see.
  defp resolve_if_condition(_cond, nil, _ctx), do: :unknown

  defp resolve_if_condition({:==, _, [left, right]}, branch, ctx) do
    case {reply_var?(left, ctx), reply_var?(right, ctx)} do
      {true, false} -> literal_equals_reply_type(right, branch.reply_type)
      {false, true} -> literal_equals_reply_type(left, branch.reply_type)
      _ -> :unknown
    end
  end

  defp resolve_if_condition(_, _branch, _ctx), do: :unknown

  defp reply_var?({name, _, var_ctx}, %{reply_var: name}) when is_atom(var_ctx), do: true
  defp reply_var?(_, _), do: false

  defp literal_equals_reply_type(literal, {:literal, value})
       when is_atom(literal) or is_integer(literal) do
    {:resolved, literal == value}
  end

  defp literal_equals_reply_type(literal, {:tagged, _tag, _inner})
       when is_atom(literal) or is_integer(literal) do
    # A tagged-tuple reply can never equal a bare literal.
    {:resolved, false}
  end

  defp literal_equals_reply_type(_, _), do: :unknown

  # Finds the matching case clause for the branch's reply type
  # and extracts map update pairs from that arm's body.
  defp resolve_case_for_branch(clauses, branch, ctx) do
    reply_type = branch.reply_type

    # A `when` guard depends on the runtime reply value, which the
    # extractor cannot evaluate against a static type. Selecting an arm
    # by type alone would ignore the guard and pick the wrong body, so a
    # case with any guarded arm is untranslatable (E042) rather than
    # silently mistranslated.
    if Enum.any?(clauses, &guarded_clause?/1) do
      {:unsupported, {:case, [], clauses}}
    else
      resolve_unguarded_case(clauses, reply_type, branch, ctx)
    end
  end

  defp guarded_clause?({:->, _, [[{:when, _, _}], _body]}), do: true
  defp guarded_clause?(_), do: false

  # Takes the first arm, in order, that matches every reply of the
  # branch, as Elixir does. An arm that matches only some replies of the
  # branch (a literal against a general type) makes the case
  # untranslatable.
  defp resolve_unguarded_case(clauses, reply_type, branch, ctx) do
    Enum.reduce_while(clauses, {:unsupported, {:case, [], clauses}}, fn
      {:->, _, [[pattern], body]}, acc ->
        match =
          if wildcard_pattern?(pattern),
            do: true,
            else: case_pattern_matches_reply_type?(pattern, reply_type)

        case match do
          true -> {:halt, extract_update_body(body, branch, ctx)}
          false -> {:cont, acc}
          :partial -> {:halt, {:unsupported, {:case, [], clauses}}}
        end
    end)
  end

  # Checks if a case pattern matches the branch's reply type. A tagged
  # pattern must have the same tag and size. A literal in the pattern must
  # equal a literal type at that position; against a general type it
  # matches only some replies, so the arm cannot be selected statically.
  defp case_pattern_matches_reply_type?(pattern, {:literal, value}) do
    pattern == value
  end

  defp case_pattern_matches_reply_type?(pattern, {:tagged, tag, inner}) do
    types = List.wrap(inner)

    case pattern_parts(pattern) do
      {^tag, parts} when length(parts) == length(types) ->
        parts
        |> Enum.zip(types)
        |> Enum.reduce_while(true, fn {part, type}, acc ->
          case part_matches?(part, type) do
            true -> {:cont, acc}
            false -> {:halt, false}
            :partial -> {:cont, :partial}
          end
        end)

      _ ->
        false
    end
  end

  defp case_pattern_matches_reply_type?(_, _), do: false

  defp pattern_parts({tag, inner}) when is_atom(tag), do: {tag, [inner]}
  defp pattern_parts({:{}, _meta, [tag | rest]}) when is_atom(tag), do: {tag, rest}
  defp pattern_parts(_), do: nil

  defp part_matches?({name, meta, ctx}, _type)
       when is_atom(name) and is_list(meta) and is_atom(ctx),
       do: true

  defp part_matches?(literal, {:literal, value}) when is_atom(literal) or is_integer(literal),
    do: literal == value

  defp part_matches?(literal, _type) when is_atom(literal) or is_integer(literal), do: :partial
  defp part_matches?(_, _type), do: :partial

  # Checks if a pattern is a wildcard (matches anything).
  defp wildcard_pattern?({:_, _, _}), do: true
  defp wildcard_pattern?({name, _, ctx}) when is_atom(name) and is_atom(ctx), do: true
  defp wildcard_pattern?(_), do: false

  defp pairs_from_keyword(pairs) do
    Enum.flat_map(pairs, fn
      {key, val} when is_atom(key) -> [{key, val}]
      _ -> []
    end)
  end

  # -- Reply values --
  #
  # A call branch quantifies over the reply values that matter: each
  # reply position that the update, the branch's `where:`, or an earlier
  # branch (for first-match selection) reads. Each position has one
  # existential, so every reader of a position sees the same value.

  @typep plan :: %{
           existentials: [{String.t(), String.t()}],
           update: map(),
           constraint: map(),
           earlier: [{Accord.IR.Branch.t(), map(), [String.t()]}]
         }

  @spec reply_plan(Transition.t(), Accord.IR.Branch.t(), [Accord.IR.Branch.t()], ModelConfig.t()) ::
          plan()
  defp reply_plan(transition, branch, earlier, config) do
    types = reply_inner_types(branch.reply_type)
    update_names = update_reply_positions(transition, branch)
    constraint_names = constraint_positions(branch.constraint)

    overlapping = Enum.filter(earlier, &overlaps?(&1.reply_type, branch.reply_type))

    earlier_names =
      Enum.map(overlapping, fn other ->
        {other, constraint_positions(other.constraint), type_tests(other.reply_type, types)}
      end)

    tested_positions =
      for {_other, _names, tests} <- earlier_names, {idx, _test} <- tests, uniq: true, do: idx

    sources = [update_names, constraint_names | Enum.map(earlier_names, &elem(&1, 1))]

    needed =
      for idx <- 0..(length(types) - 1)//1,
          idx in tested_positions or Enum.any?(sources, &(Enum.at(&1, idx) != nil)),
          do: idx

    {vars, existentials, _used} =
      Enum.reduce(needed, {%{}, [], MapSet.new()}, fn idx, {vars, exs, used} ->
        name = Enum.find_value(sources, &Enum.at(&1, idx))
        type = Enum.at(types, idx)
        base = "reply_#{name || idx}"

        {var, domain} =
          case type do
            {:list, _} ->
              {base <> "_len", "0..#{config.max_list_length || 3}"}

            _ ->
              {base,
               config
               |> ModelConfig.resolve_domain(name || :_, type)
               |> ModelConfig.domain_to_tla()}
          end

        var = if MapSet.member?(used, var), do: "#{var}_#{idx}", else: var
        binding = if match?({:list, _}, type), do: {:list_length, var}, else: var
        {Map.put(vars, idx, binding), [{var, domain} | exs], MapSet.put(used, var)}
      end)

    bind = fn names ->
      names
      |> Enum.with_index()
      |> Enum.flat_map(fn
        {nil, _idx} -> []
        {name, idx} -> [{name, Map.fetch!(vars, idx)}]
      end)
      |> Map.new()
    end

    %{
      existentials: Enum.reverse(existentials),
      update: bind.(update_names),
      constraint: bind.(constraint_names),
      earlier:
        Enum.map(earlier_names, fn {other, names, tests} ->
          {other, bind.(names),
           Enum.map(tests, fn {idx, test} -> test.(plain_var(vars[idx])) end)}
        end)
    }
  end

  defp plain_var({:list_length, var}), do: var
  defp plain_var(var), do: var

  defp reply_inner_types({:tagged, _tag, inner}), do: List.wrap(inner)
  defp reply_inner_types(_), do: []

  # The names in the update's reply pattern, by position: from a
  # destructured head (`fn msg, {:ok, a}, tracks`), or from the arm of
  # `case reply do` that matches this branch.
  defp update_reply_positions(%Transition{update: %{ast: ast}}, branch) when not is_nil(ast) do
    case ast do
      {:fn, _, [{:->, _, [[_msg, reply_pat, _tracks], body]}]} ->
        case var_name_any(reply_pat) do
          nil -> tuple_positions(reply_pat)
          reply_var -> case_arm_positions(body, reply_var, branch)
        end

      _ ->
        []
    end
  end

  defp update_reply_positions(_, _), do: []

  # The names of the `case reply do` arm that matches the branch.
  defp case_arm_positions(body, reply_var, branch) do
    case find_case_on_var(body, reply_var) do
      {:ok, clauses} ->
        Enum.find_value(clauses, [], fn {:->, _, [[pattern], _]} ->
          if case_pattern_matches_reply_type?(pattern, branch.reply_type) == true,
            do: tuple_positions(pattern)
        end)

      :not_found ->
        []
    end
  end

  defp var_name_any({name, meta, ctx}) when is_atom(name) and is_list(meta) and is_atom(ctx),
    do: name

  defp var_name_any(_), do: nil

  defp constraint_positions(%{ast: {:fn, _, [{:->, _, [[reply_pat, _tracks], _body]}]}}),
    do: tuple_positions(reply_pat)

  defp constraint_positions(_), do: []

  # Whether an earlier branch can accept a reply of this branch. Two
  # literals overlap when they are equal. Two tagged tuples overlap when
  # they have the same tag and size.
  defp overlaps?({:literal, a}, {:literal, b}), do: a == b

  defp overlaps?({:tagged, tag, a}, {:tagged, tag, b}),
    do: length(List.wrap(a)) == length(List.wrap(b))

  defp overlaps?({:literal, _}, {:tagged, _, _}), do: false
  defp overlaps?({:tagged, _, _}, {:literal, _}), do: false
  defp overlaps?(earlier, type), do: Accord.IR.Type.subtype?(type, earlier)

  # The positions where an earlier branch's type is narrower than this
  # branch's type, with a TLA+ test that the value has the earlier type.
  defp type_tests({:tagged, _tag, inner}, types) do
    inner
    |> List.wrap()
    |> Enum.with_index()
    |> Enum.flat_map(fn {type, idx} ->
      case type_test(type, Enum.at(types, idx)) do
        nil -> []
        test -> [{idx, test}]
      end
    end)
  end

  defp type_tests(_type, _types), do: []

  defp type_test(same, same), do: nil
  defp type_test(:term, _), do: nil
  defp type_test({:list, _}, _), do: nil
  defp type_test({:literal, value}, _), do: &"#{&1} = #{literal_to_tla(value)}"
  defp type_test(:integer, _), do: &"#{&1} \\in Int"
  defp type_test(:pos_integer, _), do: &"(#{&1} \\in Int /\\ #{&1} > 0)"
  defp type_test(:non_neg_integer, _), do: &"#{&1} \\in Nat"
  defp type_test(:boolean, _), do: &"#{&1} \\in BOOLEAN"
  # Atoms, strings, maps, and structs are model values or strings in the
  # model. Only an integer value is outside these types.
  defp type_test(_, _), do: &"~(#{&1} \\in Int)"

  defp literal_to_tla(true), do: "TRUE"
  defp literal_to_tla(false), do: "FALSE"
  defp literal_to_tla(nil), do: "NULL"
  defp literal_to_tla(n) when is_integer(n), do: Integer.to_string(n)
  defp literal_to_tla(a) when is_atom(a), do: ~s("#{a}")
  defp literal_to_tla(s) when is_binary(s), do: ~s("#{s}")

  defp compile_branch_constraint(_ir, %{constraint: nil}, _bindings, _track_names, _sessions),
    do: {:ok, []}

  defp compile_branch_constraint(
         ir,
         %{constraint: %{ast: ast}} = branch,
         bindings,
         track_names,
         sessions
       ) do
    case ast do
      {:fn, _, [{:->, _, [[_reply_pat, _tracks_var], body]}]} ->
        case Expr.compile(body, bindings,
               ir: ir,
               code: "E045",
               context: "where: constraint",
               track_names: track_names,
               span: branch.span,
               render_field: Sessions.render_field(sessions)
             ) do
          {:ok, tla} -> {:ok, [tla]}
          {:error, reports} -> {:error, reports}
        end

      _ ->
        {:ok, []}
    end
  end

  # This branch runs only when no earlier branch accepts the reply: for
  # each earlier branch that can accept it, the reply fails that branch's
  # type or that branch's `where:`.
  defp compile_first_match(ir, _transition, _branch, plan, track_names, sessions) do
    plan.earlier
    |> Enum.map(fn {other, bindings, tests} ->
      with {:ok, where} <- compile_branch_constraint(ir, other, bindings, track_names, sessions) do
        case tests ++ where do
          [] -> {:ok, "FALSE"}
          conds -> {:ok, "~(" <> Enum.map_join(conds, " /\\ ", &"(#{&1})") <> ")"}
        end
      end
    end)
    |> collect_preconditions()
  end

  # Walks the AST to find a case expression whose subject is the given variable.
  defp find_case_on_var({:case, _, [{var_name, _, ctx}, [do: clauses]]}, var_name)
       when is_atom(ctx) do
    {:ok, clauses}
  end

  defp find_case_on_var({:__block__, _, exprs}, var_name) do
    Enum.find_value(exprs, :not_found, fn expr ->
      case find_case_on_var(expr, var_name) do
        {:ok, _} = found -> found
        :not_found -> nil
      end
    end) || :not_found
  end

  defp find_case_on_var(_, _), do: :not_found

  # Builds primed assignments for correspondence counter variables.
  defp build_correspondence_primed(tag, source, target, %StateSpace{
         correspondences: correspondences,
         sessions: sessions
       }) do
    Enum.reduce(correspondences, %{}, fn corr, acc ->
      open_tag = Atom.to_string(corr.open)
      close_tags = Enum.map(corr.close, &Atom.to_string/1)
      counter_read = Sessions.read(sessions, corr.counter_var)

      cond do
        tag == open_tag and source != target ->
          Map.put(
            acc,
            corr.counter_var,
            Sessions.assign(sessions, corr.counter_var, "(#{counter_read} + 1)")
          )

        tag in close_tags and source != target ->
          Map.put(
            acc,
            corr.counter_var,
            Sessions.assign(sessions, corr.counter_var, "(#{counter_read} - 1)")
          )

        true ->
          acc
      end
    end)
  end

  defp build_action_name(tag, source, target, nil) do
    "#{camelize(tag)}From#{camelize(source)}To#{camelize(target)}"
  end

  defp build_action_name(tag, source, target, index) do
    "#{camelize(tag)}From#{camelize(source)}To#{camelize(target)}#{index}"
  end

  defp resolve_next_state(:__same__, current), do: current
  defp resolve_next_state(state, _current), do: state

  defp message_tag(pattern) when is_atom(pattern), do: Atom.to_string(pattern)
  defp message_tag(pattern) when is_tuple(pattern), do: pattern |> elem(0) |> Atom.to_string()

  defp camelize(s) when is_binary(s) do
    s
    |> String.split("_")
    |> Enum.map_join("", &String.capitalize/1)
  end
end
