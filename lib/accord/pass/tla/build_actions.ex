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
  alias Accord.TLA.{Action, ModelConfig, StateSpace}
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
      |> Enum.flat_map(fn {state_name, state} ->
        # Include anystate transitions for non-terminal states.
        transitions =
          if state.terminal do
            state.transitions
          else
            state.transitions ++ ir.anystate
          end

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
          Enum.map_reduce(branches, %{}, fn branch, seen ->
            target_state = resolve_next_state(branch.next_state, state_name)
            idx = Map.get(seen, target_state, 0)
            seen = Map.put(seen, target_state, idx + 1)

            suffix =
              if Map.fetch!(target_counts, target_state) > 1, do: idx, else: nil

            action =
              build_call_action(
                ir,
                state_name,
                transition,
                branch,
                tag,
                source,
                state_space,
                config,
                all_var_names,
                track_names,
                suffix
              )

            {action, seen}
          end)

        actions
    end
  end

  defp build_call_action(
         ir,
         state_name,
         transition,
         branch,
         tag,
         source,
         state_space,
         config,
         all_var_names,
         track_names,
         suffix
       ) do
    target_state = resolve_next_state(branch.next_state, state_name)
    target = Atom.to_string(target_state)

    action_name = build_action_name(tag, source, target, suffix)

    # Build existential variables for message parameters.
    {existential_vars, param_bindings} =
      build_existentials(transition, config)

    # Preconditions.
    preconditions = [~s(state = "#{source}")]

    # Guard condition.
    guard_result = compile_guard(ir, transition, param_bindings, track_names)

    # Build bindings for update fn params and additional reply existentials.
    {reply_existentials, update_bindings} =
      build_update_bindings(transition, branch, existential_vars, config)

    # Constraint precondition from where clause.
    constraint_result =
      build_constraint(ir, branch, reply_existentials, update_bindings, config, track_names)

    # Track updates from update AST.
    track_primed_result =
      build_track_primed(ir, transition, branch, update_bindings, track_names)

    # Collect errors from every failing site, not just the first.
    errors =
      [guard_result, constraint_result, track_primed_result]
      |> Enum.flat_map(fn
        {:error, reports} -> reports
        {:ok, _} -> []
      end)

    if errors != [] do
      {:error, errors}
    else
      {:ok, guard_precondition} = guard_result
      {:ok, {constraint_existentials, constraint_precondition}} = constraint_result
      {:ok, track_primed} = track_primed_result

      existential_vars = existential_vars ++ reply_existentials ++ constraint_existentials

      # Primed assignments.
      primed = %{"state" => ~s("#{target}")}

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
         preconditions: preconditions ++ guard_precondition ++ constraint_precondition,
         existential_vars: existential_vars,
         primed: all_primed,
         unchanged: unchanged,
         comment: "#{tag} from #{source} to #{target}"
       }}
    end
  end

  defp compile_guard(ir, transition, param_bindings, track_names) do
    case transition.guard do
      %{ast: ast} = guard when not is_nil(ast) ->
        span = Map.get(guard, :span) || transition.span

        case Expr.compile(ast, param_bindings,
               ir: ir,
               code: "E041",
               context: "guard",
               track_names: track_names,
               span: span
             ) do
          {:ok, tla} -> {:ok, [tla]}
          {:error, reports} -> {:error, reports}
        end

      _ ->
        {:ok, []}
    end
  end

  defp build_cast_action(_ir, _state_name, _transition, tag, source, _state_space, all_var_names) do
    # Casts don't change state (stay in same state). With no primed
    # variables the action is a pure stuttering step — semantically a
    # no-op for TLC, kept for spec readability.
    target = source
    action_name = "Cast#{camelize(tag)}From#{camelize(source)}"

    unchanged = all_var_names |> MapSet.to_list() |> Enum.sort()

    %Action{
      name: action_name,
      source_state: source,
      target_state: target,
      message_tag: tag,
      preconditions: [~s(state = "#{source}")],
      existential_vars: [],
      primed: %{},
      unchanged: unchanged,
      comment: "cast #{tag} in #{source}"
    }
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

  defp build_track_primed(_ir, %Transition{update: nil}, _branch, _bindings, _track_names),
    do: {:ok, %{}}

  defp build_track_primed(
         ir,
         %Transition{update: %{ast: ast} = update} = transition,
         branch,
         bindings,
         track_names
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
        compile_update_pairs(ir, update_pairs, bindings, track_names, span)
    end
  end

  defp build_track_primed(_, _, _, _, _), do: {:ok, %{}}

  defp compile_update_pairs(ir, update_pairs, bindings, track_names, span) do
    results =
      Enum.map(update_pairs, fn {key, val_ast} ->
        key_str = Atom.to_string(key)

        if MapSet.member?(track_names, key_str) do
          case Expr.compile(val_ast, bindings,
                 ir: ir,
                 code: "E042",
                 context: "update",
                 track_names: track_names,
                 span: span
               ) do
            {:ok, tla_val} -> {:ok, {key_str, tla_val}}
            {:error, reports} -> {:error, reports}
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
    ctx = %{
      reply_var: fn_arg_var(args, 1),
      tracks_var: fn_arg_var(args, length(args) - 1)
    }

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
      # Resolve against the branch's reply type.
      {:case, _, [_expr, [do: clauses]]} ->
        resolve_case_for_branch(clauses, branch, ctx)

      # if reply == :ok, do: ..., else: ...
      # Resolvable when the condition compares the reply to a literal.
      {:if, _, [cond_ast, clauses]} ->
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

      # Block — check last expression.
      {:__block__, _, exprs} ->
        extract_update_body(List.last(exprs), branch, ctx)

      _ ->
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

    # Find the first matching clause.
    matching_clause =
      Enum.find(clauses, fn {:->, _, [[pattern], _body]} ->
        case_pattern_matches_reply_type?(pattern, reply_type)
      end)

    case matching_clause do
      {:->, _, [[_pattern], body]} ->
        extract_update_body(body, branch, ctx)

      nil ->
        # No match found — try wildcard clause.
        wildcard =
          Enum.find(clauses, fn {:->, _, [[pattern], _body]} ->
            wildcard_pattern?(pattern)
          end)

        case wildcard do
          {:->, _, [[_pattern], body]} ->
            extract_update_body(body, branch, ctx)

          nil ->
            {:unsupported, {:case, [], clauses}}
        end
    end
  end

  # Checks if a case pattern matches the branch's reply type.
  defp case_pattern_matches_reply_type?(pattern, {:literal, value}) do
    pattern == value
  end

  defp case_pattern_matches_reply_type?({tag, _}, {:tagged, tag, _inner}) do
    true
  end

  defp case_pattern_matches_reply_type?(_, _), do: false

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

  # Builds bindings from the update fn's param names to TLA+ identifiers.
  # Maps message params to existing existential vars and creates new
  # existential vars for reply params.
  defp build_update_bindings(%Transition{update: nil}, _branch, _existentials, _config) do
    {[], %{}}
  end

  defp build_update_bindings(%Transition{update: %{ast: ast}}, branch, existentials, config)
       when not is_nil(ast) do
    case ast do
      {:fn, _, [{:->, _, [[msg_pat, reply_pat, _tracks_var], body]}]} ->
        # Map update fn's message params to existing existential vars by position.
        msg_params = extract_pattern_params(msg_pat)
        msg_bindings = zip_to_existentials(msg_params, existentials)

        # Create reply existentials either from destructured pattern or from
        # case-arm patterns when the reply is a bare variable with case dispatch.
        {reply_existentials, reply_bindings} =
          if destructured_pattern?(reply_pat) do
            reply_params = extract_pattern_params(reply_pat)
            reply_types = extract_reply_inner_types(branch.reply_type)
            build_reply_existentials(reply_params, reply_types, config)
          else
            extract_case_reply_bindings(reply_pat, body, branch, config)
          end

        {reply_existentials, Map.merge(msg_bindings, reply_bindings)}

      _ ->
        {[], %{}}
    end
  end

  defp build_update_bindings(_, _, _, _), do: {[], %{}}

  # When the update fn binds the reply to a bare variable and dispatches via
  # a case expression, extract reply param bindings from the matching arm's
  # pattern. This handles patterns like:
  #
  #     fn _msg, reply, tracks ->
  #       case reply do
  #         {:ok, items} -> %{tracks | buffer_size: tracks.buffer_size - length(items)}
  #         {:done, items} -> %{tracks | buffer_size: tracks.buffer_size - length(items)}
  #       end
  #     end
  #
  defp extract_case_reply_bindings(reply_pat, body, branch, config) do
    reply_var_name = extract_var_name(reply_pat)

    case find_case_on_var(body, reply_var_name) do
      {:ok, clauses} ->
        matching_clause =
          Enum.find(clauses, fn {:->, _, [[pattern], _body]} ->
            case_pattern_matches_reply_type?(pattern, branch.reply_type)
          end)

        case matching_clause do
          {:->, _, [[pattern], _body]} ->
            reply_params = extract_pattern_params(pattern)
            reply_types = extract_reply_inner_types(branch.reply_type)
            build_reply_existentials(reply_params, reply_types, config)

          nil ->
            {[], %{}}
        end

      :not_found ->
        {[], %{}}
    end
  end

  defp extract_var_name({name, _meta, ctx}) when is_atom(name) and is_atom(ctx), do: name
  defp extract_var_name(_), do: nil

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

  # Compiles a branch constraint (where clause) into a TLA+ precondition.
  # Maps the constraint fn's reply params to existing reply existential vars,
  # or creates new ones if the branch has no update fn.
  defp build_constraint(
         _ir,
         %{constraint: nil},
         _reply_existentials,
         _update_bindings,
         _config,
         _track_names
       ),
       do: {:ok, {[], []}}

  defp build_constraint(
         ir,
         %{constraint: %{ast: ast}, reply_type: reply_type} = branch,
         reply_existentials,
         update_bindings,
         config,
         track_names
       ) do
    case ast do
      {:fn, _, [{:->, _, [[reply_pat, _tracks_var], body]}]} ->
        reply_params = extract_pattern_params(reply_pat)

        {extra_existentials, bindings} =
          if reply_existentials != [] do
            # Map constraint params to existing reply existentials by position,
            # then merge update_bindings to preserve list-length tags.
            base = zip_to_existentials(reply_params, reply_existentials)
            {[], enrich_bindings(base, update_bindings)}
          else
            # No update fn created reply existentials — create from constraint.
            reply_types = extract_reply_inner_types(reply_type)
            build_reply_existentials(reply_params, reply_types, config)
          end

        case Expr.compile(body, bindings,
               ir: ir,
               code: "E045",
               context: "where: constraint",
               track_names: track_names,
               span: branch.span
             ) do
          {:ok, tla} -> {:ok, {extra_existentials, [tla]}}
          {:error, reports} -> {:error, reports}
        end

      _ ->
        {:ok, {[], []}}
    end
  end

  # Enriches base bindings with tagged forms (e.g. {:list_length, var}) from
  # the update bindings. When a constraint param maps to the same TLA+ var as
  # an update param, the richer binding form is used so that length() calls
  # compile correctly.
  defp enrich_bindings(base, update_bindings) do
    # Build reverse lookup: tla_var string → full binding form.
    reverse =
      Map.new(update_bindings, fn
        {_name, {:list_length, tla_var} = binding} -> {tla_var, binding}
        {_name, tla_var} -> {tla_var, tla_var}
      end)

    Map.new(base, fn {name, tla_var} ->
      {name, Map.get(reverse, tla_var, tla_var)}
    end)
  end

  # Returns true if the pattern destructures into components (tagged tuple),
  # false if it's a bare variable binding.
  defp destructured_pattern?({name, meta, ctx})
       when is_atom(name) and is_list(meta) and is_atom(ctx),
       do: false

  defp destructured_pattern?(_), do: true

  # Extracts variable names from pattern AST, skipping tags and underscored vars.
  defp extract_pattern_params({name, meta, ctx})
       when is_atom(name) and is_list(meta) and is_atom(ctx) do
    name_str = Atom.to_string(name)
    if String.starts_with?(name_str, "_"), do: [], else: [name]
  end

  defp extract_pattern_params({tag, inner}) when is_atom(tag) do
    # 2-tuple pattern like {:ok, val} — skip tag, extract from inner.
    extract_pattern_params(inner)
  end

  defp extract_pattern_params({:{}, _meta, [_tag | rest]}) do
    # 3+ tuple pattern — skip tag, extract from rest.
    Enum.flat_map(rest, &extract_pattern_params/1)
  end

  defp extract_pattern_params(_), do: []

  # Maps param names to existing existential TLA+ var names by position.
  defp zip_to_existentials(param_names, existential_vars) do
    param_names
    |> Enum.zip(existential_vars)
    |> Map.new(fn {name, {tla_var, _domain}} -> {name, tla_var} end)
  end

  # Extracts the inner type atoms from a reply type spec.
  defp extract_reply_inner_types({:tagged, _tag, inner_type}), do: [inner_type]
  defp extract_reply_inner_types(_), do: []

  # Creates existential vars for reply parameters.
  # When a reply parameter has list type, abstracts it to its length
  # (a non_neg_integer) since TLC can't enumerate variable-length sequences.
  # The binding marks the variable as a list-length abstraction so that
  # `length(name)` in guards/updates compiles to just the variable.
  defp build_reply_existentials(params, types, config) do
    {vars_rev, bindings} =
      params
      |> Enum.zip(types)
      |> Enum.reduce({[], %{}}, fn {name, type}, {vars_acc, bindings_acc} ->
        case type do
          {:list, _elem_type} ->
            # Abstract list to its length.
            tla_var = "reply_#{name}_len"
            max_len = config.max_list_length || 3
            domain_tla = "0..#{max_len}"

            {[{tla_var, domain_tla} | vars_acc],
             Map.put(bindings_acc, name, {:list_length, tla_var})}

          _ ->
            tla_var = "reply_#{name}"
            domain = ModelConfig.resolve_domain(config, name, type)
            domain_tla = ModelConfig.domain_to_tla(domain)
            {[{tla_var, domain_tla} | vars_acc], Map.put(bindings_acc, name, tla_var)}
        end
      end)

    {Enum.reverse(vars_rev), bindings}
  end

  # Builds primed assignments for correspondence counter variables.
  defp build_correspondence_primed(tag, source, target, %StateSpace{
         correspondences: correspondences
       }) do
    Enum.reduce(correspondences, %{}, fn corr, acc ->
      open_tag = Atom.to_string(corr.open)
      close_tags = Enum.map(corr.close, &Atom.to_string/1)

      cond do
        tag == open_tag and source != target ->
          Map.put(acc, corr.counter_var, "(#{corr.counter_var} + 1)")

        tag in close_tags and source != target ->
          Map.put(acc, corr.counter_var, "(#{corr.counter_var} - 1)")

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
    |> Enum.map(&String.capitalize/1)
    |> Enum.join()
  end
end
