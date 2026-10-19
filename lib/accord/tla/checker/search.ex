defmodule Accord.TLA.Checker.Search do
  @moduledoc """
  The breadth-first search of the checker, with the rules of TLC.

  - The initial states come from the initial predicate. Each one must
    satisfy the invariants and the state predicates of the properties.
  - For each state, the successors come from the next-state action. A
    state with no successor is a deadlock (unless deadlock checking is
    off).
  - Each step must satisfy the action constraints (or it is not taken) and
    the action properties (or it is a violation).
  - Each new state must satisfy the invariants. A state that does not
    satisfy the state constraints is not explored and not counted.
  - With `SYMMETRY`, two states that differ by a permutation count as one
    state. With `VIEW`, two states with the same view count as one state.
  - The search stops at the first violation. Because it is breadth-first,
    the trace has the minimum length.
  - At the end, the liveness properties are checked on the state graph
    (see `Accord.TLA.Checker.Liveness`).
  """

  alias Accord.TLA.Checker.{Constant, Context, Eval, Liveness, Spec, Temporal, Value}

  defmodule Stop do
    @moduledoc false
    defexception [:result]
    @impl true
    def message(_), do: "search stopped"
  end

  @doc """
  Runs the model of a loaded context.

  Options: `:deadlock` (default: the config), `:max_states` (default:
  no limit).
  """
  def run(%Context{} = ctx, opts \\ []) do
    config = ctx.config
    Eval.reset_cache()
    # The memos of an earlier run (in the same process) are of no use.
    Enum.each([:tla_constants, :tla_constant_defs, :tla_levels, :tla_tlccache], &Process.delete/1)
    Process.put(:tla_registers, %{})
    Process.put(:tla_properties, Keyword.get(opts, :properties, %{}))
    Process.put(:tla_warn, Keyword.get(opts, :warn, true))
    Process.put(:tla_deadlock, Keyword.get(opts, :deadlock, config.check_deadlock))

    Process.put(
      :tla_typed_model_values,
      ctx.constants |> Map.values() |> Enum.any?(&typed_model_values?/1)
    )

    base = %{
      ctx: ctx,
      deadlock: Keyword.get(opts, :deadlock, config.check_deadlock),
      max_states: Keyword.get(opts, :max_states, :infinity),
      generated: 0,
      warnings: [],
      graph: Keyword.get(opts, :graph, false)
    }

    try do
      check_replacements(ctx, base)
      check_assumptions(ctx)
      # An error in the analysis of the config is a config error in TLC.
      spec = setup(ctx, base, fn -> Spec.analyze(ctx, config) end)
      trivial_check(ctx, base, spec)

      # A model of constants (no variables): TLC only checks the
      # assumptions.
      if spec.init == nil or tuple_size(ctx.variables) == 0 do
        %{result(ctx) | status: :ok}
      else
        check_invariant_levels(ctx, base, config)
        model = setup(ctx, base, fn -> model(ctx, spec, config) end)
        constant_invariants(model, base)
        check_dnf_size(model, base)

        # Temporal properties whose negations are all FALSE: TLC has nothing
        # to check, an error.
        if model.live != [] and Enum.all?(model.live, fn {_, f, _} -> f == false end),
          do:
            raise(Stop,
              result:
                error_result(
                  ctx,
                  "Temporal formula is a tautology (its negation is unsatisfiable).",
                  [],
                  base,
                  nil,
                  :liveness_eval
                )
            )

        extra =
          for {text, e} <- Keyword.get(opts, :invariant_exprs, []),
              do: {text, {e, ctx.root, %{}, %{}}}

        search(base, %{model | invariants: model.invariants ++ extra})
      end
    rescue
      e in Stop ->
        e.result

      e in [Value.Error, Context.Error, Accord.TLA.Checker.Parser.Error] ->
        error_result(ctx, Exception.message(e), [], base)
    end
  end

  # -- Setup --

  # A conjunct of the initial predicate that is a constant FALSE makes the
  # specification trivial: TLC reports a config error.
  defp trivial_check(_ctx, _base, %{init: nil}), do: :ok

  # Only for a SPECIFICATION, and only for a part that is a name (or
  # FALSE), as in TLC.
  defp trivial_check(%{config: %{specification: nil}}, _base, _spec), do: :ok

  defp trivial_check(ctx, base, spec) do
    spec.init
    |> Enum.filter(&match?({{:name, _, _}, _, _, _}, &1))
    |> Enum.each(fn {e, scope, bound, frames} ->
      env = %{Eval.new(ctx) | scope: scope, bound: bound, frames: frames, state: nil, level: 0}

      constant_false =
        try do
          Eval.bool(e, env) == false
        rescue
          Value.Error -> false
        end

      if constant_false,
        do:
          raise(Stop,
            result:
              error_result(
                ctx,
                "the specification is trivial: a conjunct of it is a constant FALSE",
                [],
                base,
                nil,
                :config
              )
          )
    end)
  end

  # An invariant that is a constant FALSE: TLC reports it as a config
  # error, before the search.
  # TLC puts the fairness conditions (each one has two disjuncts) and the
  # negated property in one formula in disjunctive normal form, with a
  # count of at most 2^31 - 1 disjuncts.
  defp check_dnf_size(model, base) do
    Enum.each(model.live, fn {name, formula, _atoms} ->
      if Temporal.dnf_size(formula) * Integer.pow(2, length(model.fairness)) > 2_147_483_647 do
        raise Stop,
          result:
            error_result(
              model.ctx,
              "TLC cannot handle the temporal formula #{name} because it exceeds the maximum supported size in disjunctive normal form.",
              [],
              base
            )
      end
    end)
  end

  defp constant_invariants(model, base) do
    Enum.each(model.invariants, fn {name, {e, scope, bound, frames}} ->
      env = %{
        Eval.new(model.ctx)
        | scope: scope,
          bound: bound,
          frames: frames,
          state: nil,
          level: 0
      }

      constant_false =
        try do
          Eval.bool(e, env) == false
        rescue
          Value.Error -> false
        end

      if constant_false,
        do:
          raise(Stop,
            result:
              error_result(
                model.ctx,
                "The invariant of #{name} is equal to FALSE",
                [],
                base,
                nil,
                :config
              )
          )
    end)
  end

  # TLC checks the level of each invariant before the properties: an
  # invariant must be a state predicate.
  defp check_invariant_levels(ctx, base, config) do
    env = Eval.new(ctx)

    Enum.each(config.invariants, fn name ->
      e = {:name, name, nil}

      if Context.root_entry(ctx, name) != nil and (Spec.action?(e, env) or Spec.temporal?(e, env)) do
        raise Stop,
          result:
            error_result(
              ctx,
              "The invariant #{name} is not a state predicate (one with no primes or temporal operators).",
              [],
              base,
              nil,
              :safety_eval
            )
      end
    end)
  end

  defp setup(ctx, base, fun) do
    fun.()
  rescue
    e in Value.Error ->
      raise Stop, result: error_result(ctx, Exception.message(e), [], base, nil, :config)

    e in Spec.CannotHandle ->
      raise Stop, result: error_result(ctx, Exception.message(e), [], base, nil, :error)

    e in Spec.Tautology ->
      raise Stop, result: error_result(ctx, Exception.message(e), [], base, nil, :liveness_eval)
  end

  # A constant that the config replaces with a definition (`C <- Def`):
  # TLC evaluates it when it reads the spec, before the model checker
  # starts (so TLCGet has no value). A failure is a config error when the
  # definition is not a constant; else TLC ignores it.
  defp check_replacements(ctx, base) do
    Process.put(:tla_phase, :processing)

    ctx.constant_replacements
    |> Enum.filter(fn {_name, target} ->
      match?({:def, %{params: []}, _}, Context.root_entry(ctx, target))
    end)
    |> Enum.each(fn {name, target} ->
      try do
        Eval.eval({:name, name, nil}, %{Eval.new(ctx) | level: 0})
      rescue
        e in Value.Error ->
          unless constant_target?(ctx, target) do
            raise Stop,
              result:
                error_result(
                  ctx,
                  "The constant parameter #{name} is not assigned a constant expression by the configuration file: #{target} (#{Exception.message(e)})",
                  [],
                  base,
                  nil,
                  :config
                )
          end
      end
    end)
  after
    Process.delete(:tla_phase)
  end

  defp constant_target?(ctx, target) do
    case Context.root_entry(ctx, target) do
      {:def, d, sid} -> Constant.definition?(ctx, sid, d)
      _ -> true
    end
  end

  defp typed_model_values?({:mv, _} = v), do: Value.model_value_type(v) != nil
  defp typed_model_values?(%MapSet{} = s), do: Enum.any?(s, &typed_model_values?/1)
  defp typed_model_values?(_), do: false

  defp check_order(%MapSet{} = s) do
    Value.check_order!(MapSet.to_list(s))
    Enum.each(s, &check_order/1)
  end

  defp check_order({:fun, m}) do
    Value.check_order!(Map.keys(m))
    Enum.each(m, fn {k, v} -> check_order(k) && check_order(v) end)
  end

  defp check_order({:seq, t}), do: t |> Tuple.to_list() |> Enum.each(&check_order/1)
  defp check_order(_), do: true

  defp check_assumptions(ctx) do
    Enum.each(ctx.assumes, fn {e, scope, {line, col}} ->
      env = %{Eval.new(ctx) | scope: scope, level: 0}

      value =
        try do
          Eval.eval(e, env)
        rescue
          err in Value.Error ->
            raise Stop,
              result: %{
                result(ctx)
                | status: :violated,
                  kind: :assumption,
                  message: "Evaluating an assumption: " <> Exception.message(err)
              }
        end

      if value != true do
        raise Stop,
          result: %{
            result(ctx)
            | status: :violated,
              kind: :assumption,
              message:
                "Assumption line #{line}, column #{col} of module #{module_of(ctx, scope)} is false."
          }
      end
    end)
  end

  defp module_of(ctx, scope), do: Map.fetch!(ctx.scopes, scope).module

  defp model(ctx, spec, config) do
    env = Eval.new(ctx)
    root = fn name -> {{:name, name, nil}, ctx.root, %{}, %{}} end

    obligations =
      Enum.flat_map(config.properties, fn name ->
        Enum.map(Spec.property(ctx, name, Map.get(spec, :temporals, [])), &{name, &1})
      end)

    %{
      ctx: ctx,
      init: spec.init,
      next: spec.next,
      actions_next: if(spec.next, do: Spec.actions(ctx, spec.next, config.next || "Next")),
      fairness: spec.fairness,
      invariants:
        Enum.map(config.invariants, &{&1, root.(&1)}) ++
          for({name, {:invariant, c}} <- obligations, do: {name, c}),
      init_props: for({name, {:init, c}} <- obligations, do: {name, c}),
      actions: for({name, {:action, a, sub}} <- obligations, do: {name, a, sub}),
      live: for({name, {:live, formula, atoms}} <- obligations, do: {name, formula, atoms}),
      constraints: Enum.map(config.constraints, root),
      action_constraints: Enum.map(config.action_constraints, root),
      perms: symmetry(env, config.symmetry),
      view: if(config.view, do: root.(config.view)),
      possible:
        Enum.map(config.possible, fn name ->
          {name, root.(name),
           if(Spec.action?({:name, name, nil}, env), do: :action, else: :state)}
        end),
      nvars: tuple_size(ctx.variables)
    }
  end

  defp symmetry(_env, nil), do: []

  # The permutations of the symmetry set, closed under composition (as
  # TLC does): the group that the set generates. The identity is left out.
  defp symmetry(env, name) do
    gens =
      {:name, name, nil}
      |> Eval.eval(env)
      |> Value.enum()
      |> Enum.map(fn f ->
        f |> Value.pairs() |> Enum.reject(fn {k, v} -> k == v end) |> Map.new()
      end)
      |> Enum.reject(&(&1 == %{}))
      |> Enum.uniq()

    gens |> close_group(MapSet.new(gens), gens) |> MapSet.to_list() |> Enum.sort()
  end

  defp close_group(_gens, group, []), do: group

  defp close_group(gens, group, frontier) do
    new =
      for p <- frontier,
          g <- gens,
          c = compose(g, p),
          c != %{},
          not MapSet.member?(group, c),
          uniq: true,
          do: c

    close_group(gens, MapSet.union(group, MapSet.new(new)), new)
  end

  defp compose(g, p) do
    keys = MapSet.union(MapSet.new(Map.keys(g)), MapSet.new(Map.keys(p)))

    for k <- keys,
        v = Map.get(g, Map.get(p, k, k), Map.get(p, k, k)),
        v != k,
        into: %{},
        do: {k, v}
  end

  # -- Search --

  defp search(base, model) do
    live? = model.live != []

    warnings =
      if live? do
        if(model.constraints != [],
          do: [
            "Warning: Declaring state constraints during liveness checking is dangerous: Please consult section 14.3.5 on page 247 of Specifying Systems."
          ],
          else: []
        ) ++
          if model.perms != [],
            do: [
              "Warning: Declaring symmetry during liveness checking is dangerous. Please check liveness without symmetry defined."
            ],
            else: []
      else
        []
      end

    base = %{base | warnings: warnings}

    st = %{
      seen: %{},
      nodes: %{},
      queue: :queue.new(),
      next_id: 0,
      depth: 0,
      generated: 0,
      edges: if(live? or base.graph, do: %{}, else: nil),
      init_ids: []
    }

    st = initial_states(base, model, st)

    # Without a next-state action, TLC stops after the initial states: an
    # error when there are initial states.
    if model.next == nil and not :queue.is_empty(st.queue) do
      raise Stop,
        result:
          error_result(
            model.ctx,
            "No next state actions defined to generate successor states from.",
            [],
            base,
            st,
            :spec_eval
          )
    end

    st = if model.next == nil, do: st, else: loop(base, model, st)

    stats = stats(st)

    result =
      if live?,
        do: check_liveness(base, model, st, stats),
        else: %{result(model.ctx) | status: :ok, stats: stats, warnings: base.warnings}

    result = if result.status == :ok, do: check_postconditions(model, result), else: result
    if base.graph, do: Map.put(result, :graph, graph(st)), else: result
  end

  # The state graph (option `:graph`): the states, and the steps as pairs
  # of state indexes.
  defp graph(st) do
    states = for i <- 0..(st.next_id - 1)//1, do: st.nodes |> Map.fetch!(i) |> elem(0)
    edges = for {from, tos} <- st.edges, {to, _label} <- tos, uniq: true, do: {from, to}
    %{states: states, edges: edges}
  end

  # The _POSSIBLE predicates: each one must be true in some state (or on
  # some step, for an action). The counts are in the named register
  # "s:_possible", as in TLC.
  defp witness(%{possible: []}, _kind, _env), do: :ok

  defp witness(model, kind, env) do
    for {name, {e, scope, bound, frames}, ^kind} <- model.possible do
      holds =
        try do
          Eval.bool(e, %{env | scope: scope, bound: bound, frames: frames})
        rescue
          Value.Error -> false
        end

      registers = Process.get(:tla_registers) || %{}
      {:fun, counts} = Map.get(registers, "s:_possible", {:fun, %{}})

      counts =
        Map.update(counts, name, if(holds, do: 1, else: 0), &(&1 + if(holds, do: 1, else: 0)))

      Process.put(:tla_registers, Map.put(registers, "s:_possible", {:fun, counts}))
    end

    :ok
  end

  defp unwitnessed(model) do
    {:fun, counts} = Map.get(Process.get(:tla_registers) || %{}, "s:_possible", {:fun, %{}})
    Enum.find(model.possible, fn {name, _, _} -> Map.get(counts, name, 0) == 0 end)
  end

  # The POSTCONDITION predicates, after the search (TLCGet("stats") gives
  # the final counts).
  defp check_postconditions(model, result) do
    case unwitnessed(model) do
      {name, _, _} -> %{result | status: :violated, kind: :possible, property: name}
      nil -> check_postconditions2(model, result)
    end
  end

  defp check_postconditions2(model, result) do
    Process.put(:tla_stats_distinct, result.stats.distinct)
    Process.put(:tla_stats_generated, result.stats.generated)
    Process.put(:tla_stats_queue, 0)
    env = %{Eval.new(model.ctx) | level: result.stats.depth}

    Enum.find_value(model.ctx.config.postconditions, result, fn name ->
      holds =
        try do
          Eval.bool({:name, name, nil}, env)
        rescue
          Value.Error -> false
        end

      unless holds, do: %{result | status: :violated, kind: :postcondition, property: name}
    end)
  end

  defp stats(st),
    do: %{
      generated: st.generated,
      distinct: map_size(st.seen),
      depth: st.depth,
      left: :queue.len(st.queue)
    }

  defp initial_states(base, model, st) do
    env = %{Eval.new(model.ctx) | state: %{}, label: "Init", level: 0}

    partials =
      try do
        model.init
        |> Enum.reduce([{%{}, "Init"}], fn {e, scope, bound, frames}, acc ->
          Enum.flat_map(acc, fn {p, label} ->
            Eval.gen(
              e,
              %{env | scope: scope, bound: bound, frames: frames, state: p, label: label},
              :init
            )
          end)
        end)
      rescue
        err in Value.Error ->
          raise Stop,
            result: error_result(model.ctx, Exception.message(err), [], base, st, :spec_eval)
      end

    # TLC checks each initial state when it generates it: the count of
    # generated states grows one by one.
    Enum.reduce(partials, st, fn {p, _label}, st ->
      st = %{st | generated: st.generated + 1}
      state = complete!(model, p, "the initial predicate", [], base, st)
      visit(base, model, st, state, nil, nil, 1)
    end)
  end

  defp loop(base, model, st) do
    case :queue.out(st.queue) do
      {:empty, _} ->
        st

      {{:value, id}, queue} ->
        st = %{st | queue: queue}

        if base.max_states != :infinity and map_size(st.seen) > base.max_states do
          raise Stop,
            result: %{
              result(model.ctx)
              | status: :incomplete,
                stats: stats(st),
                warnings: base.warnings
            }
        end

        loop(base, model, expand(base, model, st, id))
    end
  end

  # The steps from a state: the actions of the next-state relation (see
  # `Spec.actions/3`), one after the other, as TLC does. The count of
  # generated states grows by the steps of each action before their check.
  defp expand(base, model, st, id) do
    {state, _parent, _label, depth} = Map.fetch!(st.nodes, id)
    Eval.reset_cache()
    Process.put(:tla_stats_distinct, map_size(st.seen))
    Process.put(:tla_stats_queue, :queue.len(st.queue))
    Process.put(:tla_trace_fun, fn _ -> trace_value(model, trace(st, id)) end)

    {st, any?} =
      Enum.reduce(model.actions_next, {st, false}, fn {{e, scope, bound, frames}, name},
                                                      {st, any?} ->
        Process.put(:tla_stats_generated, st.generated)
        Process.put(:tla_extra_generated, 0)

        env = %{
          Eval.new(model.ctx)
          | scope: scope,
            bound: bound,
            frames: frames,
            state: state,
            next: %{},
            label: name,
            level: depth
        }

        successors =
          try do
            Eval.gen(e, env, :next)
          rescue
            # TLC: an error of an operator of a standard module is a general
            # error; an error of the core semantics is an error of the spec.
            err in Value.Error ->
              kind = if err.module, do: :error, else: :spec_eval

              raise Stop,
                result:
                  error_result(model.ctx, Exception.message(err), trace(st, id), base, st, kind)
          end

        st = %{
          st
          | generated: st.generated + length(successors) + Process.get(:tla_extra_generated, 0)
        }

        st =
          Enum.reduce(successors, st, fn {p, label}, st ->
            next_state = complete!(model, p, "the action #{label}", trace(st, id), base, st)
            step(base, model, st, id, state, next_state, label, depth)
          end)

        {st, any? or successors != []}
      end)

    if not any? and base.deadlock do
      raise Stop,
        result: %{
          result(model.ctx)
          | status: :violated,
            kind: :deadlock,
            trace: trace(st, id),
            stats: stats(st),
            warnings: base.warnings
        }
    end

    st
  end

  defp step(base, model, st, id, state, next_state, label, depth),
    do: visit(base, model, st, next_state, {id, state}, label, depth + 1)

  defp action_holds?(
         {a, scope, bound, frames},
         {sub, sscope, sbound, sframes},
         env,
         model,
         st,
         id,
         base
       ) do
    try do
      Eval.bool(a, %{env | scope: scope, bound: bound, frames: frames}) or
        Value.eq?(
          Eval.eval(sub, %{env | scope: sscope, bound: sbound, frames: sframes, primed: true}),
          Eval.eval(sub, %{env | scope: sscope, bound: sbound, frames: sframes})
        )
    rescue
      err in Value.Error ->
        raise Stop,
          result: error_result(model.ctx, Exception.message(err), trace(st, id), base, st)
    end
  end

  # Visits a state that the initial predicate (`from` is nil) or a step
  # from `{id, state}` gives, in the order of TLC:
  #
  # 1. The state is in the model when it satisfies the state constraints
  #    and the step satisfies the action constraints.
  # 2. A state in the model goes in the set of seen states (when it is
  #    new) and in the queue.
  # 3. A new state (or one that is not in the model) must satisfy the
  #    invariants (and, for an initial state, the state predicates of the
  #    properties).
  # 4. Each step must satisfy the action properties.
  defp visit(base, model, st, state, from, label, depth) do
    parent = if from, do: elem(from, 0)
    # TLC sorts the sets of a state when it computes the fingerprint; a set
    # with typed model values of different types cannot be sorted.
    if Process.get(:tla_typed_model_values),
      do: state |> Tuple.to_list() |> Enum.each(&check_order/1)

    partial_trace = fn ->
      if(parent, do: trace(st, parent), else: []) ++ [%{state: state, action: label}]
    end

    Process.put(:tla_trace_fun, fn _ -> trace_value(model, partial_trace.()) end)
    # TLCGet("level") is the level of the state (1 for an initial state);
    # in a step, the level of the first state (the primed level is one
    # more).
    env = %{Eval.new(model.ctx) | state: state, level: depth}

    step_env =
      if from, do: %{Eval.new(model.ctx) | state: elem(from, 1), next: state, level: depth - 1}

    # The _POSSIBLE predicates go after the constraints, as in TLC: a
    # state predicate is a state constraint, an action is an action
    # constraint (both always true).
    in_model =
      Enum.all?(model.constraints, &holds?(&1, env, model, st, nil, base, partial_trace)) and
        witness(model, :state, env) == :ok and
        (from == nil or
           (Enum.all?(model.action_constraints, &holds?(&1, step_env, model, st, parent, base)) and
              witness(model, :action, step_env) == :ok))

    key = fingerprint(model, state)

    {st, unseen} =
      cond do
        not in_model ->
          {st, :outside}

        Map.has_key?(st.seen, key) ->
          {record_edge(st, parent, Map.fetch!(st.seen, key), label), nil}

        true ->
          id = st.next_id

          st = %{
            st
            | seen: Map.put(st.seen, key, id),
              nodes: Map.put(st.nodes, id, {state, parent, label, depth}),
              next_id: id + 1,
              depth: max(st.depth, depth),
              init_ids: if(parent == nil, do: [id | st.init_ids], else: st.init_ids)
          }

          {record_edge(st, parent, id, label), {:new, id}}
      end

    if unseen != nil do
      if from == nil do
        Enum.each(model.init_props, fn {name, closure} ->
          unless holds?(closure, env, model, st, nil, base, partial_trace),
            do: violation(model, base, st, :init_property, name, partial_trace.())
        end)
      end

      # TLC reports an error in an invariant of an initial state as an
      # error of the initial predicate.
      eval_kind = if from == nil, do: :spec_eval, else: :safety_eval

      Enum.each(model.invariants, fn {name, closure} ->
        unless holds?(closure, env, model, st, nil, base, partial_trace, eval_kind),
          do: violation(model, base, st, :invariant, name, partial_trace.())
      end)
    end

    if from do
      Enum.each(model.actions, fn {name, a, sub} ->
        unless action_holds?(a, sub, step_env, model, st, parent, base),
          do: violation(model, base, st, :action_property, name, partial_trace.())
      end)
    end

    # A new state goes in the queue after the checks, as in TLC.
    case unseen do
      {:new, id} -> %{st | queue: :queue.in(id, st.queue)}
      _ -> st
    end
  end

  defp violation(model, base, st, kind, name, trace) do
    raise Stop,
      result: %{
        result(model.ctx)
        | status: :violated,
          kind: kind,
          property: name,
          trace: trace,
          stats: stats(st),
          warnings: base.warnings
      }
  end

  defp record_edge(%{edges: nil} = st, _from, _to, _label), do: st
  defp record_edge(st, nil, _to, _label), do: st

  defp record_edge(st, from, to, label) do
    %{st | edges: Map.update(st.edges, from, [{to, label}], &[{to, label} | &1])}
  end

  # `kind` :auto: as an error of the next-state relation (see `expand/4`).
  defp holds?(closure, env, model, st, id, base, trace_fun \\ nil, kind \\ :auto)

  defp holds?({e, scope, bound, frames}, env, model, st, id, base, trace_fun, kind) do
    Eval.bool(e, %{env | scope: scope, bound: bound, frames: frames})
  rescue
    err in Value.Error ->
      trace = if trace_fun, do: trace_fun.(), else: if(id, do: trace(st, id), else: [])
      kind = if kind == :auto, do: if(err.module, do: :error, else: :spec_eval), else: kind
      # An error in the comparison of two values: TLC reports that it cannot
      # compute the fingerprint (an error of the specification).
      kind = if err.fingerprint and kind == :safety_eval, do: :spec_eval, else: kind
      raise Stop, result: error_result(model.ctx, Exception.message(err), trace, base, st, kind)
  end

  defp complete!(model, p, what, trace, base, st) do
    if map_size(p) == model.nvars do
      List.to_tuple(for i <- 0..(model.nvars - 1)//1, do: Map.fetch!(p, i))
    else
      missing =
        for i <- 0..(model.nvars - 1)//1, not Map.has_key?(p, i), do: elem(model.ctx.variables, i)

      raise Stop,
        result:
          error_result(
            model.ctx,
            "The state is not completely specified by #{what}. The following variables are not assigned: #{Enum.join(missing, ", ")}.",
            trace,
            base,
            st,
            :spec_eval
          )
    end
  end

  defp fingerprint(%{view: nil, perms: []}, state), do: state

  defp fingerprint(%{view: nil, perms: perms}, state) do
    Enum.reduce(perms, state, fn perm, best -> min(best, permute(state, perm)) end)
  end

  defp fingerprint(%{view: {e, scope, bound, frames}} = model, state) do
    env = %{Eval.new(model.ctx) | state: state, scope: scope, bound: bound, frames: frames}
    Value.canon(Eval.eval(e, env))
  end

  defp permute(state, perm),
    do: state |> Tuple.to_list() |> Enum.map(&permute_value(&1, perm)) |> List.to_tuple()

  defp permute_value({:mv, _} = v, perm), do: Map.get(perm, v, v)
  defp permute_value(%MapSet{} = s, perm), do: MapSet.new(s, &permute_value(&1, perm))

  defp permute_value({:seq, t}, perm),
    do: {:seq, t |> Tuple.to_list() |> Enum.map(&permute_value(&1, perm)) |> List.to_tuple()}

  defp permute_value({:fun, m}, perm),
    do: {:fun, Map.new(m, fn {k, v} -> {permute_value(k, perm), permute_value(v, perm)} end)}

  defp permute_value(v, _perm), do: v

  # -- Traces --

  defp trace(st, id), do: build_trace(st, id, [])

  defp build_trace(_st, nil, acc), do: acc

  defp build_trace(st, id, acc) do
    {state, parent, label, _depth} = Map.fetch!(st.nodes, id)
    build_trace(st, parent, [%{state: state, action: label} | acc])
  end

  # The value of TLCExt!Trace: the states of a trace, as records.
  defp trace_value(model, trace) do
    names = Tuple.to_list(model.ctx.variables)

    trace
    |> Enum.map(fn %{state: state} ->
      names
      |> Enum.with_index()
      |> Enum.map(fn {n, i} -> {n, elem(state, i)} end)
      |> Value.record()
    end)
    |> Value.tuple()
  end

  # -- Results --

  defp result(ctx) do
    %{
      status: :ok,
      kind: nil,
      property: nil,
      message: nil,
      trace: [],
      loop: nil,
      stats: %{generated: 0, distinct: 0, depth: 0, left: 0},
      warnings: [],
      variables: Tuple.to_list(ctx.variables)
    }
  end

  # The kinds of errors follow the exit codes of TLC: `:spec_eval` (a
  # state is not completely specified), `:safety_eval` (an invariant
  # cannot be evaluated), `:liveness_eval`, `:assert` (a false Assert), and
  # `:error` (any other error).
  defp error_result(ctx, message, trace, base, st \\ nil, kind \\ :error) do
    kind =
      if String.starts_with?(message, "The first argument of Assert"), do: :assert, else: kind

    %{
      result(ctx)
      | status: :error,
        kind: kind,
        message: message,
        trace: trace,
        stats:
          if(st,
            do: stats(st),
            else: %{generated: base.generated, distinct: 0, depth: 0, left: 0}
          ),
        warnings: base.warnings
    }
  end

  # -- Liveness --

  defp check_liveness(base, model, st, stats) do
    n = st.next_id
    nodes = for i <- 0..(n - 1)//1, do: Map.fetch!(st.nodes, i)
    states = nodes |> Enum.map(&elem(&1, 0)) |> List.to_tuple()

    succ =
      for i <- 0..(n - 1)//1 do
        st.edges |> Map.get(i, []) |> Enum.reverse() |> Enum.uniq_by(&elem(&1, 0))
      end
      |> List.to_tuple()

    graph = %{n: n, states: states, succ: succ, init: Enum.reverse(st.init_ids)}
    conds = Enum.map(model.fairness, &fair_condition(model, graph, &1))

    failure =
      Enum.find_value(model.live, fn {name, formula, atoms} ->
        lit = atom_evaluator(model, graph, atoms)
        kind = fn id -> atoms |> Map.fetch!(id) |> elem(0) end

        formula
        |> Temporal.dnf()
        |> Enum.find_value(fn disjunct ->
          parts = Temporal.split(disjunct)
          tableau = if parts.rest == true, do: nil, else: Temporal.tableau(parts.rest)
          check = %{ae: parts.ae, ea: parts.ea, tableau: tableau, lit: lit, kind: kind}

          case Liveness.check(graph, conds, check) do
            nil -> nil
            lasso -> {name, lasso}
          end
        end)
      end)

    case failure do
      nil ->
        %{result(model.ctx) | status: :ok, stats: stats, warnings: base.warnings}

      {name, lasso} ->
        trace =
          Enum.map(lasso.steps, fn {v, label} -> %{state: elem(states, v), action: label} end)

        %{
          result(model.ctx)
          | status: :violated,
            kind: :temporal,
            property: name,
            trace: trace,
            loop: lasso.loop,
            stats: stats,
            warnings: base.warnings
        }
    end
  rescue
    err in Value.Error ->
      # TLC reports an error in the evaluation of the liveness check as a
      # general error.
      error_result(model.ctx, Exception.message(err), [], base, st, :error)
  end

  # Evaluates the atoms of a property, with a memo: a state predicate at a
  # state, an action on a step.
  defp atom_evaluator(model, graph, atoms) do
    memo(fn
      {id, v, w} ->
        {kind, {e, scope, bound, frames}} = Map.fetch!(atoms, id)
        Eval.reset_cache()

        env = %{
          Eval.new(model.ctx)
          | state: elem(graph.states, v),
            scope: scope,
            bound: bound,
            frames: frames
        }

        case kind do
          :state -> Eval.bool(e, env)
          :action -> Eval.bool(e, %{env | next: elem(graph.states, w)})
        end
    end)
    |> then(fn f ->
      fn id, v, w ->
        case Map.fetch!(atoms, id) do
          {:state, _} -> f.({id, v, nil})
          {:action, _} -> f.({id, v, w})
        end
      end
    end)
  end

  # A fairness condition WF_sub(a) or SF_sub(a): the states where <a>_sub
  # is enabled, and a test for the steps that take it.
  defp fair_condition(
         model,
         graph,
         {strength, {sub, sscope, sbound, sframes}, {a, ascope, abound, aframes}}
       ) do
    sub_value = fn state, next ->
      env = %{
        Eval.new(model.ctx)
        | state: state,
          next: next,
          scope: sscope,
          bound: sbound,
          frames: sframes
      }

      Eval.eval(sub, if(next, do: %{env | primed: true}, else: env))
    end

    enabled =
      for v <- 0..(graph.n - 1)//1,
          state = elem(graph.states, v),
          enabled_at?(model, state, a, ascope, abound, aframes, sub_value),
          into: MapSet.new(),
          do: v

    taken = fn {v, w} ->
      s = elem(graph.states, v)
      t = elem(graph.states, w)

      env = %{
        Eval.new(model.ctx)
        | state: s,
          next: t,
          scope: ascope,
          bound: abound,
          frames: aframes
      }

      Eval.reset_cache()

      v != w and not Value.eq?(sub_value.(s, nil), sub_value.(s, t)) and Eval.bool(a, env)
    end

    taken = memo(taken)
    %{strength: strength, enabled: enabled, taken: fn v, w -> taken.({v, w}) end}
  end

  defp enabled_at?(model, state, a, scope, bound, frames, sub_value) do
    Eval.reset_cache()

    env = %{
      Eval.new(model.ctx)
      | state: state,
        next: %{},
        scope: scope,
        bound: bound,
        frames: frames,
        pseudo: true
    }

    current = sub_value.(state, nil)

    a
    |> Eval.gen(env, :next)
    |> Enum.any?(fn {p, _} ->
      try do
        not Value.eq?(sub_value.(state, p), current)
      rescue
        Value.Error -> true
      end
    end)
  end

  defp memo(fun) do
    table = :ets.new(:tla_memo, [:set, :private])

    fn key ->
      case :ets.lookup(table, key) do
        [{_, r}] ->
          r

        [] ->
          r = fun.(key)
          :ets.insert(table, {key, r})
          r
      end
    end
  end
end
