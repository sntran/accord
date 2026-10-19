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

  import Bitwise, only: [&&&: 2, |||: 2, <<<: 2, bnot: 1]

  alias Accord.TLA.Checker.{
    Purity,
    Constant,
    Context,
    Eval,
    Liveness,
    Random,
    SafetyTableau,
    Spec,
    Stdlib,
    Temporal,
    Value
  }

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
    Enum.each(
      [
        :tla_constants,
        :tla_field_orders,
        :tla_constant_defs,
        :tla_constant_scopes,
        :tla_levels,
        :tla_tlccache,
        :tla_normal_sets
      ],
      &Process.delete/1
    )

    Process.put(:tla_registers, %{})
    # Workers (TLC's -workers): each has its registers (TLCSet, TLCGet).
    Process.put(:tla_workers, Keyword.get(opts, :workers, 1))

    Enum.each(
      [:tla_worker_regs, :tla_worker_slot, :tla_expansions, :tla_simulation, :tla_stats_traces],
      &Process.delete/1
    )

    Random.setup(Keyword.get(opts, :seed))
    Process.put(:tla_string_ranks, ctx.string_ranks)
    # Coverage (TLC's -coverage): the counts of states of each action.
    Process.put(:tla_coverage, Keyword.get(opts, :coverage, false))
    Process.put(:tla_continue, Keyword.get(opts, :continue, false))

    if sim = Keyword.get(opts, :simulate) do
      Process.put(:tla_simulation, %{
        depth: Keyword.get(sim, :depth, 100),
        traces: Keyword.get(sim, :num, :infinity)
      })
    end

    Process.put(:tla_violations, [])
    Process.put(:tla_counts, %{})
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
      # Time-bound checking (TLC's -Dtlc2.TLC.stopAfter, in seconds).
      deadline:
        if(opts[:stop_after],
          do: System.monotonic_time(:millisecond) + trunc(opts[:stop_after] * 1000)
        ),
      # Depth-limited search (TLC's -dfid n): the states at depth n are
      # checked, not expanded. The search is breadth first: the result is
      # the result of TLC's iterative deepening, the order of the states is
      # not.
      max_depth: opts[:max_depth],
      # The liveness check of the simulation: TLC's default
      # (`:trace`) or its experimental one (`:experimental`, the system
      # property tlc2.tool.Simulator.experimentalLiveness).
      sim_liveness: Keyword.get(opts[:simulate] || [], :liveness, :trace),
      liveness_interval: Keyword.get(opts, :liveness_interval, {30_000, 600_000}),
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
        if model.live_full != [] and Enum.all?(model.live_full, fn {_, f, _} -> f == false end),
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

        model = %{model | invariants: model.invariants ++ extra}

        case Keyword.get(opts, :simulate) do
          nil -> search(base, model)
          sim -> simulate(base, model, sim)
        end
      end
    rescue
      e in Stop ->
        e.result

      e in [Value.Error, Context.Error, Accord.TLA.Checker.Parser.Error] ->
        error_result(ctx, Exception.message(e), [], base)
    end
    |> with_alias(ctx)
  end

  # ALIAS: the trace prints the fields of the alias expression in place of
  # the variables. TLC evaluates it with each state and its successor in
  # the trace (the state itself for the last one); on an error, the state
  # prints as it is.
  defp with_alias(%{trace: [_ | _] = trace} = result, %{config: %{alias: name}} = ctx)
       when is_binary(name) do
    states = Enum.map(trace, & &1.state)
    nexts = Enum.drop(states, 1) ++ [List.last(states)]
    trace_values = trace_value(%{ctx: ctx}, trace)

    aliased =
      Enum.zip(states, nexts)
      |> Enum.with_index(1)
      |> Enum.map(fn {{s, t}, i} ->
        Process.put(:tla_trace_fun, fn _ -> trace_prefix(trace_values, i) end)
        env = %{Eval.new(ctx) | state: s, next: t, level: i}

        try do
          v = Eval.eval({:name, name, nil}, env)
          Enum.map(Value.written_keys(v), &{&1, Value.apply_fun(v, &1)})
        rescue
          Value.Error -> nil
        end
      end)

    Map.put(result, :alias, aliased)
  end

  defp with_alias(result, _ctx), do: result

  defp trace_prefix({:seq, t}, i),
    do: {:seq, t |> Tuple.to_list() |> Enum.take(i) |> List.to_tuple()}

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
    Enum.each(model.live_full, fn {name, formula, _atoms} ->
      # TLC: WF_v(A) is []<>(~ENABLED <<A>>_v \/ <<A>>_v), one disjunct;
      # SF_v(A) is <>[]~ENABLED <<A>>_v \/ []<><<A>>_v, two disjuncts.
      strong = Enum.count(model.fairness, &(elem(&1, 0) == :strong))

      if Temporal.dnf_size(formula) * Integer.pow(2, strong) > 2_147_483_647 do
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
    Enum.each(ctx.assumes, fn {e, scope, _pos, {{l1, c1}, {l2, c2}}} ->
      where = "line #{l1}, col #{c1} to line #{l2}, col #{c2} of module #{module_of(ctx, scope)}"

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
                  message: "Evaluating assumption #{where} failed.\n" <> Exception.message(err)
              }
        end

      if value != true do
        raise Stop,
          result: %{
            result(ctx)
            | status: :violated,
              kind: :assumption,
              message: "Assumption #{where} is false."
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
      # The fairness conditions whose action has side effects (Print,
      # TLCSet): the liveness check evaluates them as TLC does, with the
      # same count of evaluations.
      impure:
        Enum.map(spec.fairness, fn {_, _, {a, scope, bound, _}} ->
          effects?(ctx, a, scope, bound)
        end),
      invariants:
        Enum.map(config.invariants, &{&1, root.(&1)}) ++
          for({name, {:invariant, c}} <- obligations, do: {name, c}),
      init_props: for({name, {:init, c}} <- obligations, do: {name, c}),
      actions: for({name, {:action, a, sub}} <- obligations, do: {name, a, sub}),
      live_obligations: for({name, {:live, _, _, _} = o} <- obligations, do: {name, o}),
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
    |> live_forms()
  end

  # The temporal properties: `live_full` has the negation of each
  # property as TLC checks it. For a property `F => P` with fairness
  # conditions F (see `Spec.property/3`), `live` has the negation of P
  # and `live_fair` the conditions of F, which the liveness check adds to
  # the fairness of the specification for this property: one check in
  # place of the 2^n disjuncts of the strong conditions of F. The
  # verdict is the same. The checker keeps the form of TLC when a
  # fairness condition has side effects (the counts of their
  # evaluations), and in the simulation mode.
  defp live_forms(model) do
    obligations = model.live_obligations
    full = for {name, {:live, f, atoms, _}} <- obligations, do: {name, f, atoms}

    pure? = fn fairness ->
      Enum.all?(fairness, fn {_, {sub, sscope, sbound, _}, {a, scope, bound, _}} ->
        not effects?(model.ctx, a, scope, bound) and not effects?(model.ctx, sub, sscope, sbound)
      end)
    end

    use_alt = not Enum.any?(model.impure)

    {live, fair} =
      obligations
      |> Enum.map(fn
        {name, {:live, _, _, {f, atoms, fairness}}} when use_alt ->
          if pure?.(fairness), do: {{name, f, atoms}, fairness}, else: nil

        _ ->
          nil
      end)
      |> Enum.zip(full)
      |> Enum.map(fn
        {nil, l} -> {l, []}
        {alt, _} -> alt
      end)
      |> Enum.unzip()

    model
    |> Map.delete(:live_obligations)
    |> Map.merge(%{live: live, live_fair: fair, live_full: full})
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
      init_ids: [],
      # A property with its own fairness has no safety part (each
      # disjunct of its negation has the fairness of F).
      safety:
        if(live?,
          do:
            SafetyTableau.new(
              for({l, []} <- Enum.zip(model.live, model.live_fair), do: l),
              model.fairness
            )
        ),
      live_cache: if(live?, do: :ets.new(:tla_live_atoms, [:set, :private]))
    }

    try do
      explore(base, model, st, live?)
    after
      if st.live_cache, do: :ets.delete(st.live_cache)
    end
  end

  defp explore(base, model, st, live?) do
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

    # TLC checks liveness on the partial graph during the search (the
    # default -lncheck): the first time 3 s after the start, then each
    # minute, with at most 20% of the time. The checker is slower than TLC,
    # so the times are longer (`:liveness_interval`, `{first, every}` in
    # ms; `nil` checks only at the end, as -lncheck final).
    if live? do
      case base.liveness_interval do
        {first, _every} -> Process.put(:tla_live_timer, {now_ms() + first, 0})
        nil -> Process.delete(:tla_live_timer)
      end
    end

    st = if model.next == nil, do: st, else: loop(base, model, st)
    Process.delete(:tla_live_timer)

    stats = stats(st)

    result =
      if live?,
        do: check_liveness(base, model, st, stats),
        else: %{result(model.ctx) | status: :ok, stats: stats, warnings: base.warnings}

    Stdlib.switch_worker(nil)
    result = if result.status == :ok, do: check_postconditions(model, result), else: result
    # With `:continue`: the violations that the search found.
    result =
      if Process.get(:tla_continue),
        do: Map.put(result, :violations, Enum.reverse(Process.get(:tla_violations, []))),
        else: result

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
    counts = Stdlib.possible_counts()
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
      left: :queue.len(st.queue),
      init: length(st.init_ids)
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
    st0 = st

    st =
      Enum.reduce(partials, st, fn {p, _label}, st ->
        # The time limit (`:stop_after`) holds also for the initial states.
        if base.deadline && System.monotonic_time(:millisecond) > base.deadline do
          raise Stop,
            result: %{
              result(model.ctx)
              | status: :incomplete,
                stats: stats(st),
                warnings: base.warnings
            }
        end

        st = %{st | generated: st.generated + 1}
        state = complete!(model, p, "the initial predicate", [], base, st)
        visit(base, model, st, state, nil, nil, 1)
      end)

    count(:init, length(partials), st.next_id - st0.next_id)
    st
  end

  # The workers take the states in turn.
  defp next_worker do
    n = Process.get(:tla_workers, 1)

    if n > 1 do
      k = Process.get(:tla_expansions, 0)
      Process.put(:tla_expansions, k + 1)
      Stdlib.switch_worker(rem(k, n) + 1)
    end
  end

  # A fairness condition of the next-state relation of the search, with
  # no constraint, symmetry, or view.
  # Tells if an expression calls an operator with side effects.
  defp effects?(ctx, e, scope, bound), do: Purity.effects?(ctx, e, scope, bound)

  defp next_fairness?(model, {_strength, _sub, a}) do
    model.constraints == [] and model.action_constraints == [] and model.perms == [] and
      model.view == nil and model.next != nil and no_pos(a) == no_pos(model.next)
  end

  # An expression without the positions of its names and applications.
  defp no_pos({:name, n, _}), do: {:name, n}
  defp no_pos({:app, op, args, _}), do: {:app, op, no_pos(args)}

  defp no_pos(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.map(&no_pos/1) |> List.to_tuple()

  defp no_pos(l) when is_list(l), do: Enum.map(l, &no_pos/1)
  defp no_pos(%{} = m) when not is_struct(m), do: Map.new(m, fn {k, v} -> {k, no_pos(v)} end)
  defp no_pos(x), do: x

  # The coverage counts of an action (or of the initial predicate).
  defp count(key, generated, distinct) do
    if Process.get(:tla_coverage) do
      counts = Process.get(:tla_counts)
      {g, d} = Map.get(counts, key, {0, 0})
      Process.put(:tla_counts, Map.put(counts, key, {g + generated, d + distinct}))
    end
  end

  defp now_ms, do: System.monotonic_time(:millisecond)

  # A liveness check of the states that the search expanded (see
  # `explore/4`). A state in the queue has no steps yet, not even its
  # stuttering step, as in TLC's behavior graph.
  defp periodic_liveness(base, model, st) do
    case Process.get(:tla_live_timer) do
      {due, size} when st.next_id > size ->
        if now_ms() >= due do
          t0 = now_ms()
          partial = Map.put(st, :no_stutter, MapSet.new(:queue.to_list(st.queue)))
          result = check_liveness(base, model, partial, stats(st))
          if result.status != :ok, do: raise(Stop, result: result)
          {_, every} = base.liveness_interval
          dt = now_ms() - t0
          Process.put(:tla_live_timer, {now_ms() + max(every, 4 * dt), st.next_id})
        end

      _ ->
        :ok
    end
  end

  defp loop(base, model, st) do
    periodic_liveness(base, model, st)

    case :queue.out(st.queue) do
      {:empty, _} ->
        st

      {{:value, id}, queue} ->
        if base.deadline && System.monotonic_time(:millisecond) > base.deadline do
          raise Stop,
            result: %{
              result(model.ctx)
              | status: :incomplete,
                stats: stats(st),
                warnings: base.warnings
            }
        end

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

        # TLCSet("exit", TRUE) stops the search (TLC's mainChecker.stop).
        if exit_requested?() do
          raise Stop,
            result: %{
              result(model.ctx)
              | status: :incomplete,
                stats: stats(st),
                warnings: base.warnings
            }
        end

        if base.max_depth && elem(Map.fetch!(st.nodes, id), 3) >= base.max_depth do
          loop(base, model, st)
        else
          st = expand(base, model, st, id)
          live_eval(base, model, st, id)
          loop(base, model, safety_step(base, model, st, id))
        end
    end
  end

  # The steps from a state: the actions of the next-state relation (see
  # `Spec.actions/3`), one after the other, as TLC does. The count of
  # generated states grows by the steps of each action before their check.
  defp expand(base, model, st, id) do
    {state, _parent, _label, depth} = Map.fetch!(st.nodes, id)
    Eval.reset_cache()
    Random.at_state({id, state})
    next_worker()
    Process.put(:tla_stats_distinct, map_size(st.seen))
    # The length of the queue only when TLCGet asks for it (:queue.len is
    # linear).
    Process.put(:tla_stats_queue, {:queue, st.queue})
    Process.put(:tla_trace_fun, fn _ -> trace_value(model, trace(st, id)) end)

    {st, any?} =
      model.actions_next
      |> Enum.with_index()
      |> Enum.reduce({st, false}, fn {{{e, scope, bound, frames}, name}, index}, {st, any?} ->
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
              # The state that TLC cannot fingerprint counts as generated.
              st = if err.fingerprint == :state, do: %{st | generated: st.generated + 1}, else: st

              raise Stop,
                result:
                  error_result(model.ctx, Exception.message(err), trace(st, id), base, st, kind)
          end

        st = %{st | generated: st.generated + Process.get(:tla_extra_generated, 0)}

        # TLC counts a successor when it checks it: after a violation, the
        # next successors do not count.
        st0 = st

        st =
          Enum.reduce(successors, st, fn {p, label}, st ->
            st = %{st | generated: st.generated + 1}
            next_state = complete!(model, p, "the action #{label}", trace(st, id), base, st)
            step(base, model, st, id, state, next_state, label, depth)
          end)

        count({:action, index}, length(successors), st.next_id - st0.next_id)

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

    key = fingerprint(model, state, depth)

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
            do: stop_violation(model, base, st, :init_property, name, partial_trace.())
        end)
      end

      # TLC reports an error in an invariant of an initial state as an
      # error of the initial predicate.
      eval_kind = if from == nil, do: :spec_eval, else: :safety_eval

      # With `:continue` (TLC's -continue), the first invariant that a
      # state violates is reported, and the search goes on.
      Enum.find(model.invariants, fn {name, closure} ->
        if holds?(closure, env, model, st, nil, base, partial_trace, eval_kind) do
          false
        else
          violation(model, base, st, :invariant, name, partial_trace.())
          true
        end
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
      {:new, id} ->
        st = %{st | queue: :queue.in(id, st.queue)}
        if from == nil, do: safety_init(base, model, st, id), else: st

      _ ->
        st
    end
  end

  # -- Simulation (TLC's -simulate) --

  # Random behaviors, as TLC's simulator with one worker: each behavior
  # starts at a random initial state; each step takes a random action
  # (the next ones in an order of a random prime when it has no step) and
  # a random successor of it. The checker checks the invariants and the
  # action properties of each successor of the action, and the temporal
  # properties of each behavior. The choices come from a java.util.Random
  # with the seed of TLC's worker, so the behaviors are the behaviors of
  # TLC for the same seed.
  defp simulate(base, model, sim) do
    max_depth = Keyword.get(sim, :depth, 100)
    max_traces = Keyword.get(sim, :num, :infinity)
    seed = Random.seed()

    st = %{
      seen: %{},
      nodes: %{},
      queue: :queue.new(),
      next_id: 0,
      depth: 0,
      generated: 0,
      edges: nil,
      init_ids: []
    }

    {inits, st} = simulation_inits(base, model, st)

    if inits == [] do
      raise Stop,
        result:
          error_result(
            model.ctx,
            "There is no initial state that satisfies the constraints.",
            [],
            base,
            st,
            :error
          )
    end

    inits = List.to_tuple(inits)
    # The worker has its own generators: a new stream of random values,
    # and the choices from the first long of the seed.
    Random.setup(seed)
    Random.choice_setup(Random.first_long(seed))
    simulation_loop(base, model, st, inits, max_depth, max_traces, 0)
  end

  defp simulation_inits(base, model, st) do
    env = %{Eval.new(model.ctx) | state: %{}, label: "Init", level: 0}

    partials =
      try do
        Enum.reduce(model.init, [{%{}, "Init"}], fn {e, scope, bound, frames}, acc ->
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

    st = %{st | generated: length(partials)}

    inits =
      for {p, _} <- partials,
          state = complete!(model, p, "the initial predicate", [], base, st),
          sim_check_state(base, model, st, state, [%{state: state, action: nil}], 1),
          Enum.all?(
            model.constraints,
            &holds?(&1, %{env | state: state, level: 1}, model, st, nil, base)
          ),
          do: state

    {inits, st}
  end

  # The invariants of a state of a behavior (at `level`).
  defp sim_check_state(base, model, st, state, trace, level) do
    Process.put(:tla_trace_fun, fn _ -> trace_value(model, trace) end)
    env = %{Eval.new(model.ctx) | state: state, level: level}
    kind = if level == 1, do: :spec_eval, else: :safety_eval

    Enum.each(model.invariants, fn {name, closure} ->
      unless holds?(closure, env, model, st, nil, base, fn -> trace end, kind),
        do: stop_violation(model, base, st, :invariant, name, trace)
    end)

    true
  end

  defp simulation_loop(base, model, st, _inits, _depth, max, traces)
       when max != :infinity and traces >= max,
       do: simulation_done(base, model, st)

  defp simulation_loop(base, model, st, inits, max_depth, max, traces) do
    Process.put(:tla_stats_traces, traces + 1)
    cur = elem(inits, floor(Random.choice_double() * tuple_size(inits)))
    trace = [%{state: cur, action: nil}]
    {st, trace} = simulate_trace(base, model, st, cur, trace, max_depth, 0)
    st = sim_liveness(base, model, st, trace)

    if exit_requested?(),
      do: simulation_done(base, model, st),
      else: simulation_loop(base, model, st, inits, max_depth, max, traces + 1)
  end

  defp simulation_done(base, model, st) do
    result = %{result(model.ctx) | status: :ok, stats: stats(st), warnings: base.warnings}
    Stdlib.switch_worker(nil)
    check_postconditions(model, result)
  end

  defp exit_requested?, do: Map.get(Process.get(:tla_registers) || %{}, "exit") == true

  defp simulate_trace(_base, _model, st, _cur, trace, max_depth, d) when d >= max_depth,
    do: {st, trace}

  defp simulate_trace(base, model, st, cur, trace, max_depth, d) do
    actions = List.to_tuple(model.actions_next)
    n = tuple_size(actions)
    index = floor(Random.choice_double() * n)
    p = Random.choice_prime()

    {st, nexts, _} =
      Enum.reduce_while(1..n//1, {st, [], index}, fn _, {st, [], i} ->
        {st, nexts} = sim_action(base, model, st, cur, trace, elem(actions, i), d + 1)

        if nexts == [],
          do: {:cont, {st, [], rem(i + p, n)}},
          else: {:halt, {st, nexts, i}}
      end)

    cond do
      nexts == [] and base.deadlock ->
        raise Stop,
          result: %{
            result(model.ctx)
            | status: :violated,
              kind: :deadlock,
              trace: trace,
              stats: stats(st),
              warnings: base.warnings
          }

      nexts == [] ->
        {st, trace}

      true ->
        nexts = List.to_tuple(Enum.reverse(nexts))
        {s1, label} = elem(nexts, floor(Random.choice_double() * tuple_size(nexts)))
        st = %{st | depth: max(st.depth, d + 2)}
        # TLC leaves out the stuttering steps of a behavior.
        trace = if s1 == cur, do: trace, else: trace ++ [%{state: s1, action: label}]

        if exit_requested?(),
          do: {st, trace},
          else: simulate_trace(base, model, st, s1, trace, max_depth, d + 1)
    end
  end

  # The successors of one action, with their checks; gives the ones in
  # the model.
  defp sim_action(base, model, st, cur, trace, {{e, scope, bound, frames}, name}, level) do
    Process.put(:tla_stats_generated, st.generated)
    Process.put(:tla_trace_fun, fn _ -> trace_value(model, trace) end)
    Eval.reset_cache()

    env = %{
      Eval.new(model.ctx)
      | scope: scope,
        bound: bound,
        frames: frames,
        state: cur,
        next: %{},
        label: name,
        level: level
    }

    successors =
      try do
        Eval.gen(e, env, :next)
      rescue
        # The simulator of TLC reports an error of the next-state relation
        # (a false Assert too) as an unexpected exception (EC.GENERAL).
        err in Value.Error ->
          result = error_result(model.ctx, Exception.message(err), trace, base, st, :error)
          raise Stop, result: %{result | kind: :error}
      end

    Enum.reduce(successors, {st, []}, fn {p, label}, {st, acc} ->
      st = %{st | generated: st.generated + 1}
      state = complete!(model, p, "the action #{label}", trace, base, st)
      strace = trace ++ [%{state: state, action: label}]
      sim_check_state(base, model, st, state, strace, level + 1)
      step_env = %{Eval.new(model.ctx) | state: cur, next: state, level: level}

      Enum.each(model.actions, fn {aname, a, sub} ->
        unless action_holds?(a, sub, step_env, model, st, nil, base),
          do: stop_violation(model, base, st, :action_property, aname, strace)
      end)

      senv = %{Eval.new(model.ctx) | state: state, level: level + 1}

      in_model =
        Enum.all?(model.constraints, &holds?(&1, senv, model, st, nil, base, fn -> strace end)) and
          Enum.all?(
            model.action_constraints,
            &holds?(&1, step_env, model, st, nil, base, fn -> strace end)
          )

      if in_model, do: {st, [{state, label} | acc]}, else: {st, acc}
    end)
  end

  # The temporal properties on one behavior, as TLC: the states of the
  # behavior with their steps; each state can stutter.
  defp sim_liveness(_base, %{live: []}, st, _trace), do: st

  defp sim_liveness(base, model, st, trace) do
    # The simulation checks the properties in the form of TLC.
    model = %{model | live: model.live_full, live_fair: Enum.map(model.live_full, fn _ -> [] end)}
    states = Enum.map(trace, & &1.state)
    ids = states |> Enum.uniq() |> Enum.with_index() |> Map.new()
    labels = Enum.map(trace, & &1.action)
    nodes = Map.new(ids, fn {s, i} -> {i, {s, nil, nil, 1}} end)

    edges =
      states
      |> Enum.zip(Enum.drop(labels, 1))
      |> Enum.zip(Enum.drop(states, 1))
      |> Enum.reduce(%{}, fn {{s, label}, t}, acc ->
        edge = {Map.fetch!(ids, t), label}
        Map.update(acc, Map.fetch!(ids, s), [edge], &[edge | &1])
      end)

    cache = :ets.new(:tla_live_atoms, [:set, :private])
    sim_impure(model, cache, ids, states, base.sim_liveness)

    gst = %{
      next_id: map_size(ids),
      nodes: nodes,
      edges: edges,
      init_ids: [Map.fetch!(ids, hd(states))],
      live_cache: cache,
      # TLC's experimental liveness simulation gives the last state of
      # the trace no steps (LiveCheck.checkTrace): no stuttering step,
      # unless the state is also earlier in the trace.
      no_stutter:
        if(base.sim_liveness == :experimental and List.last(states) not in Enum.drop(states, -1),
          do: MapSet.new([Map.fetch!(ids, List.last(states))]),
          else: MapSet.new()
        )
    }

    # A state without steps is in no cycle: TLC does not evaluate the
    # fairness conditions there.
    for v <- gst.no_stutter, {_, i} <- Enum.with_index(model.fairness) do
      if lc_get(cache, {:fair, i, :enabled, v}) == :none,
        do: lc_put(cache, {:fair, i, :enabled, v}, false)
    end

    result =
      try do
        check_liveness(base, model, gst, stats(st))
      after
        :ets.delete(cache)
      end

    if result.status == :ok,
      do: st,
      else: raise(Stop, result: %{result | stats: stats(st)})
  end

  # -- Liveness atoms during the search --

  # TLC evaluates the predicates of the liveness check on the steps of a
  # state when it expands the state (so an error comes up at once). The
  # values go to a cache for the check after the search.
  defp live_eval(_base, _model, %{live_cache: nil}, _id), do: :ok

  defp live_eval(base, model, st, id) do
    to = st.edges |> Map.get(id, []) |> Enum.reverse() |> Enum.map(&elem(&1, 0))
    succs = Enum.uniq(to ++ [id])
    {state, _, _, level} = Map.fetch!(st.nodes, id)
    cache = st.live_cache
    # TLCGet("level") in the predicates: the level of the state.
    Process.put(:tla_live_level, level)

    # The fairness conditions: first the steps, then ENABLED at the state.
    # A condition of the next-state relation itself (WF_v(Next)) needs no
    # evaluation: the steps of the graph are its steps (when no constraint
    # removes steps).
    fast = Enum.map(model.fairness, &next_fairness?(model, &1))
    sub_of = fn fc, x -> fc |> elem(1) |> then(&sub_value(model, &1)) |> then(& &1.(x, nil)) end

    # A condition with side effects: the evaluations of TLC. TLC checks
    # WF_v(A) as []<>(~ENABLED <<A>>_v \/ <<A>>_v) on each step, the
    # stuttering step too: ENABLED on each step, and A when ENABLED holds.
    # It checks the ENABLED of SF_v(A) one time on the state.
    if Enum.any?(model.impure) and lc_get(cache, {:impure, id}) == :none do
      lc_put(cache, {:impure, id}, true)
      state_of = fn w -> elem(Map.fetch!(st.nodes, w), 0) end
      steps = if id in to, do: to, else: to ++ [id]

      for {_tableau, choice} <- impure_solutions(model) do
        check_state(model, cache, choice, id, state)
        Enum.each(steps, &check_action(model, cache, choice, id, state, &1, state_of.(&1)))
      end
    end

    model.fairness
    |> Enum.with_index()
    |> Enum.each(fn {fc, index} ->
      Enum.each(to, fn w ->
        key = {:fair, index, :taken, id, w}

        if lc_get(cache, key) == :none do
          {next, _, _, _} = Map.fetch!(st.nodes, w)

          taken =
            if Enum.at(fast, index),
              do: id != w and not Value.eq?(sub_of.(fc, state), sub_of.(fc, next)),
              else: fair_taken?(model, fc, state, next, id == w)

          lc_put(cache, key, taken)
        end
      end)
    end)

    model.fairness
    |> Enum.with_index()
    |> Enum.each(fn {fc, index} ->
      key = {:fair, index, :enabled, id}

      if lc_get(cache, key) == :none do
        enabled =
          if Enum.at(fast, index),
            do: Enum.any?(to, &(lc_get(cache, {:fair, index, :taken, id, &1}) == {:ok, true})),
            else: fair_enabled?(model, fc, state)

        lc_put(cache, key, enabled)
      end
    end)

    model.live
    |> Enum.with_index()
    |> Enum.each(fn {{_name, _formula, atoms}, index} ->
      Enum.each(atoms, fn {aid, {kind, {e, scope, bound, frames}}} ->
        Enum.each(succs, fn w ->
          key = if kind == :state, do: {index, aid, w, nil}, else: {index, aid, id, w}

          if lc_get(st.live_cache, key) == :none do
            {next, _, _, _} = Map.fetch!(st.nodes, w)
            Eval.reset_cache()

            env = %{Eval.new(model.ctx) | scope: scope, bound: bound, frames: frames}

            value =
              case kind do
                :state -> Eval.bool(e, %{env | state: next})
                :action -> Eval.bool(e, %{env | state: state, next: next})
              end

            lc_put(st.live_cache, key, value)
          end
        end)
      end)
    end)
  rescue
    err in Value.Error ->
      raise Stop,
        result: error_result(model.ctx, Exception.message(err), trace(st, id), base, st, :error)
  end

  # -- Fairness with side effects --

  # TLC checks a liveness property on each disjunct (a "solution") of the
  # disjunctive normal form of the negation of the property and the
  # fairness. SF_v(A) is <>[]~ENABLED <<A>>_v \/ []<><<A>>_v, so it gives
  # two kinds of solutions: one checks ENABLED on the states, the other
  # checks A on the steps. WF_v(A) is []<>(~ENABLED <<A>>_v \/ <<A>>_v),
  # a check on the steps: ENABLED at the first state of the step, then A
  # when ENABLED holds. Each solution evaluates its checks again. For an
  # action with side effects (Print, TLCSet), the checker does the same
  # evaluations. `{tableau?, choice}`: `choice` maps a strong condition
  # to `:en` or `:act`.
  defp impure_solutions(model) do
    case Process.get(:tla_impure_solutions) do
      {^model, sols} ->
        sols

      _ ->
        tabs =
          for {_, f, _} <- model.live, d <- Temporal.dnf(f), do: Temporal.split(d).rest != true

        strong = for {{:strong, _, _}, i} <- Enum.with_index(model.fairness), do: i

        choices =
          Enum.reduce(strong, [%{}], fn i, acc ->
            for c <- acc, k <- [:en, :act], do: Map.put(c, i, k)
          end)

        sols = Enum.take(for(t <- tabs, c <- choices, do: {t, c}), 256)
        Process.put(:tla_impure_solutions, {model, sols})
        sols
    end
  end

  # The state checks of a solution at the state `id`.
  defp check_state(model, cache, choice, id, s) do
    model.fairness
    |> Enum.with_index()
    |> Enum.each(fn {fc, i} ->
      if Enum.at(model.impure, i) and Map.get(choice, i) == :en do
        en = fair_enabled?(model, fc, s)
        lc_put(cache, {:fair, i, :enabled, id}, en)
      end
    end)
  end

  # The action checks of a solution on the step from `id` to `wid`.
  defp check_action(model, cache, choice, id, s, wid, t) do
    model.fairness
    |> Enum.with_index()
    |> Enum.each(fn {{strength, _, _} = fc, i} ->
      if Enum.at(model.impure, i) do
        case {strength, Map.get(choice, i)} do
          {:weak, _} ->
            en = fair_enabled?(model, fc, s)
            taken = en and fair_taken?(model, fc, s, t, id == wid)
            merge_enabled(cache, i, id, en)
            lc_put(cache, {:fair, i, :taken, id, wid}, taken)

          {:strong, :act} ->
            lc_put(cache, {:fair, i, :taken, id, wid}, fair_taken?(model, fc, s, t, id == wid))

          _ ->
            :ok
        end
      end
    end)
  end

  defp merge_enabled(cache, i, id, en) do
    key = {:fair, i, :enabled, id}

    case lc_get(cache, key) do
      {:ok, true} -> :ok
      _ -> lc_put(cache, key, en)
    end
  end

  # The evaluations of TLC's liveness check of a simulation trace
  # (LiveCheck1.constructBEGraph): for each solution, the checks of the
  # first state and of its stuttering step, then for each step to a new
  # state the checks of the state, of its stuttering step, and of the
  # step; for a step to a known state, the check of a new step. With a
  # tableau, TLC checks each state and each step of the trace. With the
  # experimental liveness of the simulator (LiveCheck), TLC checks each
  # step of the trace and its stuttering step, as in a search.
  defp sim_impure(model, cache, ids, states, mode) do
    if Enum.any?(model.impure) do
      [s0 | _] = states
      id = &Map.fetch!(ids, &1)
      # TLCGet("level"): the level of the first state of the check.
      at = &Process.put(:tla_live_level, &1)
      steps = states |> Enum.with_index(1) |> Enum.chunk_every(2, 1, :discard)

      for {tableau, choice} <- impure_solutions(model) do
        case mode do
          :experimental ->
            at.(1)
            check_state(model, cache, choice, id.(s0), s0)

            Enum.each(steps, fn [{s, l}, {t, _}] ->
              at.(l)
              check_state(model, cache, choice, id.(s), s)
              check_action(model, cache, choice, id.(s), s, id.(s), s)
              if s != t, do: check_action(model, cache, choice, id.(s), s, id.(t), t)
            end)

            last = List.last(states)
            at.(length(states))
            check_state(model, cache, choice, id.(last), last)

          _ ->
            at.(1)
            check_state(model, cache, choice, id.(s0), s0)
            check_action(model, cache, choice, id.(s0), s0, id.(s0), s0)

            steps
            |> Enum.reduce({MapSet.new([s0]), MapSet.new()}, fn [{s, l}, {t, lt}], {seen, done} ->
              cond do
                tableau ->
                  at.(lt)
                  check_state(model, cache, choice, id.(t), t)
                  at.(l)
                  check_action(model, cache, choice, id.(s), s, id.(t), t)
                  at.(lt)
                  check_action(model, cache, choice, id.(t), t, id.(t), t)
                  {seen, done}

                not MapSet.member?(seen, t) ->
                  at.(lt)
                  check_state(model, cache, choice, id.(t), t)
                  check_action(model, cache, choice, id.(t), t, id.(t), t)
                  at.(l)
                  check_action(model, cache, choice, id.(s), s, id.(t), t)
                  {MapSet.put(seen, t), MapSet.put(done, {s, t})}

                not MapSet.member?(done, {s, t}) and s != t ->
                  at.(l)
                  check_action(model, cache, choice, id.(s), s, id.(t), t)
                  {seen, MapSet.put(done, {s, t})}

                true ->
                  {seen, done}
              end
            end)
        end
      end

      :ok
    end
  end

  # -- The safety part of temporal properties (see SafetyTableau) --

  defp safety_active?(st), do: st.safety != nil and SafetyTableau.active?(st.safety)

  defp safety_literal(model, st) do
    fn {:state, {e, scope, bound, frames}}, id ->
      {state, _, _, _} = Map.fetch!(st.nodes, id)
      Eval.reset_cache()

      Eval.bool(e, %{
        Eval.new(model.ctx)
        | state: state,
          scope: scope,
          bound: bound,
          frames: frames
      })
    end
  end

  # TLC reports an error in the evaluation of a property on an initial
  # state as an error of the initial state (a config error).
  defp safety_init(base, model, st, id) do
    if safety_active?(st) do
      {:ok, safety} = SafetyTableau.init(st.safety, id, safety_literal(model, st))
      %{st | safety: safety}
    else
      st
    end
  rescue
    err in Value.Error ->
      raise Stop, result: error_result(model.ctx, Exception.message(err), [], base, st, :config)
  end

  defp safety_step(base, model, st, id) do
    if safety_active?(st) do
      succs = fn s ->
        to = st.edges |> Map.get(s, []) |> Enum.reverse() |> Enum.map(&elem(&1, 0))
        Enum.uniq(to ++ [s])
      end

      case SafetyTableau.step(st.safety, id, succs, safety_literal(model, st)) do
        {:ok, safety} ->
          %{st | safety: safety}

        {:violated, name, ids} ->
          trace =
            Enum.map(ids, fn i ->
              {state, _, label, _} = Map.fetch!(st.nodes, i)
              %{state: state, action: label}
            end)

          raise Stop,
            result: %{
              result(model.ctx)
              | status: :violated,
                kind: :temporal_safety,
                property: name,
                trace: trace,
                stats: stats(st),
                warnings: base.warnings
            }
      end
    else
      st
    end
  rescue
    err in Value.Error ->
      raise Stop, result: error_result(model.ctx, Exception.message(err), [], base, st, :error)
  end

  defp violation(model, base, st, kind, name, trace) do
    if kind in [:invariant, :action_property] and Process.get(:tla_continue) == true do
      v = %{kind: kind, property: name, trace: trace}
      Process.put(:tla_violations, [v | Process.get(:tla_violations, [])])
      :continue
    else
      stop_violation(model, base, st, kind, name, trace)
    end
  end

  defp stop_violation(model, base, st, kind, name, trace) do
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

  defp fingerprint(%{view: nil, perms: []}, state, _level), do: state

  defp fingerprint(%{view: nil, perms: perms}, state, _level) do
    Enum.reduce(perms, state, fn perm, best -> min(best, permute(state, perm)) end)
  end

  # The VIEW sees the level of the state (TLCGet("level")).
  defp fingerprint(%{view: {e, scope, bound, frames}} = model, state, level) do
    env = %{
      Eval.new(model.ctx)
      | state: state,
        scope: scope,
        bound: bound,
        frames: frames,
        level: level
    }

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
      stats: %{generated: 0, distinct: 0, depth: 0, left: 0, init: 0},
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
            else: %{generated: base.generated, distinct: 0, depth: 0, left: 0, init: 0}
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

    graph = %{
      n: n,
      states: states,
      succ: succ,
      init: Enum.reverse(st.init_ids),
      no_stutter: Map.get(st, :no_stutter, MapSet.new())
    }

    conds =
      model.fairness
      |> Enum.with_index()
      |> Enum.map(&fair_condition(model, graph, &1, st.live_cache))

    failure =
      model.live
      |> Enum.zip(model.live_fair)
      |> Enum.with_index()
      |> Enum.find_value(fn {{{name, formula, atoms}, fair}, index} ->
        lit = atom_evaluator(model, graph, atoms, {st.live_cache, index})
        kind = fn id -> atoms |> Map.fetch!(id) |> elem(0) end

        # The fairness of the property (`F => P`), after the fairness of
        # the specification.
        conds =
          conds ++
            (fair
             |> Enum.with_index()
             |> Enum.map(fn {fc, j} ->
               fair_condition(model, graph, {fc, {:property, index, j}}, st.live_cache)
             end))

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
  # The values go to the cache of the search (a bit for each value).
  defp atom_evaluator(model, graph, atoms, {cache, index}) do
    f = fn {id, v, w} ->
      key = {index, id, v, w}

      case lc_get(cache, key) do
        {:ok, value} ->
          value

        :none ->
          value = eval_atom(model, graph, atoms, id, v, w)
          lc_put(cache, key, value)
          value
      end
    end

    f
    |> then(fn f ->
      fn id, v, w ->
        case Map.fetch!(atoms, id) do
          {:state, _} -> f.({id, v, nil})
          {:action, _} -> f.({id, v, w})
        end
      end
    end)
  end

  defp eval_atom(model, graph, atoms, id, v, w) do
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
  end

  # The cache of the liveness check keeps the booleans of one state (or
  # one step) in one entry, as two integers: the bits of the known values
  # and the bits of the true values. Each atom of a property and each
  # fairness condition has a bit. (One entry for each value takes about
  # 100 bytes: with several properties, kilobytes for each state.)
  defp lc_get(cache, key) do
    case lc_pack(key) do
      {pk, bit} ->
        case :ets.lookup(cache, pk) do
          [{_, known, val}] when (known &&& bit) != 0 -> {:ok, (val &&& bit) != 0}
          _ -> :none
        end

      :plain ->
        case :ets.lookup(cache, key) do
          [{_, v}] -> {:ok, v}
          [] -> :none
        end
    end
  end

  defp lc_put(cache, key, value) do
    case lc_pack(key) do
      {pk, bit} ->
        {known, val} =
          case :ets.lookup(cache, pk) do
            [{_, k, v}] -> {k, v}
            [] -> {0, 0}
          end

        val = if value, do: val ||| bit, else: val &&& bnot(bit)
        :ets.insert(cache, {pk, known ||| bit, val})

      :plain ->
        :ets.insert(cache, {key, value})
    end
  end

  defp lc_pack({:fair, i, :enabled, v}), do: {{:fe, v}, lc_bit({:fair, i})}
  defp lc_pack({:fair, i, :taken, v, w}), do: {{:ft, v, w}, lc_bit({:fair, i})}
  defp lc_pack({index, aid, v, w}) when is_integer(index), do: {{:a, v, w}, lc_bit({index, aid})}
  defp lc_pack(_), do: :plain

  defp lc_bit(slot) do
    slots = Process.get(:tla_live_slots, %{})

    case Map.fetch(slots, slot) do
      {:ok, bit} ->
        bit

      :error ->
        bit = 1 <<< map_size(slots)
        Process.put(:tla_live_slots, Map.put(slots, slot, bit))
        bit
    end
  end

  # A fairness condition WF_sub(a) or SF_sub(a): the states where <a>_sub
  # is enabled, and a test for the steps that take it.
  defp fair_condition(model, graph, {fc, index}, cache) do
    cached = fn key, fun ->
      case lc_get(cache, key) do
        {:ok, value} -> value
        :none -> fun.()
      end
    end

    enabled =
      for v <- 0..(graph.n - 1)//1,
          cached.({:fair, index, :enabled, v}, fn ->
            fair_enabled?(model, fc, elem(graph.states, v))
          end),
          into: MapSet.new(),
          do: v

    taken = fn v, w ->
      key = {:fair, index, :taken, v, w}

      cached.(key, fn ->
        t = fair_taken?(model, fc, elem(graph.states, v), elem(graph.states, w), v == w)
        lc_put(cache, key, t)
        t
      end)
    end

    %{strength: elem(fc, 0), enabled: enabled, taken: taken}
  end

  defp fair_enabled?(model, {_, sub, {a, ascope, abound, aframes}}, state) do
    enabled_at?(model, state, a, ascope, abound, aframes, sub_value(model, sub))
  end

  defp fair_taken?(_model, _fc, _s, _t, true), do: false

  defp fair_taken?(model, {_, sub, {a, ascope, abound, aframes}}, s, t, false) do
    sub_value = sub_value(model, sub)

    env = %{
      Eval.new(model.ctx)
      | state: s,
        next: t,
        scope: ascope,
        bound: abound,
        frames: aframes,
        level: Process.get(:tla_live_level, 1)
    }

    Eval.reset_cache()
    not Value.eq?(sub_value.(s, nil), sub_value.(s, t)) and Eval.bool(a, env)
  end

  defp sub_value(model, {sub, sscope, sbound, sframes}) do
    fn state, next ->
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
        pseudo: true,
        level: Process.get(:tla_live_level, 1)
    }

    current = sub_value.(state, nil)

    a
    |> Eval.gen(env, :next)
    |> Enum.any?(fn {p, _} ->
      try do
        not Value.eq?(sub_value.(state, p), current)
      rescue
        # TLC: the step of A does not give a value to a variable of the
        # subscript (TLC_STATE_NOT_COMPLETELY_SPECIFIED_LIVE).
        e in Value.Error ->
          if e.message =~ ~r/' has no value yet/,
            do:
              raise(Value.Error,
                message:
                  "In evaluation of the fairness condition, the step of the action does not give a value to all the variables of the subscript: " <>
                    e.message
              ),
            else: true
      end
    end)
  end
end
