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

  alias Accord.TLA.Checker.{Context, Eval, Liveness, Spec, Temporal, Value}

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
    Process.put(:tla_registers, %{})
    Process.put(:tla_properties, Keyword.get(opts, :properties, %{}))
    Process.put(:tla_warn, Keyword.get(opts, :warn, true))
    Process.put(:tla_deadlock, Keyword.get(opts, :deadlock, config.check_deadlock))

    base = %{
      ctx: ctx,
      deadlock: Keyword.get(opts, :deadlock, config.check_deadlock),
      max_states: Keyword.get(opts, :max_states, :infinity),
      generated: 0,
      warnings: []
    }

    try do
      check_assumptions(ctx)
      spec = Spec.analyze(ctx, config)

      if spec.init == nil do
        %{result(ctx) | status: :ok}
      else
        search(base, ctx |> model(spec, config))
      end
    rescue
      e in Stop ->
        e.result

      e in [Value.Error, Context.Error, Accord.TLA.Checker.Parser.Error] ->
        error_result(ctx, Exception.message(e), [], base)
    end
  end

  # -- Setup --

  defp check_assumptions(ctx) do
    Enum.each(ctx.assumes, fn {e, scope, {line, col}} ->
      env = %{Eval.new(ctx) | scope: scope}

      if Eval.eval(e, env) != true do
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
        Enum.map(Spec.property(ctx, name), &{name, &1})
      end)

    %{
      ctx: ctx,
      init: spec.init,
      next: spec.next,
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

    if model.next == nil,
      do: raise(Value.Error, message: "the specification has no next-state action")

    st = %{
      seen: %{},
      nodes: %{},
      queue: :queue.new(),
      next_id: 0,
      depth: 0,
      generated: 0,
      edges: if(live?, do: %{}, else: nil),
      init_ids: []
    }

    st = initial_states(base, model, st)
    st = loop(base, model, st)

    stats = stats(st)

    result =
      if live?,
        do: check_liveness(base, model, st, stats),
        else: %{result(model.ctx) | status: :ok, stats: stats, warnings: base.warnings}

    if result.status == :ok, do: check_postconditions(model, result), else: result
  end

  # The POSTCONDITION predicates, after the search (TLCGet("stats") gives
  # the final counts).
  defp check_postconditions(model, result) do
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

  # TLC counts a new state before it checks the invariants.
  defp stats_with_new(st), do: %{stats(st) | distinct: map_size(st.seen) + 1}

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

    st = %{st | generated: st.generated + length(partials)}

    Enum.reduce(partials, st, fn {p, _label}, st ->
      state = complete!(model, p, "the initial predicate", [], base, st)
      add_state(base, model, st, state, nil, nil, 1)
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

  defp expand(base, model, st, id) do
    {state, _parent, _label, depth} = Map.fetch!(st.nodes, id)
    Eval.reset_cache()
    Process.put(:tla_stats_distinct, map_size(st.seen))
    Process.put(:tla_stats_generated, st.generated)
    Process.put(:tla_stats_queue, :queue.len(st.queue))
    {e, scope, bound, frames} = model.next

    env = %{
      Eval.new(model.ctx)
      | scope: scope,
        bound: bound,
        frames: frames,
        state: state,
        next: %{},
        label: "Next",
        label_mode: true,
        level: depth
    }

    Process.put(:tla_extra_generated, 0)
    Process.put(:tla_trace_fun, fn _ -> trace_value(model, trace(st, id)) end)

    successors =
      try do
        Eval.gen(e, env, :next)
      rescue
        err in Value.Error ->
          raise Stop,
            result: error_result(model.ctx, Exception.message(err), trace(st, id), base, st)
      end

    st = %{
      st
      | generated: st.generated + length(successors) + Process.get(:tla_extra_generated, 0)
    }

    if successors == [] and base.deadlock do
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

    Enum.reduce(successors, st, fn {p, label}, st ->
      next_state = complete!(model, p, "the action #{label}", trace(st, id), base, st)
      step(base, model, st, id, state, next_state, label, depth)
    end)
  end

  defp step(base, model, st, id, state, next_state, label, depth) do
    env = %{Eval.new(model.ctx) | state: state, next: next_state, level: depth}

    if Enum.all?(model.action_constraints, &holds?(&1, env, model, st, id, base)) do
      Enum.each(model.actions, fn {name, a, sub} ->
        unless action_holds?(a, sub, env, model, st, id, base) do
          raise Stop,
            result: %{
              result(model.ctx)
              | status: :violated,
                kind: :action_property,
                property: name,
                trace: trace(st, id) ++ [%{state: next_state, action: label}],
                stats: stats(st),
                warnings: base.warnings
            }
        end
      end)

      add_state(base, model, st, next_state, id, label, depth + 1)
    else
      st
    end
  end

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

  # Adds a state that a step (or the initial predicate) gives.
  defp add_state(base, model, st, state, parent, label, depth) do
    key = fingerprint(model, state)

    case Map.fetch(st.seen, key) do
      {:ok, existing} ->
        record_edge(st, parent, existing, label)

      :error ->
        partial_trace = fn ->
          if(parent, do: trace(st, parent), else: []) ++ [%{state: state, action: label}]
        end

        Process.put(:tla_trace_fun, fn _ -> trace_value(model, partial_trace.()) end)
        # TLC checks a new state with the level of its predecessor (0 for
        # an initial state).
        env = %{Eval.new(model.ctx) | state: state, level: depth - 1}

        if parent == nil do
          Enum.each(model.init_props, fn {name, closure} ->
            unless holds?(closure, env, model, st, nil, base, partial_trace) do
              raise Stop,
                result: %{
                  result(model.ctx)
                  | status: :violated,
                    kind: :init_property,
                    property: name,
                    trace: partial_trace.(),
                    stats: stats_with_new(st),
                    warnings: base.warnings
                }
            end
          end)
        end

        Enum.each(model.invariants, fn {name, closure} ->
          unless holds?(closure, env, model, st, nil, base, partial_trace, :safety_eval) do
            raise Stop,
              result: %{
                result(model.ctx)
                | status: :violated,
                  kind: :invariant,
                  property: name,
                  trace: partial_trace.(),
                  stats: stats_with_new(st),
                  warnings: base.warnings
              }
          end
        end)

        if Enum.all?(model.constraints, &holds?(&1, env, model, st, nil, base, partial_trace)) do
          id = st.next_id

          st = %{
            st
            | seen: Map.put(st.seen, key, id),
              nodes: Map.put(st.nodes, id, {state, parent, label, depth}),
              queue: :queue.in(id, st.queue),
              next_id: id + 1,
              depth: max(st.depth, depth),
              init_ids: if(parent == nil, do: [id | st.init_ids], else: st.init_ids)
          }

          record_edge(st, parent, id, label)
        else
          st
        end
    end
  end

  defp record_edge(%{edges: nil} = st, _from, _to, _label), do: st
  defp record_edge(st, nil, _to, _label), do: st

  defp record_edge(st, from, to, label) do
    %{st | edges: Map.update(st.edges, from, [{to, label}], &[{to, label} | &1])}
  end

  defp holds?(closure, env, model, st, id, base, trace_fun \\ nil, kind \\ :error)

  defp holds?({e, scope, bound, frames}, env, model, st, id, base, trace_fun, kind) do
    Eval.bool(e, %{env | scope: scope, bound: bound, frames: frames})
  rescue
    err in Value.Error ->
      trace = if trace_fun, do: trace_fun.(), else: if(id, do: trace(st, id), else: [])
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
      error_result(model.ctx, Exception.message(err), [], base, st, :liveness_eval)
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
        frames: frames
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
