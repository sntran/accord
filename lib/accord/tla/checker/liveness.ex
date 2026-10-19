defmodule Accord.TLA.Checker.Liveness do
  @moduledoc """
  The liveness check of the checker: a search for a fair cycle that
  satisfies the negation of a property.

  The search uses the product of the state graph and the tableau of the
  negated property (see `Accord.TLA.Checker.Temporal`). A behavior can
  stutter at each state, so each state has a stuttering step to itself.

  One check takes a disjunct of the negated property:

  - `ea`: the formulas `p` of `<>[]p`. The cycle must stay where `p` is
    true (`p` is on nodes, or on steps if it is an action).
  - `ae`: the formulas `p` of `[]<>p`. The cycle must touch `p`.
  - `tableau`: the automaton of the other parts, or nil. The cycle must
    touch each acceptance set of the automaton.

  The fairness conditions of the specification remove the cycles that no
  fair behavior can follow. A weak condition is true on a cycle if the
  action is disabled at a node of the cycle, or a step of the cycle takes
  it. A strong condition is true on a cycle if the action is disabled at
  all nodes of the cycle, or a step of the cycle takes it. The search for
  strong conditions removes the enabled nodes and tries again on the
  smaller components (the method of Emerson and Lei).

  This module is independent of `Accord.Explore.Liveness`, so that the
  cross-check of the two engines stays meaningful.
  """

  alias Accord.TLA.Checker.Temporal

  @doc """
  Returns `nil` if no fair cycle satisfies the disjunct. Else returns a
  lasso: `%{steps: [{state, label}], loop: {:back_to, index, label} |
  :stuttering}`. The index starts at 0; the label is the label of the
  step that closes the cycle.

  `graph` has `n`, `succ` (a tuple of lists of `{state, label}`) and
  `init`. `check.kind.(id)` gives the kind of an atom (`:state` or
  `:action`), and `check.lit.(id, v, w)` its value on the step from `v`
  to `w` (a state predicate is evaluated at `v`; `w` can be nil).
  """
  def check(graph, conds, check) do
    lit = check.lit
    kind = check.kind
    holds = fn f, v, w -> holds?(f, v, w, lit) end

    automaton = check.tableau || %{nodes: %{0 => %{lits: [], succ: [0]}}, init: [0], accept: []}
    product = product(graph, automaton, lit, kind)

    # A formula of `<>[]` with only state predicates restricts the nodes;
    # all the formulas restrict the steps.
    state_ea =
      Enum.filter(check.ea, fn f -> f |> Temporal.atoms() |> Enum.all?(&(kind.(&1) == :state)) end)

    node_ok = fn x -> Enum.all?(state_ea, &holds.(&1, state(product, x), nil)) end

    edge_ok = fn x, y ->
      v = state(product, x)
      w = state(product, y)
      Enum.all?(check.ea, &holds.(&1, v, w))
    end

    region = for x <- 0..(product.size - 1)//1, node_ok.(x), into: MapSet.new(), do: x

    out = fn x ->
      for {y, label} <- elem(product.succ, x),
          MapSet.member?(region, y),
          edge_ok.(x, y),
          do: {y, label}
    end

    accept =
      Enum.map(automaton.accept, fn names ->
        for x <- region,
            {_, q} = elem(product.nodes, x),
            MapSet.member?(names, q),
            into: MapSet.new(),
            do: x
      end)

    on_states = fn f -> fn x, y -> holds.(f, state(product, x), state(product, y)) end end
    ae = Enum.map(check.ae, on_states)

    fair =
      Enum.map(conds, fn c ->
        %{
          strength: c.strength,
          enabled:
            for(
              x <- region,
              MapSet.member?(c.enabled, state(product, x)),
              into: MapSet.new(),
              do: x
            ),
          taken: fn x, y -> c.taken.(state(product, x), state(product, y)) end
        }
      end)

    region
    |> sccs(out)
    |> Enum.find_value(&fair_component(&1, out, fair, accept, ae))
    |> case do
      nil -> nil
      {component, plan} -> lasso(product, component, plan, out)
    end
  end

  defp state(product, x), do: elem(elem(product.nodes, x), 0)

  defp holds?(true, _v, _w, _lit), do: true
  defp holds?(false, _v, _w, _lit), do: false
  defp holds?({:lit, id, pol}, v, w, lit), do: lit.(id, v, w) == pol
  defp holds?({:and, items}, v, w, lit), do: Enum.all?(items, &holds?(&1, v, w, lit))
  defp holds?({:or, items}, v, w, lit), do: Enum.any?(items, &holds?(&1, v, w, lit))

  # -- The product of the state graph and the automaton --

  # The nodes that the initial states reach, by breadth-first search.
  defp product(graph, automaton, lit, kind) do
    %{nodes: anodes} = automaton
    ok = consistency(anodes, lit, kind)

    starts =
      for v <- graph.init,
          q <- automaton.init,
          ok.state.(q, v),
          uniq: true,
          do: {v, ok.rep.(q)}

    index = starts |> Enum.with_index() |> Map.new()
    queue = :queue.from_list(starts)
    parents = Map.new(starts, &{&1, nil})

    {index, parents, edges} = explore(queue, graph, anodes, ok, index, parents, %{})
    :ets.delete(ok.table)

    size = map_size(index)
    nodes = index |> Enum.sort_by(&elem(&1, 1)) |> Enum.map(&elem(&1, 0)) |> List.to_tuple()

    succ =
      for x <- 0..(size - 1)//1 do
        edges |> Map.get(x, []) |> Enum.reverse()
      end
      |> List.to_tuple()

    parent =
      for x <- 0..(size - 1)//1 do
        case Map.fetch!(parents, elem(nodes, x)) do
          nil -> nil
          {p, label} -> {Map.fetch!(index, p), label}
        end
      end
      |> List.to_tuple()

    %{size: size, nodes: nodes, succ: succ, parent: parent}
  end

  # The literals of an automaton node: the state predicates must hold at
  # the node, and the actions on the step from it. A state (a step) has a
  # signature: the values of all the state (action) atoms. The test of a
  # node depends only on the signature: it is computed one time for each
  # node and signature.
  defp consistency(anodes, lit, kind) do
    ids =
      anodes |> Enum.flat_map(fn {_, n} -> n.lits end) |> Enum.map(&elem(&1, 0)) |> Enum.uniq()

    state_ids = ids |> Enum.filter(&(kind.(&1) == :state)) |> Enum.sort()
    action_ids = ids |> Enum.filter(&(kind.(&1) == :action)) |> Enum.sort()
    spos = state_ids |> Enum.with_index() |> Map.new()
    apos = action_ids |> Enum.with_index() |> Map.new()

    lits =
      Map.new(anodes, fn {q, n} ->
        {q,
         {for({id, pol} <- n.lits, kind.(id) == :state, do: {Map.fetch!(spos, id), pol}),
          for({id, pol} <- n.lits, kind.(id) == :action, do: {Map.fetch!(apos, id), pol})}}
      end)

    # The nodes with the same obligations, acceptance, and action literals
    # are one class: in a product node, a class takes the place of the
    # nodes of the class that the state is consistent with (they have the
    # same successors and the same acceptance).
    class_key = fn q, n ->
      {Map.get(n, :cls, q), for({id, _} = l <- n.lits, kind.(id) == :action, do: l)}
    end

    rep =
      anodes
      |> Enum.group_by(fn {q, n} -> class_key.(q, n) end, &elem(&1, 0))
      |> Enum.flat_map(fn {_, qs} -> Enum.map(qs, &{&1, Enum.min(qs)}) end)
      |> Map.new()

    table = :ets.new(:tla_consistency, [:set, :private])

    cached = fn key, fun ->
      case :ets.lookup(table, key) do
        [{_, r}] ->
          r

        [] ->
          r = fun.()
          :ets.insert(table, {key, r})
          r
      end
    end

    ssig = fn v ->
      cached.({:s, v}, fn -> state_ids |> Enum.map(&lit.(&1, v, nil)) |> List.to_tuple() end)
    end

    asig = fn v, w ->
      cached.({:a, v, w}, fn -> action_ids |> Enum.map(&lit.(&1, v, w)) |> List.to_tuple() end)
    end

    %{
      table: table,
      rep: &Map.fetch!(rep, &1),
      state: fn q, v ->
        sig = ssig.(v)

        cached.({:qs, q, sig}, fn ->
          Enum.all?(elem(Map.fetch!(lits, q), 0), fn {i, pol} -> elem(sig, i) == pol end)
        end)
      end,
      # The successors of the node q that a state v is consistent with.
      succ: fn q, v ->
        sig = ssig.(v)

        cached.({:succ, q, sig}, fn ->
          Map.fetch!(anodes, q).succ
          |> Enum.filter(fn q2 ->
            Enum.all?(elem(Map.fetch!(lits, q2), 0), fn {i, pol} -> elem(sig, i) == pol end)
          end)
          |> Enum.map(&Map.fetch!(rep, &1))
          |> Enum.uniq()
        end)
      end,
      action: fn q, v, w ->
        case elem(Map.fetch!(lits, q), 1) do
          [] ->
            true

          alits ->
            sig = asig.(v, w)

            cached.({:qa, q, sig}, fn ->
              Enum.all?(alits, fn {i, pol} -> elem(sig, i) == pol end)
            end)
        end
      end
    }
  end

  defp explore(queue, graph, anodes, ok, index, parents, edges) do
    case :queue.out(queue) do
      {:empty, _} ->
        {index, parents, edges}

      {{:value, {v, q} = node}, queue} ->
        x = Map.fetch!(index, node)
        steps = [{v, nil} | elem(graph.succ, v)]

        {queue, index, parents, edges} =
          Enum.reduce(steps, {queue, index, parents, edges}, fn {w, label}, acc ->
            if ok.action.(q, v, w) do
              Enum.reduce(ok.succ.(q, w), acc, fn q2, {queue, index, parents, edges} ->
                target = {w, q2}

                {queue, index, parents} =
                  if Map.has_key?(index, target),
                    do: {queue, index, parents},
                    else:
                      {:queue.in(target, queue), Map.put(index, target, map_size(index)),
                       Map.put(parents, target, {node, label})}

                y = Map.fetch!(index, target)
                {queue, index, parents, Map.update(edges, x, [{y, label}], &[{y, label} | &1])}
              end)
            else
              acc
            end
          end)

        explore(queue, graph, anodes, ok, index, parents, edges)
    end
  end

  # -- Strongly connected components (Tarjan) --

  @doc false
  def sccs(nodes, out) do
    succ = fn v -> for {w, _} <- out.(v), MapSet.member?(nodes, w), do: w end

    init = %{index: 0, indices: %{}, low: %{}, stack: [], on: MapSet.new(), result: []}

    nodes
    |> Enum.sort()
    |> Enum.reduce(init, fn v, st ->
      if Map.has_key?(st.indices, v), do: st, else: strong(v, succ, st)
    end)
    |> Map.fetch!(:result)
  end

  defp strong(v, succ, st) do
    st = %{
      st
      | indices: Map.put(st.indices, v, st.index),
        low: Map.put(st.low, v, st.index),
        index: st.index + 1,
        stack: [v | st.stack],
        on: MapSet.put(st.on, v)
    }

    st =
      Enum.reduce(succ.(v), st, fn w, st ->
        cond do
          not Map.has_key?(st.indices, w) ->
            st = strong(w, succ, st)
            %{st | low: Map.put(st.low, v, min(st.low[v], st.low[w]))}

          MapSet.member?(st.on, w) ->
            %{st | low: Map.put(st.low, v, min(st.low[v], st.indices[w]))}

          true ->
            st
        end
      end)

    if st.low[v] == st.indices[v] do
      {component, rest} = pop_component(st.stack, v, [])

      %{
        st
        | stack: rest,
          on: Enum.reduce(component, st.on, &MapSet.delete(&2, &1)),
          result: [MapSet.new(component) | st.result]
      }
    else
      st
    end
  end

  defp pop_component([v | rest], v, acc), do: {[v | acc], rest}
  defp pop_component([w | rest], v, acc), do: pop_component(rest, v, [w | acc])

  # -- Fair components --

  defp fair_component(component, out, fair, accept, ae) do
    edges = for v <- component, {w, _} <- out.(v), MapSet.member?(component, w), do: {v, w}
    find_edge = fn test -> Enum.find(edges, fn {v, w} -> test.(v, w) end) end

    weak_test = fn c -> fn v, w -> not MapSet.member?(c.enabled, v) or c.taken.(v, w) end end

    cond do
      # A component without a step has no cycle.
      edges == [] ->
        nil

      Enum.any?(accept, &MapSet.disjoint?(&1, component)) ->
        nil

      Enum.any?(ae, &(find_edge.(&1) == nil)) ->
        nil

      Enum.any?(fair, &(&1.strength == :weak and find_edge.(weak_test.(&1)) == nil)) ->
        nil

      true ->
        open =
          Enum.find(fair, &(&1.strength == :strong and strong_open?(&1, component, find_edge)))

        case open do
          nil ->
            nodes = Enum.map(accept, &{:node, &1 |> MapSet.intersection(component) |> Enum.min()})
            steps = Enum.map(ae, &{:edge, find_edge.(&1)})

            fairness =
              Enum.flat_map(fair, fn c ->
                test = if c.strength == :weak, do: weak_test.(c), else: c.taken

                case find_edge.(test) do
                  nil -> []
                  edge -> [{:edge, edge}]
                end
              end)

            {component, Enum.uniq(nodes ++ steps ++ fairness)}

          c ->
            component
            |> MapSet.difference(c.enabled)
            |> sccs(out)
            |> Enum.find_value(&fair_component(&1, out, fair, accept, ae))
        end
    end
  end

  defp strong_open?(c, component, find_edge) do
    not MapSet.disjoint?(component, c.enabled) and find_edge.(c.taken) == nil
  end

  # -- The counterexample --

  defp lasso(product, component, plan, out) do
    inner = fn v -> Enum.filter(out.(v), fn {w, _} -> MapSet.member?(component, w) end) end

    entry = Enum.min(component)
    head = prefix(product, entry, [])
    cycle = cycle(entry, plan, inner)

    # The trace shows states, without the stuttering steps.
    head = project(product, head)

    case cycle
         |> Enum.map(fn {x, label} -> {state(product, x), label} end)
         |> Enum.reject(&(elem(&1, 1) == nil)) do
      [] ->
        %{steps: head, loop: :stuttering}

      real ->
        loop_index = length(head) - 1
        {body, [{_, label}]} = Enum.split(real, -1)
        %{steps: head ++ body, loop: {:back_to, loop_index, label}}
    end
  end

  # The path in the product from an initial node to `x`.
  defp prefix(product, x, acc) do
    case elem(product.parent, x) do
      nil -> [{x, nil} | acc]
      {p, label} -> prefix(product, p, [{x, label} | acc])
    end
  end

  # The states of a path in the product; a stuttering step goes out.
  defp project(product, [{x, _} | rest]) do
    [
      {state(product, x), nil}
      | for({y, label} <- rest, label != nil, do: {state(product, y), label})
    ]
  end

  # A walk from the entry node through each target and back: the steps
  # after the entry node; the last step comes back to it.
  defp cycle(entry, plan, inner) do
    {at, steps} =
      Enum.reduce(plan, {entry, []}, fn
        {:node, v}, {at, acc} ->
          {v, acc ++ path(at, v, inner)}

        {:edge, {v, w}}, {at, acc} ->
          {_, label} = Enum.find(inner.(v), fn {x, _} -> x == w end)
          {w, acc ++ path(at, v, inner) ++ [{w, label}]}
      end)

    steps = steps ++ path(at, entry, inner)

    # A cycle needs a step: when no target asks for one, take a step that
    # comes back to the entry node.
    if steps == [], do: loop_at(entry, inner), else: steps
  end

  defp loop_at(entry, inner) do
    case Enum.find(inner.(entry), fn {w, _} -> w == entry end) do
      {_, label} ->
        [{entry, label}]

      nil ->
        [{w, label} | _] = inner.(entry)
        [{w, label} | path(w, entry, inner)]
    end
  end

  # The shortest path of steps from `from` to `to` inside the component.
  defp path(v, v, _inner), do: []

  defp path(from, to, inner) do
    bfs(:queue.from_list([from]), to, inner, %{from => nil})
  end

  defp bfs(queue, to, inner, tree) do
    {{:value, v}, queue} = :queue.out(queue)

    if v == to do
      unwind(tree, to, [])
    else
      {queue, tree} =
        Enum.reduce(inner.(v), {queue, tree}, fn {w, label}, {q, t} ->
          if Map.has_key?(t, w), do: {q, t}, else: {:queue.in(w, q), Map.put(t, w, {v, label})}
        end)

      bfs(queue, to, inner, tree)
    end
  end

  defp unwind(tree, v, acc) do
    case Map.fetch!(tree, v) do
      nil -> acc
      {parent, label} -> unwind(tree, parent, [{v, label} | acc])
    end
  end
end
