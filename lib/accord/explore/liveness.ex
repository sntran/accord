defmodule Accord.Explore.Liveness do
  @moduledoc """
  Checks the liveness properties of a model: `trigger ~> target` for each
  session, under the fairness of the property.

  The check uses the semantics of the TLA+ spec that Accord makes:

      Name == (Fairness) => \\A s \\in Sessions : (state[s] = trigger ~> state[s] = target)

  A behavior is an infinite sequence of states. It can repeat a state
  forever (stuttering). A fairness condition is about steps that change
  the state:

  - Weak fairness on an action: if the action can change the state in
    every state from some point on, it changes the state infinitely often.
  - Strong fairness on an action: if the action can change the state
    infinitely often, it changes the state infinitely often.

  The property is violated when a fair behavior reaches a state where the
  trigger holds and the target does not, and after that the target never
  holds. On a finite graph, such a behavior ends in one of two ways:

  - it stays forever in one state where no fair action can change the
    state, or
  - it goes around a strongly connected set of states forever, and the
    set satisfies each fairness condition.

  The check finds these ends with Tarjan's algorithm. For strong
  fairness, it removes the states where the action can run and searches
  the rest again (the Emerson-Lei method).

  As TLC does, the check uses only the states inside the state
  constraint. A step to a state outside the constraint is not part of a
  behavior, but it still makes its action enabled.
  """

  alias Accord.Explore.Model

  @typedoc """
  A liveness counterexample: a lasso. `trace` is the path from the
  initial state. `loop` is `:stutter` (the behavior stays in the last
  state forever) or `%{to: index, label: label}` (a step from the last
  state goes back to the state at `index`, 1-based, and the behavior
  repeats from there).
  """
  @type lasso :: %{trace: [map()], loop: :stutter | %{to: pos_integer(), label: map()}}

  @doc """
  Checks one liveness property.

  `seen` is the map of the explorer: state to `{parent, label, depth}`.
  Gives `nil` when the property holds, or a lasso.
  """
  @spec check(Model.t(), map(), Model.liveness()) :: lasso() | nil
  def check(%Model{} = model, seen, check) do
    graph = build_graph(model, seen)

    Enum.find_value(1..model.sessions, fn session ->
      check_session(graph, seen, check, session)
    end)
  end

  # -- Graph --

  # Gives the states by id, the real steps (the ones that change the
  # state) inside the constraint, and the actions that can change each
  # state (also by a step out of the constraint).
  defp build_graph(model, seen) do
    states = seen |> Map.keys() |> Enum.sort_by(&elem(Map.fetch!(seen, &1), 2))
    ids = states |> Enum.with_index() |> Map.new()
    by_id = List.to_tuple(states)

    {edges, enabled} =
      states
      |> Enum.map(fn state ->
        real =
          for {label, next} <- Model.successors(model, state), next != state, do: {label, next}

        edges =
          for {label, next} <- real, id = Map.get(ids, next), id != nil, do: {id, label}

        {edges, MapSet.new(real, fn {label, _} -> label.action end)}
      end)
      |> Enum.unzip()

    %{
      states: by_id,
      ids: ids,
      edges: List.to_tuple(edges),
      enabled: List.to_tuple(enabled),
      size: length(states)
    }
  end

  defp enabled?(graph, v, :next), do: MapSet.size(elem(graph.enabled, v)) > 0
  defp enabled?(graph, v, key), do: MapSet.member?(elem(graph.enabled, v), key)

  defp matches?(_label, :next), do: true
  defp matches?(label, key), do: label.action == key

  defp session_state(graph, v, session) do
    {sessions, _shared} = elem(graph.states, v)
    sessions |> elem(session - 1) |> elem(0)
  end

  # -- One session --

  defp check_session(graph, seen, check, session) do
    if check.trigger == check.target do
      nil
    else
      in_h = fn v -> session_state(graph, v, session) != check.target end
      h = for v <- 0..(graph.size - 1)//1, in_h.(v), into: MapSet.new(), do: v

      stutter = for v <- h, fair_stutter?(graph, v, check.fairness), into: MapSet.new(), do: v
      cycles = fair_components(graph, h, check.fairness)
      goal = Enum.reduce(cycles, stutter, &MapSet.union(MapSet.new(&1), &2))
      reach = backward(graph, h, goal)

      start =
        reach
        |> Enum.filter(&(session_state(graph, &1, session) == check.trigger))
        |> Enum.min_by(&depth(graph, seen, &1), fn -> nil end)

      if start, do: lasso(graph, seen, h, start, stutter, cycles, check.fairness)
    end
  end

  defp depth(graph, seen, v), do: seen |> Map.fetch!(elem(graph.states, v)) |> elem(2)

  # The behavior can stay in `v` forever if no fair action can change it.
  defp fair_stutter?(graph, v, fairness) do
    Enum.all?(fairness, fn {_strength, key} -> not enabled?(graph, v, key) end)
  end

  # -- Fair strongly connected sets --

  defp fair_components(graph, set, fairness) do
    graph
    |> sccs(set)
    |> Enum.flat_map(&fair_subsets(graph, &1, fairness))
  end

  # A set is fair when it has a real step inside it and each fairness
  # condition holds for a behavior that visits all its states and takes
  # all its steps. A weak condition that fails cannot hold on a subset. A
  # strong condition that fails can hold on the states where its action
  # is not enabled.
  defp fair_subsets(graph, component, fairness) do
    set = MapSet.new(component)
    inner = inner_edges(graph, set)

    if inner == [] do
      []
    else
      failing =
        Enum.reject(fairness, fn {strength, key} ->
          taken = Enum.any?(inner, fn {_v, _w, label} -> matches?(label, key) end)

          case strength do
            :weak -> taken or Enum.any?(set, &(not enabled?(graph, &1, key)))
            :strong -> taken or Enum.all?(set, &(not enabled?(graph, &1, key)))
          end
        end)

      cond do
        failing == [] ->
          [component]

        Enum.any?(failing, &match?({:weak, _}, &1)) ->
          []

        true ->
          keys = Enum.map(failing, &elem(&1, 1))

          rest =
            for v <- set, not Enum.any?(keys, &enabled?(graph, v, &1)), into: MapSet.new(), do: v

          fair_components(graph, rest, fairness)
      end
    end
  end

  defp inner_edges(graph, set) do
    for v <- set, {w, label} <- elem(graph.edges, v), MapSet.member?(set, w), do: {v, w, label}
  end

  # Tarjan's algorithm on the subgraph of `set`, without recursion.
  defp sccs(graph, set) do
    init = %{index: %{}, low: %{}, stack: [], on_stack: MapSet.new(), next: 0, result: []}

    set
    |> Enum.sort()
    |> Enum.reduce(init, fn v, st ->
      if Map.has_key?(st.index, v), do: st, else: strongconnect(graph, set, v, st)
    end)
    |> Map.fetch!(:result)
  end

  defp strongconnect(graph, set, root, st) do
    st = visit(st, root)
    work = [{root, successors_in(graph, set, root)}]
    tarjan_loop(graph, set, work, st)
  end

  defp tarjan_loop(_graph, _set, [], st), do: st

  defp tarjan_loop(graph, set, [{v, [w | rest]} | frames], st) do
    frames = [{v, rest} | frames]

    cond do
      not Map.has_key?(st.index, w) ->
        st = visit(st, w)
        tarjan_loop(graph, set, [{w, successors_in(graph, set, w)} | frames], st)

      MapSet.member?(st.on_stack, w) ->
        st = %{st | low: Map.update!(st.low, v, &min(&1, Map.fetch!(st.index, w)))}
        tarjan_loop(graph, set, frames, st)

      true ->
        tarjan_loop(graph, set, frames, st)
    end
  end

  defp tarjan_loop(graph, set, [{v, []} | frames], st) do
    st =
      if Map.fetch!(st.low, v) == Map.fetch!(st.index, v) do
        {component, stack} = pop_component(st.stack, v, [])
        on_stack = Enum.reduce(component, st.on_stack, &MapSet.delete(&2, &1))
        %{st | stack: stack, on_stack: on_stack, result: [component | st.result]}
      else
        st
      end

    st =
      case frames do
        [{parent, _} | _] ->
          %{st | low: Map.update!(st.low, parent, &min(&1, Map.fetch!(st.low, v)))}

        [] ->
          st
      end

    tarjan_loop(graph, set, frames, st)
  end

  defp visit(st, v) do
    %{
      st
      | index: Map.put(st.index, v, st.next),
        low: Map.put(st.low, v, st.next),
        next: st.next + 1,
        stack: [v | st.stack],
        on_stack: MapSet.put(st.on_stack, v)
    }
  end

  defp pop_component([v | rest], v, acc), do: {[v | acc], rest}
  defp pop_component([w | rest], v, acc), do: pop_component(rest, v, [w | acc])

  defp successors_in(graph, set, v) do
    for {w, _label} <- elem(graph.edges, v), MapSet.member?(set, w), uniq: true, do: w
  end

  # The states of `set` that can reach `goal` by steps inside `set`.
  defp backward(graph, set, goal) do
    preds =
      Enum.reduce(set, %{}, fn v, acc ->
        Enum.reduce(elem(graph.edges, v), acc, fn {w, _}, acc ->
          if MapSet.member?(set, w), do: Map.update(acc, w, [v], &[v | &1]), else: acc
        end)
      end)

    grow(MapSet.to_list(goal), goal, preds)
  end

  defp grow([], reached, _preds), do: reached

  defp grow([v | rest], reached, preds) do
    new = preds |> Map.get(v, []) |> Enum.reject(&MapSet.member?(reached, &1))
    grow(new ++ rest, Enum.reduce(new, reached, &MapSet.put(&2, &1)), preds)
  end

  # -- Counterexample --

  defp lasso(graph, seen, h, start, stutter, cycles, fairness) do
    prefix = prefix(graph, seen, start)
    goal = Enum.reduce(cycles, stutter, &MapSet.union(MapSet.new(&1), &2))
    {path, end_state} = shortest_path(graph, h, start, &MapSet.member?(goal, &1))
    trace = prefix ++ path

    if MapSet.member?(stutter, end_state) do
      %{trace: trace, loop: :stutter}
    else
      component = Enum.find(cycles, &(end_state in &1))
      {loop_steps, return_label} = cycle(graph, MapSet.new(component), end_state, fairness)
      %{trace: trace ++ loop_steps, loop: %{to: length(trace), label: return_label}}
    end
  end

  defp prefix(graph, seen, v) do
    build_prefix(seen, elem(graph.states, v), [])
  end

  defp build_prefix(_seen, nil, steps), do: steps

  defp build_prefix(seen, state, steps) do
    {parent, label, _depth} = Map.fetch!(seen, state)
    build_prefix(seen, parent, [%{state: state, label: label} | steps])
  end

  # A shortest path inside `set` from `from` to a state where `goal?`
  # holds. Gives the steps after `from`, and the last state.
  defp shortest_path(graph, set, from, goal?) do
    if goal?.(from) do
      {[], from}
    else
      bfs(graph, set, :queue.from_list([from]), %{from => nil}, goal?)
    end
  end

  defp bfs(graph, set, queue, parents, goal?) do
    {{:value, v}, queue} = :queue.out(queue)

    {queue, parents, found} =
      Enum.reduce_while(elem(graph.edges, v), {queue, parents, nil}, fn {w, label}, {q, p, _} ->
        cond do
          not MapSet.member?(set, w) or Map.has_key?(p, w) -> {:cont, {q, p, nil}}
          goal?.(w) -> {:halt, {q, Map.put(p, w, {v, label}), w}}
          true -> {:cont, {:queue.in(w, q), Map.put(p, w, {v, label}), nil}}
        end
      end)

    if found do
      {path_to(graph, parents, found, []), found}
    else
      bfs(graph, set, queue, parents, goal?)
    end
  end

  defp path_to(_graph, parents, v, steps) when :erlang.map_get(v, parents) == nil, do: steps

  defp path_to(graph, parents, v, steps) do
    {u, label} = Map.fetch!(parents, v)
    path_to(graph, parents, u, [%{state: elem(graph.states, v), label: label} | steps])
  end

  # A closed walk in a fair set from `start`: it visits every state of
  # the set and takes one step of each fair action that has a step in the
  # set. Gives the steps after `start` except the last one, and the label
  # of the last step (back to `start`).
  defp cycle(graph, set, start, fairness) do
    inner = inner_edges(graph, set)

    required =
      fairness
      |> Enum.flat_map(fn {_strength, key} ->
        case Enum.find(inner, fn {_v, _w, label} -> matches?(label, key) end) do
          nil -> []
          edge -> [edge]
        end
      end)
      |> Enum.uniq()

    {steps, current} =
      Enum.reduce(required, {[], start}, fn {v, w, label}, {steps, current} ->
        {to_v, _} = shortest_path(graph, set, current, &(&1 == v))
        {steps ++ to_v ++ [%{state: elem(graph.states, w), label: label}], w}
      end)

    visited = MapSet.new([start | Enum.map(steps, &Map.fetch!(graph.ids, &1.state))])

    {steps, current} =
      set
      |> Enum.sort()
      |> Enum.reduce({steps, current}, fn s, {steps, current} ->
        if MapSet.member?(visited, s) or Enum.any?(steps, &(Map.fetch!(graph.ids, &1.state) == s)) do
          {steps, current}
        else
          {to_s, _} = shortest_path(graph, set, current, &(&1 == s))
          {steps ++ to_s, s}
        end
      end)

    # Back to the start. A walk that is already at the start ends with
    # its last step, which goes to the start.
    back =
      if current == start and steps != [] do
        []
      else
        {to_start, _} = shortest_path_nonempty(graph, set, current, start)
        to_start
      end

    all = steps ++ back
    {Enum.drop(all, -1), List.last(all).label}
  end

  # A shortest path with at least one step (also from a state to itself).
  defp shortest_path_nonempty(graph, set, from, to) do
    if from == to do
      [{w, label} | _] = for {w, l} <- elem(graph.edges, from), MapSet.member?(set, w), do: {w, l}
      {rest, _} = shortest_path(graph, set, w, &(&1 == to))
      {[%{state: elem(graph.states, w), label: label} | rest], to}
    else
      shortest_path(graph, set, from, &(&1 == to))
    end
  end
end
