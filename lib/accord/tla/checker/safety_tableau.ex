defmodule Accord.TLA.Checker.SafetyTableau do
  @moduledoc """
  The check of the safety part of temporal properties during the search,
  as TLC does it.

  TLC builds the product of the state graph and the tableau of a negated
  property while it explores the states. When a disjunct of the negated
  property has no fairness conditions (no `[]<>` or `<>[]` parts), a
  product node whose tableau successor is a sink (no literal and no
  obligation) ends a finite counterexample: the property is a safety
  property, and the run of the property is false. TLC reports this at
  once, as a safety violation, with the shortest path in the product to
  that node.

  The checker keeps the product for each such disjunct (with state
  literals only). `init/3` adds an initial state; `step/4` adds the steps
  of a state after its expansion. Both give `:ok` with the new product,
  or `{:violated, name, path}` with the state ids of the counterexample.
  """

  alias Accord.TLA.Checker.Temporal

  defstruct parts: []

  @doc """
  The products for the live properties `[{name, formula, atoms}]`.
  `literal` evaluates a state literal: `literal.(atom, state_id)`.
  """
  def new(live, fairness) do
    parts =
      if fairness != [] do
        []
      else
        for {name, formula, atoms} <- live,
            disjunct <- Temporal.dnf(formula),
            parts = Temporal.split(disjunct),
            parts.ae == [] and parts.ea == [] and parts.rest != true,
            tableau = Temporal.tableau(parts.rest),
            state_only?(tableau, atoms) do
          %{
            name: name,
            atoms: atoms,
            tableau: tableau,
            reached: MapSet.new(),
            adj: %{},
            inits: [],
            done: MapSet.new()
          }
        end
      end

    %__MODULE__{parts: parts}
  end

  @doc "Tells if there is a product to keep."
  def active?(%__MODULE__{parts: parts}), do: parts != []

  defp state_only?(tableau, atoms) do
    Enum.all?(tableau.nodes, fn {_, n} ->
      Enum.all?(n.lits, fn {id, _} -> match?({:state, _}, Map.fetch!(atoms, id)) end)
    end)
  end

  @doc "Adds the initial state `s`."
  def init(%__MODULE__{} = st, s, literal) do
    parts =
      Enum.map(st.parts, fn p ->
        Enum.reduce(p.tableau.init, p, fn t, p ->
          if consistent?(p, t, s, literal) and not MapSet.member?(p.reached, {s, t}),
            do: %{p | reached: MapSet.put(p.reached, {s, t}), inits: p.inits ++ [{s, t}]},
            else: p
        end)
      end)

    {:ok, %{st | parts: parts}}
  end

  @doc """
  Adds the steps of the state `s0` (just expanded): `succs.(s)` gives the
  successors of a state (with the stuttering step).
  """
  def step(%__MODULE__{} = st, s0, succs, literal) do
    Enum.reduce_while(Enum.with_index(st.parts), {:ok, st}, fn {p, i}, {:ok, st} ->
      p = %{p | done: MapSet.put(p.done, s0)}

      result =
        catch_violation(fn ->
          nodes0 = for {^s0, t} <- MapSet.to_list(p.reached), do: t

          Enum.reduce(Enum.sort(nodes0), p, fn t0, p ->
            Enum.reduce(succs.(s0), p, fn s1, p ->
              Enum.reduce(succ(p, t0), p, fn t1, p ->
                visit(p, {s0, t0}, {s1, t1}, succs, literal)
              end)
            end)
          end)
        end)

      case result do
        {:ok, p} -> {:cont, {:ok, %{st | parts: List.replace_at(st.parts, i, p)}}}
        {:violated, p, node} -> {:halt, {:violated, p.name, path(p, node)}}
      end
    end)
  end

  defp catch_violation(fun) do
    {:ok, fun.()}
  catch
    {:safety_violation, p, node} -> {:violated, p, node}
  end

  # The edge from `from` to `{s1, t1}` when s1 is consistent with t1. A
  # new node of a state that is done goes on at once (TLC's addNextState
  # for a done state).
  defp visit(p, from, {s1, t1} = to, succs, literal) do
    if consistent?(p, t1, s1, literal) do
      p = %{p | adj: Map.update(p.adj, from, [to], &(&1 ++ [to]))}

      if MapSet.member?(p.reached, to) do
        p
      else
        p = %{p | reached: MapSet.put(p.reached, to)}
        if MapSet.member?(p.done, s1), do: done(p, to, succs, literal), else: p
      end
    else
      p
    end
  end

  defp done(p, {s, t} = node, succs, literal) do
    # The self-loop s -> s: a sink ends a counterexample.
    p =
      Enum.reduce(succ(p, t), p, fn t1, p ->
        if consistent?(p, t1, s, literal) do
          if p.tableau.nodes |> Map.fetch!(t1) |> Map.get(:sink, false),
            do: throw({:safety_violation, p, node})

          visit(p, node, {s, t1}, succs, literal)
        else
          p
        end
      end)

    Enum.reduce(succs.(s), p, fn s1, p ->
      if s1 == s do
        p
      else
        Enum.reduce(succ(p, t), p, fn t1, p -> visit(p, node, {s1, t1}, succs, literal) end)
      end
    end)
  end

  defp succ(p, t), do: p.tableau.nodes |> Map.fetch!(t) |> Map.fetch!(:succ)

  defp consistent?(p, t, s, literal) do
    p.tableau.nodes
    |> Map.fetch!(t)
    |> Map.fetch!(:lits)
    |> Enum.all?(fn {id, pol} -> literal.(Map.fetch!(p.atoms, id), s) == pol end)
  end

  # The shortest path in the product from an initial node to `target`, as
  # state ids, without stuttering steps.
  defp path(p, target) do
    if target in p.inits do
      [elem(target, 0)]
    else
      queue = :queue.from_list(p.inits)
      parents = Map.new(p.inits, &{&1, nil})
      p |> bfs(queue, parents, target) |> Enum.map(&elem(&1, 0)) |> Enum.dedup()
    end
  end

  defp bfs(p, queue, parents, target) do
    case :queue.out(queue) do
      {:empty, _} ->
        []

      {{:value, node}, queue} ->
        nexts = p.adj |> Map.get(node, []) |> Enum.reject(&(&1 == node))

        Enum.reduce_while(nexts, {queue, parents}, fn n, {q, par} ->
          cond do
            n == target -> {:halt, {:found, Map.put(par, n, node)}}
            Map.has_key?(par, n) -> {:cont, {q, par}}
            true -> {:cont, {:queue.in(n, q), Map.put(par, n, node)}}
          end
        end)
        |> case do
          {:found, par} -> unwind(par, target, [])
          {q, par} -> bfs(p, q, par, target)
        end
    end
  end

  defp unwind(_par, nil, acc), do: acc
  defp unwind(par, node, acc), do: unwind(par, Map.fetch!(par, node), [node | acc])
end
