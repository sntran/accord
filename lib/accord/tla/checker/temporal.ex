defmodule Accord.TLA.Checker.Temporal do
  @moduledoc """
  Temporal formulas for the liveness check.

  A formula is in negation normal form:

  - `true`, `false`
  - `{:lit, id, polarity}` — an atom (a state predicate or an action) or
    its negation. `id` refers to a table of atoms.
  - `{:and, [f]}`, `{:or, [f]}`
  - `{:always, f}`, `{:eventually, f}`

  `dnf/1` splits a formula into disjuncts. `split/1` takes the simple
  parts of a disjunct: `[]<>p` and `<>[]p` with `p` not temporal. The
  other parts go to a tableau: `tableau/1` gives a generalized Büchi
  automaton (the method of Gerth, Peled, Vardi and Wolper).
  """

  @doc "Tells if a formula has a temporal operator."
  def temporal?({kind, _}) when kind in [:always, :eventually], do: true
  def temporal?({kind, items}) when kind in [:and, :or], do: Enum.any?(items, &temporal?/1)
  def temporal?(_), do: false

  @doc "The negation of a formula, in negation normal form."
  def negate(true), do: false
  def negate(false), do: true
  def negate({:lit, id, pol}), do: {:lit, id, not pol}
  def negate({:atom, kind, c, pol}), do: {:atom, kind, c, not pol}
  def negate({:and, items}), do: {:or, Enum.map(items, &negate/1)}
  def negate({:or, items}), do: {:and, Enum.map(items, &negate/1)}
  def negate({:always, f}), do: {:eventually, negate(f)}
  def negate({:eventually, f}), do: {:always, negate(f)}

  @doc "Makes `{:and, ...}` and `{:or, ...}` flat and removes constants."
  def simplify({:and, items}) do
    items =
      items
      |> Enum.map(&simplify/1)
      |> Enum.flat_map(fn
        {:and, i} -> i
        f -> [f]
      end)
      |> Enum.uniq()

    cond do
      false in items -> false
      true -> items |> Enum.reject(&(&1 == true)) |> wrap(:and, true)
    end
  end

  def simplify({:or, items}) do
    items =
      items
      |> Enum.map(&simplify/1)
      |> Enum.flat_map(fn
        {:or, i} -> i
        f -> [f]
      end)
      |> Enum.uniq()

    cond do
      true in items -> true
      true -> items |> Enum.reject(&(&1 == false)) |> wrap(:or, false)
    end
  end

  def simplify({:always, f}) do
    case simplify(f) do
      b when is_boolean(b) -> b
      {:always, _} = g -> g
      g -> {:always, g}
    end
  end

  def simplify({:eventually, f}) do
    case simplify(f) do
      b when is_boolean(b) -> b
      {:eventually, _} = g -> g
      g -> {:eventually, g}
    end
  end

  def simplify(f), do: f

  defp wrap([], _kind, empty), do: empty
  defp wrap([one], _kind, _empty), do: one
  defp wrap(items, kind, _empty), do: {kind, items}

  @doc "The disjuncts of a formula, each a list of conjuncts."
  def dnf({:or, items}), do: Enum.flat_map(items, &dnf/1)

  def dnf({:and, items}) do
    Enum.reduce(items, [[]], fn item, acc ->
      for conj <- acc, d <- dnf(item), do: conj ++ d
    end)
  end

  def dnf(true), do: [[]]
  def dnf(false), do: []
  def dnf(f), do: [[f]]

  @doc """
  Splits the conjuncts of a disjunct: `%{ae: [p], ea: [p], rest: f}` for
  `[]<>p`, `<>[]p`, and the conjunction of the other parts (or `true`).
  """
  def split(conjuncts) do
    {ae, ea, rest} =
      Enum.reduce(conjuncts, {[], [], []}, fn
        {:always, {:eventually, p}}, {ae, ea, rest} ->
          if temporal?(p),
            do: {ae, ea, [{:always, {:eventually, p}} | rest]},
            else: {[p | ae], ea, rest}

        {:eventually, {:always, p}}, {ae, ea, rest} ->
          if temporal?(p),
            do: {ae, ea, [{:eventually, {:always, p}} | rest]},
            else: {ae, [p | ea], rest}

        f, {ae, ea, rest} ->
          {ae, ea, [f | rest]}
      end)

    %{ae: Enum.reverse(ae), ea: Enum.reverse(ea), rest: simplify({:and, Enum.reverse(rest)})}
  end

  @doc "The atom ids of a formula."
  def atoms({:lit, id, _}), do: [id]
  def atoms({kind, items}) when kind in [:and, :or], do: Enum.flat_map(items, &atoms/1)
  def atoms({_, f}), do: atoms(f)
  def atoms(_), do: []

  # -- Tableau --

  @doc """
  The tableau of a formula: a generalized Büchi automaton.

  Gives `%{nodes: %{name => %{lits: [{id, polarity}], succ: [name]}},
  init: [name], accept: [MapSet]}`. The literals of a node must hold at
  the position of the node (an action literal holds on the step from the
  position).
  """
  def tableau(f) do
    f = ur(f)

    start = %{
      name: 0,
      incoming: MapSet.new([:init]),
      new: [f],
      old: MapSet.new(),
      next: MapSet.new()
    }

    {nodes, _} = expand(start, %{}, 1)

    succ =
      Enum.reduce(nodes, %{}, fn {name, node}, acc ->
        Enum.reduce(node.incoming, acc, fn
          :init, acc -> acc
          from, acc -> Map.update(acc, from, [name], &[name | &1])
        end)
      end)

    graph =
      Map.new(nodes, fn {name, node} ->
        lits = for {:lit, id, pol} <- node.old, do: {id, pol}
        {name, %{lits: Enum.sort(lits), succ: succ |> Map.get(name, []) |> Enum.sort()}}
      end)

    init = for {name, node} <- nodes, MapSet.member?(node.incoming, :init), do: name

    accept =
      for {:until, _a, b} = u <- subformulas(f) |> Enum.uniq() do
        for {name, node} <- nodes,
            not MapSet.member?(node.old, u) or MapSet.member?(node.old, b),
            into: MapSet.new(),
            do: name
      end

    %{nodes: graph, init: Enum.sort(init), accept: accept}
  end

  # `[]f` is `false R f`; `<>f` is `true U f`.
  defp ur({:always, f}), do: {:release, false, ur(f)}
  defp ur({:eventually, f}), do: {:until, true, ur(f)}
  defp ur({kind, items}) when kind in [:and, :or], do: {kind, Enum.map(items, &ur/1)}
  defp ur(f), do: f

  defp subformulas({kind, a, b} = f) when kind in [:until, :release],
    do: [f | subformulas(a) ++ subformulas(b)]

  defp subformulas({kind, items} = f) when kind in [:and, :or],
    do: [f | Enum.flat_map(items, &subformulas/1)]

  defp subformulas(f), do: [f]

  defp expand(%{new: []} = node, nodes, counter) do
    case Enum.find(nodes, fn {_, nd} -> nd.old == node.old and nd.next == node.next end) do
      {name, nd} ->
        {Map.put(nodes, name, %{nd | incoming: MapSet.union(nd.incoming, node.incoming)}),
         counter}

      nil ->
        nodes = Map.put(nodes, node.name, node)

        fresh = %{
          name: counter,
          incoming: MapSet.new([node.name]),
          new: MapSet.to_list(node.next),
          old: MapSet.new(),
          next: MapSet.new()
        }

        expand(fresh, nodes, counter + 1)
    end
  end

  defp expand(%{new: [eta | rest]} = node, nodes, counter) do
    node = %{node | new: rest}

    cond do
      MapSet.member?(node.old, eta) ->
        expand(node, nodes, counter)

      literal?(eta) ->
        if eta == false or MapSet.member?(node.old, contra(eta)),
          do: {nodes, counter},
          else: expand(%{node | old: MapSet.put(node.old, eta)}, nodes, counter)

      true ->
        old = MapSet.put(node.old, eta)

        case eta do
          {:and, items} ->
            expand(%{node | new: add_new(node.new, items, old), old: old}, nodes, counter)

          {:or, items} ->
            Enum.reduce(items, {nodes, counter}, fn item, {nodes, counter} ->
              branch = %{node | name: counter, new: add_new(node.new, [item], old), old: old}
              expand(branch, nodes, counter + 1)
            end)

          {:until, a, b} ->
            n1 = %{
              node
              | name: counter,
                new: add_new(node.new, [a], old),
                old: old,
                next: MapSet.put(node.next, eta)
            }

            n2 = %{node | name: counter + 1, new: add_new(node.new, [b], old), old: old}
            {nodes, counter} = expand(n1, nodes, counter + 2)
            expand(n2, nodes, counter)

          {:release, a, b} ->
            n1 = %{
              node
              | name: counter,
                new: add_new(node.new, [b], old),
                old: old,
                next: MapSet.put(node.next, eta)
            }

            n2 = %{node | name: counter + 1, new: add_new(node.new, [a, b], old), old: old}
            {nodes, counter} = expand(n1, nodes, counter + 2)
            expand(n2, nodes, counter)
        end
    end
  end

  defp add_new(new, items, old),
    do: new ++ Enum.reject(items, &(MapSet.member?(old, &1) or &1 in new))

  defp literal?(f), do: is_boolean(f) or match?({:lit, _, _}, f)

  defp contra({:lit, id, pol}), do: {:lit, id, not pol}
  defp contra(true), do: false
  defp contra(false), do: true
end
