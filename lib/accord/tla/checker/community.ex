defmodule Accord.TLA.Checker.Community do
  @moduledoc """
  Native versions of some operators of the TLA+ community modules.

  TLC replaces these operators with Java code (the overrides of the
  community modules). Some of their TLA+ definitions cannot be evaluated
  (they use `Seq(S)` or an unbounded `CHOOSE`), and some are slow. The
  checker reads the module from its `.tla` file and replaces the
  operators of this table with native code, as TLC does.

  The order of the folds is the order of TLC: the elements of a set in
  the order of `Accord.TLA.Checker.Value.sort/1`.
  """

  alias Accord.TLA.Checker.{Eval, Value}
  import Value, only: [error: 1]

  # Module => operator => arities of the parameters.
  @ops %{
    "UndirectedGraphs" => %{
      "ConnectedComponents" => [0],
      "AreConnectedIn" => [0, 0, 0],
      "SimplePath" => [0]
    },
    "Graphs" => %{
      "AreConnectedIn" => [0, 0, 0],
      "IsStronglyConnected" => [0],
      "SimplePath" => [0]
    },
    "FiniteSetsExt" => %{"FoldSet" => [2, 0, 0], "Quantify" => [0, 1], "kSubset" => [0, 0]},
    "Functions" => %{
      "FoldFunction" => [2, 0, 0],
      "FoldFunctionOnSet" => [2, 0, 0, 0],
      "IsInjective" => [0],
      "AntiFunction" => [0]
    },
    "SequencesExt" => %{
      "FoldLeft" => [2, 0, 0],
      "FoldRight" => [2, 0, 0],
      "FoldSeq" => [2, 0, 0],
      "FoldLeftDomain" => [2, 0, 0],
      "FoldRightDomain" => [2, 0, 0],
      "SetToSeq" => [0],
      "SetToSeqs" => [0]
    },
    "BagsExt" => %{"FoldBag" => [2, 0, 0]},
    "Bitwise" => %{
      "And" => [0, 0, 0, 0],
      "Or" => [0, 0, 0, 0],
      "Xor" => [0, 0, 0, 0],
      "Not" => [0],
      "shiftR" => [0, 0]
    },
    "Combinatorics" => %{"factorial" => [0], "choose" => [0, 0]},
    "Json" => %{
      "ToJson" => [0],
      "ToJsonArray" => [0],
      "ToJsonObject" => [0],
      "JsonSerialize" => [0, 0],
      "JsonDeserialize" => [0],
      "ndJsonSerialize" => [0, 0],
      "ndJsonDeserialize" => [0]
    },
    "IOUtils" => %{
      "IOEnv" => [],
      "atoi" => [0],
      "IODeserialize" => [0, 0],
      "IOSerialize" => [0, 0, 0]
    }
  }

  @doc "The native operators of a module, as `%{name => arities}`."
  def ops(module), do: Map.get(@ops, module, %{})

  @doc "Tells if a module has native operators."
  def module?(module), do: Map.has_key?(@ops, module)

  @doc "The arities of the parameters of a native operator."
  def op_params(module, op), do: @ops |> Map.get(module, %{}) |> Map.get(op)

  @doc "Calls a native operator."
  def call(module, op, args, env), do: op(module, op, args, env)

  # -- Graphs --

  defp op("UndirectedGraphs", "ConnectedComponents", [g], _env) do
    {nodes, edges} = graph(g)

    parent =
      Enum.reduce(edges, Map.new(nodes, &{&1, &1}), fn e, parent ->
        case pair(e) do
          {a, b} -> if node?(a, nodes) and node?(b, nodes), do: union(parent, a, b), else: parent
          nil -> parent
        end
      end)

    nodes
    |> Enum.group_by(&find(parent, &1))
    |> Map.values()
    |> Enum.map(&Value.set/1)
    |> Value.set()
  end

  defp op("UndirectedGraphs", "AreConnectedIn", [m, n, g], _env),
    do: connected?(m, n, g, &pair/1, :symmetric)

  defp op("Graphs", "AreConnectedIn", [m, n, g], _env),
    do: connected?(m, n, g, &tuple_pair/1, :forward)

  defp op("UndirectedGraphs", "SimplePath", [g], _env), do: simple_paths(g, &pair/1, :symmetric)
  defp op("Graphs", "SimplePath", [g], _env), do: simple_paths(g, &tuple_pair/1, :forward)

  defp op("Graphs", "IsStronglyConnected", [g], _env) do
    {nodes, _} = graph(g)

    case Value.sort(nodes) do
      [] ->
        true

      [root | _] ->
        n = length(nodes)

        MapSet.size(reachable(root, adjacency(g, &tuple_pair/1, :forward))) == n and
          MapSet.size(reachable(root, adjacency(g, &tuple_pair/1, :transpose))) == n
    end
  end

  # -- Folds --

  defp op("FiniteSetsExt", "FoldSet", [opv, base, set], env),
    do:
      set |> Value.enum() |> Value.sort() |> Enum.reduce(base, &Eval.apply_op(opv, [&1, &2], env))

  defp op("FiniteSetsExt", "Quantify", [set, test], env),
    do: set |> Value.enum() |> Enum.count(&(Eval.apply_op(test, [&1], env) == true))

  # A lazy set, as TLC's KSubsetValue (see Value).
  defp op("FiniteSetsExt", "kSubset", [k, set], _env) do
    unless is_integer(k),
      do:
        error(
          "The first argument of kSubset should be an integer, but instead it is:\n#{Value.show(k)}"
        )

    unless Value.set?(set),
      do:
        error(
          "The second argument of kSubset should be a set, but instead it is:\n#{Value.show(set)}"
        )

    {:ksubset, k, set}
  end

  defp op("Functions", "FoldFunction", [opv, base, f], env),
    do: fold_function(opv, base, f, Value.domain(f), env)

  defp op("Functions", "FoldFunctionOnSet", [opv, base, f, set], env),
    do: fold_function(opv, base, f, set, env)

  defp op("Functions", "IsInjective", [f], _env) do
    values = f |> Value.pairs() |> Enum.map(&elem(&1, 1))
    length(Enum.uniq(values)) == length(values)
  end

  defp op("Functions", "AntiFunction", [f], _env) do
    f |> Value.pairs() |> Map.new(fn {k, v} -> {v, k} end) |> Value.fun()
  end

  defp op("SequencesExt", "FoldSeq", [opv, base, s], env),
    do: fold_function(opv, base, s, Value.domain(s), env)

  defp op("SequencesExt", "FoldLeft", [opv, base, s], env),
    do: s |> Value.seq_list() |> Enum.reduce(base, &Eval.apply_op(opv, [&2, &1], env))

  defp op("SequencesExt", "FoldRight", [opv, s, base], env),
    do:
      s
      |> Value.seq_list()
      |> Enum.reverse()
      |> Enum.reduce(base, &Eval.apply_op(opv, [&1, &2], env))

  defp op("SequencesExt", "FoldLeftDomain", [opv, base, s], env),
    do:
      s
      |> Value.seq_list()
      |> Enum.with_index(1)
      |> Enum.reduce(base, fn {_, i}, acc -> Eval.apply_op(opv, [acc, i], env) end)

  defp op("SequencesExt", "FoldRightDomain", [opv, s, base], env),
    do:
      s
      |> Value.seq_list()
      |> Enum.with_index(1)
      |> Enum.reverse()
      |> Enum.reduce(base, fn {_, i}, acc -> Eval.apply_op(opv, [i, acc], env) end)

  defp op("SequencesExt", "SetToSeq", [set], _env),
    do: set |> Value.enum() |> Value.sort() |> Value.tuple()

  defp op("SequencesExt", "SetToSeqs", [set], _env),
    do:
      set
      |> Value.enum()
      |> Value.sort()
      |> permutations()
      |> Enum.map(&Value.tuple/1)
      |> MapSet.new()

  defp op("BagsExt", "FoldBag", [opv, base, bag], env) do
    bag
    |> Value.pairs()
    |> Enum.sort_by(&elem(&1, 0), &(Value.compare(&1, &2) != :gt))
    |> Enum.reduce(base, fn {e, n}, acc ->
      Enum.reduce(1..n//1, acc, fn _, a -> Eval.apply_op(opv, [e, a], env) end)
    end)
  end

  # -- Bitwise and Combinatorics --

  defp op("Bitwise", "And", [x, y | _], _env), do: Bitwise.band(int(x), int(y))
  defp op("Bitwise", "Or", [x, y | _], _env), do: Bitwise.bor(int(x), int(y))
  defp op("Bitwise", "Xor", [x, y | _], _env), do: Bitwise.bxor(int(x), int(y))

  defp op("Bitwise", "Not", [x], _env) do
    x = int(x)
    bits = if x == 0, do: 1, else: length(Integer.digits(x, 2))
    Bitwise.band(Bitwise.bnot(x), Bitwise.bsl(1, bits) - 1)
  end

  defp op("Bitwise", "shiftR", [n, pos], _env), do: Bitwise.bsr(int(n), int(pos))

  defp op("Combinatorics", "factorial", [n], _env) do
    n = int(n)
    if n < 0, do: error("factorial needs a natural number")
    Enum.reduce(1..n//1, 1, &(&1 * &2))
  end

  defp op("Combinatorics", "choose", [n, k], _env) do
    n = int(n)
    k = int(k)
    if n < 0 or k < 0, do: error("choose needs natural numbers")

    if k > n,
      do: 0,
      else:
        div(Enum.reduce((n - k + 1)..n//1, 1, &(&1 * &2)), Enum.reduce(1..k//1, 1, &(&1 * &2)))
  end

  # -- Json --
  # As TLC's Json module: a record (or a function with strings in its
  # domain) is an object, a sequence or a set is an array.

  defp op("Json", "ToJson", [v], _env), do: v |> json_node() |> json_text()
  defp op("Json", "ToJsonArray", [v], _env), do: v |> json_array() |> json_text()
  defp op("Json", "ToJsonObject", [v], _env), do: v |> json_object() |> json_text()

  defp op("Json", "JsonSerialize", [path, v], _env) do
    record? =
      match?({:fun, m} when is_map(m), v) and Enum.all?(Map.keys(elem(v, 1)), &is_binary/1)

    unless match?({:seq, _}, v) or record?,
      do:
        error(
          "The second argument of JsonSerialize should be a sequence or record, but instead it is:\n#{Value.show(v)}"
        )

    write!(path, v |> json_node() |> json_text())
    true
  end

  defp op("Json", "ndJsonSerialize", [path, v], _env) do
    unless match?({:seq, _}, v),
      do:
        error(
          "The second argument of ndJsonSerialize should be a sequence, but instead it is:\n#{Value.show(v)}"
        )

    write!(path, v |> Value.seq_list() |> Enum.map_join("", &(json_text(json_node(&1)) <> "\n")))
    true
  end

  defp op("Json", "JsonDeserialize", [path], _env),
    do: path |> read!() |> JSON.decode!() |> from_json()

  defp op("Json", "ndJsonDeserialize", [path], _env) do
    path
    |> read!()
    |> String.split("\n")
    |> Enum.map(&String.trim/1)
    |> Enum.reject(&(&1 == ""))
    |> Enum.map(&(&1 |> JSON.decode!() |> from_json()))
    |> Value.tuple()
  end

  # -- IOUtils --

  defp op("IOUtils", "IOEnv", [], _env),
    do: System.get_env() |> Enum.map(fn {k, v} -> {k, v} end) |> Value.record()

  defp op("IOUtils", "atoi", [s], _env) do
    case Integer.parse(to_string(s)) do
      {n, ""} -> n
      _ -> error("atoi: #{Value.show(s)} is not a number")
    end
  end

  defp op("IOUtils", "IODeserialize", [path, compressed], _env) do
    case File.read(to_string(path)) do
      {:ok, bin} ->
        Accord.TLA.Checker.ValueStream.decode(bin, compressed == true)

      {:error, reason} ->
        error("IODeserialize: cannot read #{path}: #{:file.format_error(reason)}")
    end
  end

  defp op("IOUtils", "IOSerialize", [value, path, compressed], _env) do
    bin = Accord.TLA.Checker.ValueStream.encode(value, compressed == true)
    File.mkdir_p!(Path.dirname(to_string(path)))
    File.write!(to_string(path), bin)
    true
  end

  defp op(module, name, args, _env),
    do: error("#{module}!#{name} with #{length(args)} arguments is not supported")

  # -- Helpers --

  defp int(n) when is_integer(n), do: n
  defp int(v), do: error("expected an integer, not #{Value.show(v)}")

  defp read!(path) do
    case File.read(path) do
      {:ok, text} -> text
      {:error, reason} -> error("cannot read #{path}: #{:file.format_error(reason)}")
    end
  end

  defp graph(g) do
    nodes = g |> field("node") |> Value.enum()
    edges = g |> field("edge") |> Value.enum()
    {nodes, edges}
  end

  defp field({:fun, m}, name) do
    case Map.fetch(m, name) do
      {:ok, v} -> v
      :error -> error("the graph has no field #{name}")
    end
  end

  defp field(g, _name),
    do: error("expected a graph (a record with node and edge), not #{Value.show(g)}")

  defp node?(v, nodes), do: Enum.any?(nodes, &Value.eq?(&1, v))

  # An undirected edge: a set of one or two nodes.
  defp pair(%MapSet{} = e) do
    case Value.sort(MapSet.to_list(e)) do
      [a] -> {a, a}
      [a, b] -> {a, b}
      _ -> nil
    end
  end

  defp pair(_), do: nil

  # A directed edge: a pair.
  defp tuple_pair({:seq, {a, b}}), do: {a, b}
  defp tuple_pair(_), do: nil

  defp adjacency(g, endpoints, mode) do
    {nodes, edges} = graph(g)
    set = MapSet.new(nodes)

    Enum.reduce(edges, %{}, fn e, adj ->
      case endpoints.(e) do
        {a, b} ->
          if MapSet.member?(set, a) and MapSet.member?(set, b) do
            {from, to} = if mode == :transpose, do: {b, a}, else: {a, b}
            adj = Map.update(adj, from, [to], &(&1 ++ [to]))

            if mode == :symmetric and from != to,
              do: Map.update(adj, to, [from], &(&1 ++ [from])),
              else: adj
          else
            adj
          end

        nil ->
          adj
      end
    end)
  end

  defp reachable(source, adj), do: reach([source], adj, MapSet.new([source]))

  defp reach([], _adj, seen), do: seen

  defp reach([v | rest], adj, seen) do
    new = adj |> Map.get(v, []) |> Enum.reject(&MapSet.member?(seen, &1))
    reach(rest ++ new, adj, Enum.reduce(new, seen, &MapSet.put(&2, &1)))
  end

  defp connected?(m, n, g, endpoints, mode) do
    {nodes, _} = graph(g)

    cond do
      not node?(m, nodes) or not node?(n, nodes) -> false
      Value.eq?(m, n) -> true
      true -> g |> adjacency(endpoints, mode) |> then(&reachable(m, &1)) |> MapSet.member?(n)
    end
  end

  defp simple_paths(g, endpoints, mode) do
    {nodes, _} = graph(g)
    adj = adjacency(g, endpoints, mode)

    nodes
    |> Value.sort()
    |> Enum.flat_map(&extend([&1], MapSet.new([&1]), adj))
    |> Enum.map(&Value.tuple/1)
    |> MapSet.new()
  end

  defp extend([current | _] = path, visited, adj) do
    here = Enum.reverse(path)

    more =
      adj
      |> Map.get(current, [])
      |> Enum.reject(&MapSet.member?(visited, &1))
      |> Enum.flat_map(&extend([&1 | path], MapSet.put(visited, &1), adj))

    [here | more]
  end

  defp find(parent, x) do
    case Map.fetch!(parent, x) do
      ^x -> x
      p -> find(parent, p)
    end
  end

  defp union(parent, a, b) do
    ra = find(parent, a)
    rb = find(parent, b)
    if ra == rb, do: parent, else: Map.put(parent, rb, ra)
  end

  defp fold_function(opv, base, f, set, env) do
    set
    |> Value.enum()
    |> Value.sort()
    |> Enum.reduce(base, fn x, acc -> Eval.apply_op(opv, [Value.apply_fun(f, x), acc], env) end)
  end

  defp combinations(_list, 0), do: [[]]
  defp combinations([], _k), do: []

  defp combinations([x | rest], k),
    do: Enum.map(combinations(rest, k - 1), &[x | &1]) ++ combinations(rest, k)

  defp permutations([]), do: [[]]
  defp permutations(list), do: for(x <- list, rest <- permutations(list -- [x]), do: [x | rest])

  defp write!(path, text) do
    dir = Path.dirname(path)
    if dir != ".", do: File.mkdir_p!(dir)
    File.write!(path, text)
  end

  # JSON values: {:obj, [{key, value}]}, {:arr, [value]}, or a scalar.
  defp json_node(v) when is_integer(v) or is_boolean(v) or is_binary(v), do: v
  defp json_node({:mv, n}), do: n
  defp json_node({:seq, _} = s), do: json_array(s)
  defp json_node({:fun, _} = f), do: json_object(f)
  defp json_node(%MapSet{} = s), do: json_array(s)
  defp json_node({:lazy_fun, _, _} = f), do: f |> Value.canon() |> json_node()

  defp json_node(v) do
    if Value.set?(v),
      do: v |> Value.canon() |> json_node(),
      else: error("cannot convert #{Value.show(v)} to JSON")
  end

  defp json_array({:seq, t}), do: {:arr, t |> Tuple.to_list() |> Enum.map(&json_node/1)}
  defp json_array({:fun, _} = f), do: json_object(f)

  defp json_array(%MapSet{} = s),
    do: {:arr, s |> MapSet.to_list() |> Value.sort() |> Enum.map(&json_node/1)}

  defp json_array({:lazy_fun, _, _} = f), do: f |> Value.canon() |> json_array()

  defp json_array(v) do
    if Value.set?(v),
      do: v |> Value.canon() |> json_array(),
      else: error("cannot convert #{Value.show(v)} to a JSON array")
  end

  defp json_object({:seq, _} = s), do: json_array(s)

  defp json_object({:fun, m}) do
    {:obj,
     m
     |> Enum.map(fn {k, v} -> {if(is_binary(k), do: k, else: Value.show(k)), json_node(v)} end)
     |> Enum.sort_by(&elem(&1, 0))}
  end

  defp json_object({:lazy_fun, _, _} = f), do: f |> Value.canon() |> json_object()
  defp json_object(v), do: error("cannot convert #{Value.show(v)} to a JSON object")

  defp json_text(true), do: "true"
  defp json_text(false), do: "false"
  defp json_text(n) when is_integer(n), do: Integer.to_string(n)
  defp json_text(s) when is_binary(s), do: JSON.encode!(s)
  defp json_text({:arr, items}), do: "[" <> Enum.map_join(items, ",", &json_text/1) <> "]"

  defp json_text({:obj, fields}),
    do:
      "{" <>
        Enum.map_join(fields, ",", fn {k, v} -> JSON.encode!(k) <> ":" <> json_text(v) end) <> "}"

  defp from_json(v) when is_integer(v) or is_boolean(v) or is_binary(v), do: v
  defp from_json(v) when is_float(v), do: error("JSON number #{v} is not an integer")
  defp from_json(nil), do: error("JSON null has no TLA+ value")
  defp from_json(l) when is_list(l), do: l |> Enum.map(&from_json/1) |> Value.tuple()
  defp from_json(%{} = m), do: m |> Enum.map(fn {k, v} -> {k, from_json(v)} end) |> Value.record()
end
