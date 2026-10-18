defmodule Accord.TLA.Checker.Value do
  @moduledoc """
  TLA+ values, and the operations on them.

  ## Canonical values

  A canonical value has one form, so that two equal TLA+ values are equal
  Elixir terms. The checker uses canonical values as states and as map
  keys.

  - an integer, `true`, or `false`
  - a string: an Elixir binary
  - a model value: `{:mv, name}`
  - a finite set: a `MapSet` of canonical values
  - a function whose domain is `1..n` (a tuple or a sequence), or the
    empty function: `{:seq, tuple}`
  - any other function, also a record: `{:fun, map}`

  In TLA+, `<<a, b>>` is the function `[i \\in 1..2 |-> ...]`, and a
  record `[a |-> 1]` is the function `[x \\in {"a"} |-> 1]`. The
  representation keeps these equal.

  ## Lazy values

  Some sets are large or infinite. They stay lazy until a value must be
  enumerated or stored:

  - `{:interval, a, b}` — `a..b`
  - `:nat`, `:int`, `:string`, `:any` — `Nat`, `Int`, `STRING`, and the
    set of all values
  - `{:subset, s}`, `{:fun_set, d, r}`, `{:seq_set, s}`,
    `{:record_set, [{field, set}]}`, `{:times, [set]}`, `{:union, s}`
  - `{:lazy_fun, domain, fun}` — a function given by an Elixir function,
    for function definitions with an infinite domain

  `canon/1` gives the canonical form of a value, or raises when a value
  is infinite.
  """

  defmodule Error do
    @moduledoc "An evaluation error."
    defexception [:message]
  end

  @big_interval 2_000

  # -- Construction --

  @doc "Makes a finite set from a list of values."
  def set(list), do: MapSet.new(list, &canon/1)

  @doc "The interval `a..b`."
  def interval(a, b) when is_integer(a) and is_integer(b) do
    cond do
      b < a -> MapSet.new()
      b - a < @big_interval -> MapSet.new(a..b)
      true -> {:interval, a, b}
    end
  end

  def interval(a, b), do: error("`..` needs integers, not #{show(a)} and #{show(b)}")

  @doc "Makes a tuple (a sequence) from a list of values."
  def tuple(list), do: {:seq, list |> Enum.map(&canon/1) |> List.to_tuple()}

  @doc """
  Makes a function from a map of canonical keys to values. A function
  with the domain `1..n` becomes a sequence.
  """
  def fun(map) when map_size(map) == 0, do: {:seq, {}}

  def fun(map) do
    n = map_size(map)
    map = Map.new(map, fn {k, v} -> {k, canon(v)} end)

    if Enum.all?(1..n, &Map.has_key?(map, &1)),
      do: {:seq, List.to_tuple(for i <- 1..n, do: Map.fetch!(map, i))},
      else: {:fun, map}
  end

  @doc "Makes a record from a list of `{field, value}`."
  def record(fields), do: fun(Map.new(fields, fn {k, v} -> {k, canon(v)} end))

  # -- Canonical form --

  @doc """
  Gives the canonical form of a value. Raises for an infinite value.
  """
  def canon(v) when is_integer(v) or is_boolean(v) or is_binary(v), do: v
  def canon({:mv, _} = v), do: v
  def canon(%MapSet{} = s), do: s
  def canon({:seq, _} = s), do: s
  def canon({:fun, _} = f), do: f
  def canon({:interval, a, b}), do: MapSet.new(a..b)

  def canon({:lazy_fun, domain, f}) do
    keys = enum(domain)
    fun(Map.new(keys, fn k -> {k, f.(k)} end))
  end

  # An infinite set stays lazy: TLC can keep it as a value (for example as
  # an element of a set) as long as nothing enumerates it.
  def canon(v) do
    cond do
      not lazy_set?(v) -> error("not a value: #{inspect(v)}")
      infinite?(v) -> v
      true -> MapSet.new(enum(v))
    end
  end

  @doc "Tells if a value is a set (finite or lazy)."
  def set?(%MapSet{}), do: true
  def set?(v), do: lazy_set?(v)

  defp lazy_set?({:interval, _, _}), do: true
  defp lazy_set?(atom) when atom in [:nat, :int, :string, :any], do: true

  defp lazy_set?({kind, _}) when kind in [:subset, :seq_set, :record_set, :times, :union],
    do: true

  defp lazy_set?({:fun_set, _, _}), do: true
  defp lazy_set?({kind, _, _}) when kind in [:diff, :cap, :filter], do: true
  defp lazy_set?({:cup, _}), do: true
  defp lazy_set?(_), do: false

  @doc "Tells if a set is infinite (or TLC cannot enumerate it)."
  def infinite?(s) when s in [:nat, :int, :string, :any], do: true
  def infinite?({:seq_set, _}), do: true
  def infinite?({:diff, a, _}), do: infinite?(a)
  def infinite?({:cap, a, b}), do: infinite?(a) and infinite?(b)
  def infinite?({:cup, sets}), do: Enum.any?(sets, &infinite?/1)
  def infinite?({:filter, s, _}), do: infinite?(s)
  def infinite?({:subset, s}), do: infinite?(s)
  def infinite?({:fun_set, d, r}), do: infinite?(d) or infinite?(r)
  def infinite?({:record_set, fields}), do: Enum.any?(fields, fn {_, s} -> infinite?(s) end)
  def infinite?({:times, sets}), do: Enum.any?(sets, &infinite?/1)
  def infinite?(_), do: false

  @doc "Tells if a value is a function (also a sequence or a record)."
  def fun?({:seq, _}), do: true
  def fun?({:fun, _}), do: true
  def fun?({:lazy_fun, _, _}), do: true
  def fun?(_), do: false

  # -- Equality and membership --

  @doc "TLA+ equality."
  def eq?(a, b) when is_integer(a) and is_integer(b), do: a == b
  def eq?(a, b) when is_binary(a) and is_binary(b), do: a == b
  def eq?(a, a), do: true
  def eq?(a, b), do: canon(a) == canon(b)

  @doc "`x \\in s`."
  def member?(x, %MapSet{} = s), do: MapSet.member?(s, canon(x))
  def member?(x, {:interval, a, b}), do: is_integer(x) and x >= a and x <= b
  def member?(x, :nat), do: is_integer(x) and x >= 0
  def member?(x, :int), do: is_integer(x)
  def member?(x, :string), do: is_binary(x)
  def member?(_x, :any), do: true

  def member?(x, {:subset, s}) do
    set?(x) and Enum.all?(enum(x), &member?(&1, s))
  end

  def member?(x, {:fun_set, d, r}) do
    fun?(x) and eq?(domain(x), d) and Enum.all?(enum(domain(x)), &member?(apply_fun(x, &1), r))
  end

  def member?(x, {:seq_set, s}) do
    case x do
      {:seq, t} -> Enum.all?(Tuple.to_list(t), &member?(&1, s))
      _ -> false
    end
  end

  def member?(x, {:record_set, fields}) do
    case x do
      {:fun, m} ->
        map_size(m) == length(fields) and
          Enum.all?(fields, fn {f, s} -> Map.has_key?(m, f) and member?(Map.fetch!(m, f), s) end)

      {:seq, {}} ->
        fields == []

      _ ->
        false
    end
  end

  def member?(x, {:times, sets}) do
    case x do
      {:seq, t} when tuple_size(t) == length(sets) ->
        sets |> Enum.with_index() |> Enum.all?(fn {s, i} -> member?(elem(t, i), s) end)

      _ ->
        false
    end
  end

  def member?(x, {:union, s}), do: Enum.any?(enum(s), &member?(x, &1))
  def member?(x, {:diff, a, b}), do: member?(x, a) and not member?(x, b)
  def member?(x, {:cap, a, b}), do: member?(x, a) and member?(x, b)
  def member?(x, {:cup, sets}), do: Enum.any?(sets, &member?(x, &1))
  def member?(x, {:filter, s, pred}), do: member?(x, s) and pred.(x)
  def member?(_x, s), do: error("`\\in` needs a set, not #{show(s)}")

  # -- Enumeration --

  @doc "The elements of a set, as a list. Raises for an infinite set."
  def enum(%MapSet{} = s), do: MapSet.to_list(s)
  def enum({:interval, a, b}), do: Enum.to_list(a..b)

  def enum({:subset, s}) do
    s
    |> enum()
    |> Enum.reverse()
    |> Enum.reduce([MapSet.new()], fn x, acc -> acc ++ Enum.map(acc, &MapSet.put(&1, x)) end)
  end

  def enum({:fun_set, d, r}) do
    keys = enum(d)
    values = enum(r)

    keys
    |> Enum.reduce([%{}], fn k, acc -> for m <- acc, v <- values, do: Map.put(m, k, v) end)
    |> Enum.map(&fun/1)
  end

  def enum({:record_set, fields}) do
    fields
    |> Enum.reduce([%{}], fn {f, s}, acc ->
      values = enum(s)
      for m <- acc, v <- values, do: Map.put(m, f, v)
    end)
    |> Enum.map(&fun/1)
  end

  def enum({:times, sets}) do
    sets
    |> Enum.reduce([[]], fn s, acc ->
      values = enum(s)
      for l <- acc, v <- values, do: [v | l]
    end)
    |> Enum.map(&(&1 |> Enum.reverse() |> List.to_tuple() |> then(fn t -> {:seq, t} end)))
  end

  def enum({:union, s}), do: s |> enum() |> Enum.flat_map(&enum/1) |> Enum.uniq()

  def enum({:filter, s, pred}) do
    if infinite?(s), do: error("cannot enumerate the infinite set #{show(s)}")
    s |> enum() |> Enum.filter(pred)
  end

  def enum({kind, _, _} = s) when kind in [:diff, :cap],
    do: error("cannot enumerate the infinite set #{show(s)}")

  def enum({:cup, _} = s), do: error("cannot enumerate the infinite set #{show(s)}")

  def enum(s) when s in [:nat, :int, :string, :any, {:seq_set, nil}],
    do: error("cannot enumerate the infinite set #{show(s)}")

  def enum({:seq_set, _} = s), do: error("cannot enumerate the infinite set #{show(s)}")
  def enum(v), do: error("expected a set, not #{show(v)}")

  @doc "The number of elements of a finite set."
  def size(%MapSet{} = s), do: MapSet.size(s)
  def size({:interval, a, b}), do: max(b - a + 1, 0)
  def size({:subset, s}), do: Integer.pow(2, size(s))

  def size({:fun_set, d, r}) do
    case size(d) do
      0 -> 1
      n -> Integer.pow(size(r), n)
    end
  end

  def size({:times, sets}), do: Enum.reduce(sets, 1, &(size(&1) * &2))
  def size({:record_set, fields}), do: Enum.reduce(fields, 1, fn {_, s}, acc -> size(s) * acc end)
  def size(s), do: length(enum(s))

  # -- Set operations --

  def union(a, b) do
    if infinite?(a) or infinite?(b), do: {:cup, [a, b]}, else: MapSet.union(to_set(a), to_set(b))
  end

  def intersection(a, b) do
    case {infinite?(a), infinite?(b)} do
      {false, false} -> MapSet.intersection(to_set(a), to_set(b))
      {false, true} -> a |> to_set() |> MapSet.filter(&member?(&1, b))
      {true, false} -> b |> to_set() |> MapSet.filter(&member?(&1, a))
      {true, true} -> {:cap, a, b}
    end
  end

  def difference(a, b) when not is_struct(a, MapSet) do
    if infinite?(a), do: {:diff, a, b}, else: difference(to_set(a), b)
  end

  def difference(%MapSet{} = a, b) do
    if match?(%MapSet{}, b),
      do: MapSet.difference(a, b),
      else: MapSet.reject(a, &member?(&1, b))
  end

  def subseteq?(a, b), do: Enum.all?(enum(a), &member?(&1, b))

  @doc "A finite set as a MapSet."
  def to_set(%MapSet{} = s), do: s
  def to_set(s), do: MapSet.new(enum(s))

  # -- Functions --

  @doc "`f[x]`."
  def apply_fun({:seq, t}, i) when is_integer(i) and i >= 1 and i <= tuple_size(t),
    do: elem(t, i - 1)

  def apply_fun({:fun, m} = f, x) do
    case Map.fetch(m, canon(x)) do
      {:ok, v} -> v
      :error -> error("#{show(x)} is not in the domain of #{show(f)}")
    end
  end

  def apply_fun({:lazy_fun, d, f}, x) do
    if member?(x, d), do: f.(x), else: error("#{show(x)} is not in the domain of the function")
  end

  def apply_fun(f, x) do
    if fun?(f),
      do: error("#{show(x)} is not in the domain of #{show(f)}"),
      else: error("cannot apply #{show(f)}: it is not a function")
  end

  @doc "`DOMAIN f`."
  def domain({:seq, t}), do: interval(1, tuple_size(t))
  def domain({:fun, m}), do: MapSet.new(Map.keys(m))
  def domain({:lazy_fun, d, _}), do: d
  def domain(v), do: error("DOMAIN needs a function, not #{show(v)}")

  @doc "The pairs of a finite function."
  def pairs({:seq, t}),
    do: t |> Tuple.to_list() |> Enum.with_index(1) |> Enum.map(fn {v, i} -> {i, v} end)

  def pairs({:fun, m}), do: Map.to_list(m)
  def pairs({:lazy_fun, _, _} = f), do: f |> canon() |> pairs()

  @doc "`[f EXCEPT ![x] = v]` for one key."
  def update({:seq, t} = f, i, v) when is_integer(i) do
    if i >= 1 and i <= tuple_size(t),
      do: {:seq, put_elem(t, i - 1, canon(v))},
      else: error("#{show(i)} is not in the domain of #{show(f)}")
  end

  def update({:fun, m} = f, x, v) do
    k = canon(x)

    if Map.has_key?(m, k),
      do: {:fun, Map.put(m, k, canon(v))},
      else: error("#{show(x)} is not in the domain of #{show(f)}")
  end

  def update({:lazy_fun, _, _} = f, x, v), do: update(canon(f), x, v)
  def update({:seq, _} = f, x, _v), do: error("#{show(x)} is not in the domain of #{show(f)}")
  def update(f, _x, _v), do: error("EXCEPT needs a function, not #{show(f)}")

  @doc "The elements of a sequence, as a list."
  def seq_list({:seq, t}), do: Tuple.to_list(t)
  def seq_list({:fun, _} = f), do: error("#{show(f)} is not a sequence")
  def seq_list(v), do: error("expected a sequence, not #{show(v)}")

  # -- Order --

  @doc """
  A total order on values, close to the order that TLC prints: numbers,
  then strings, then model values, then booleans, then sets, then
  functions.
  """
  def compare(a, b) do
    ka = sort_key(a)
    kb = sort_key(b)

    cond do
      ka < kb -> :lt
      ka > kb -> :gt
      true -> :eq
    end
  end

  def sort(values), do: Enum.sort(values, &(compare(&1, &2) != :gt))

  defp sort_key(v) when is_boolean(v), do: {3, v}
  defp sort_key(v) when is_integer(v), do: {0, v}
  defp sort_key(v) when is_binary(v), do: {1, v}
  defp sort_key({:mv, n}), do: {2, n}

  defp sort_key(%MapSet{} = s),
    do: {4, MapSet.size(s), s |> MapSet.to_list() |> sort() |> Enum.map(&sort_key/1)}

  defp sort_key({:seq, t}), do: {5, tuple_size(t), t |> Tuple.to_list() |> Enum.map(&sort_key/1)}

  defp sort_key({:fun, m}),
    do:
      {6, map_size(m),
       m |> Map.to_list() |> Enum.map(fn {k, v} -> {sort_key(k), sort_key(v)} end) |> Enum.sort()}

  defp sort_key(other), do: {9, inspect(other)}

  # -- Printing --

  @doc "Writes a value in the form that TLC prints."
  def show(true), do: "TRUE"
  def show(false), do: "FALSE"
  def show(n) when is_integer(n), do: Integer.to_string(n)
  def show(s) when is_binary(s), do: inspect(s)
  def show({:mv, n}), do: n

  def show(%MapSet{} = s),
    do: "{" <> (s |> MapSet.to_list() |> sort() |> Enum.map_join(", ", &show/1)) <> "}"

  def show({:seq, t}), do: "<<" <> (t |> Tuple.to_list() |> Enum.map_join(", ", &show/1)) <> ">>"

  def show({:fun, m}) do
    if Enum.all?(Map.keys(m), &is_binary/1) do
      "[" <>
        (m |> Enum.sort() |> Enum.map_join(", ", fn {k, v} -> "#{k} |-> #{show(v)}" end)) <> "]"
    else
      "(" <>
        (m
         |> Map.to_list()
         |> Enum.sort_by(&elem(&1, 0), &(compare(&1, &2) != :gt))
         |> Enum.map_join(" @@ ", fn {k, v} -> "#{show(k)} :> #{show(v)}" end)) <> ")"
    end
  end

  def show({:interval, a, b}), do: "#{a}..#{b}"
  def show(:nat), do: "Nat"
  def show(:int), do: "Int"
  def show(:string), do: "STRING"
  def show(:any), do: "the set of all values"
  def show({:subset, s}), do: "SUBSET #{show(s)}"
  def show({:fun_set, d, r}), do: "[#{show(d)} -> #{show(r)}]"
  def show({:seq_set, s}), do: "Seq(#{show(s)})"
  def show({:union, s}), do: "UNION #{show(s)}"
  def show({:times, sets}), do: Enum.map_join(sets, " \\X ", &show/1)

  def show({:record_set, fields}),
    do: "[" <> Enum.map_join(fields, ", ", fn {f, s} -> "#{f} : #{show(s)}" end) <> "]"

  def show({:diff, a, b}), do: "(#{show(a)} \\ #{show(b)})"
  def show({:cap, a, b}), do: "(#{show(a)} \\cap #{show(b)})"
  def show({:cup, sets}), do: "(" <> Enum.map_join(sets, " \\cup ", &show/1) <> ")"
  def show({:filter, s, _}), do: "{x \\in #{show(s)} : ...}"
  def show({:lazy_fun, d, _}), do: "[x \\in #{show(d)} |-> ...]"
  def show({:op_value, name, _, _}), do: "operator #{name}"
  def show(other), do: inspect(other)

  @doc "Raises an evaluation error."
  @spec error(String.t()) :: no_return()
  def error(message), do: raise(Error, message: message)
end
