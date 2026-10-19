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
    @moduledoc """
    An evaluation error. `module: true` for an error in an operator of a
    standard module: TLC reports these with another exit code than the
    errors of the core semantics.
    """
    defexception [:message, module: false, fingerprint: false]
  end

  @big_interval 2_000
  @builtin_sets [:nat, :int, :string, :any]

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
  def canon({:interval, a, b} = s), do: if(b - a >= 100_000, do: s, else: MapSet.new(a..b))

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
      # A large set with a known size stays lazy (TLC enumerates it only
      # when it must).
      large?(v) -> v
      true -> MapSet.new(enum(v))
    end
  end

  @doc "Tells if a value is a set (finite or lazy)."
  def set?(%MapSet{}), do: true
  def set?(v), do: lazy_set?(v)

  @doc "Tells if a value is a lazy set."
  def lazy?(v), do: lazy_set?(v)

  defp lazy_set?({:interval, _, _}), do: true
  defp lazy_set?(atom) when atom in [:nat, :int, :string, :any], do: true

  defp lazy_set?({kind, _}) when kind in [:subset, :seq_set, :record_set, :times, :union],
    do: true

  defp lazy_set?({:fun_set, _, _}), do: true
  defp lazy_set?({:ksubset, _, _}), do: true
  defp lazy_set?({kind, _, _}) when kind in [:diff, :cap, :filter], do: true
  defp lazy_set?({:cup, _}), do: true
  defp lazy_set?(_), do: false

  @doc """
  Tells if a set is infinite, or TLC cannot enumerate it. The checker uses
  this to keep a set lazy; `finite?/1` is `IsFiniteSet` with the rules of
  TLC.
  """
  def infinite?(s) when s in [:nat, :int, :string, :any], do: true
  def infinite?({:seq_set, _}), do: true
  def infinite?({:diff, a, _}), do: infinite?(a)
  def infinite?({:cap, a, b}), do: infinite?(a) and infinite?(b)
  def infinite?({:cup, sets}), do: Enum.any?(sets, &infinite?/1)
  def infinite?({:filter, s, _}), do: infinite?(s)
  def infinite?({:subset, s}), do: infinite?(s)
  def infinite?({:union, s}), do: s |> enum() |> Enum.any?(&infinite?/1)
  def infinite?({:ksubset, _, _} = s), do: not finite?(s)

  # An empty domain gives {<<>>}; an empty range (with a domain that is
  # not empty) gives {}; a range of one element gives one function.
  def infinite?({:fun_set, d, r}),
    do:
      not safe_empty?(d) and not safe_empty?(r) and
        (infinite?(r) or (infinite?(d) and safe_size(r) != 1))

  def infinite?({:record_set, fields}),
    do:
      not Enum.any?(fields, fn {_, s} -> safe_empty?(s) end) and
        Enum.any?(fields, fn {_, s} -> infinite?(s) end)

  def infinite?({:times, sets}),
    do: not Enum.any?(sets, &safe_empty?/1) and Enum.any?(sets, &infinite?/1)

  def infinite?(_), do: false

  defp safe_empty?(s) do
    empty?(s)
  rescue
    Error -> false
  end

  defp safe_size(s) do
    size(s)
  rescue
    Error -> :unknown
  end

  @doc "`IsFiniteSet(s)`, with the rules (and the errors) of TLC."
  def finite?(%MapSet{}), do: true
  def finite?({:interval, _, _}), do: true
  def finite?(s) when s in [:nat, :int, :string, :any], do: false
  def finite?({:subset, s}), do: finite?(s)

  def finite?({:fun_set, d, r}) do
    fd = finite?(d)

    if fd and empty?(d) do
      true
    else
      fr = finite?(r)

      cond do
        fr and empty?(r) -> true
        fd and fr -> true
        true -> fr and size(r) == 1
      end
    end
  end

  def finite?({:record_set, fields}), do: parts_finite?(Enum.map(fields, &elem(&1, 1)))
  def finite?({:times, sets}), do: parts_finite?(sets)
  def finite?({:seq_set, s}), do: finite?(s) and empty?(s)

  def finite?({:diff, a, b} = s) do
    cond do
      finite?(a) -> true
      not finite?(b) -> error("Attempted to check if the set #{show(s)}is finite.")
      true -> false
    end
  end

  def finite?({:cap, a, b} = s) do
    if not finite?(a) and not finite?(b),
      do: error("Attempted to check if the set #{show(s)}is finite."),
      else: true
  end

  def finite?({:ksubset, k, s}), do: k <= 0 or finite?(s)
  def finite?({:cup, sets}), do: Enum.all?(sets, &finite?/1)
  def finite?({:union, s}), do: s |> enum() |> Enum.all?(&finite?/1)

  def finite?({:filter, inner, _}) do
    if finite?(inner),
      do: true,
      else:
        error(
          "Attempted to check if expression of form {x \\in S : p(x)} is a finite set, but cannot check if S:\n#{show(inner)}\nis finite."
        )
  end

  def finite?(v), do: error("Attempted to check if #{show(v)} is a finite set.")

  # A set of records or tuples is finite when a finite part is empty, or
  # when all the parts are finite.
  defp parts_finite?(parts) do
    Enum.reduce_while(parts, true, fn p, all ->
      if finite?(p) do
        if empty?(p), do: {:halt, true}, else: {:cont, all}
      else
        {:cont, false}
      end
    end)
  end

  @doc """
  Tells if a set is empty, with the rules of TLC: a set of functions, of
  records, or of tuples decides from its parts; a difference, an
  intersection, a union, or a filter looks for a first element (an error
  when TLC cannot enumerate it).
  """
  def empty?(%MapSet{} = s), do: MapSet.size(s) == 0
  def empty?({:interval, a, b}), do: b < a
  def empty?(s) when s in [:nat, :int, :string], do: false
  def empty?(:any), do: error("Shouldn't call isEmpty() on value ANY")
  def empty?({:subset, _}), do: false
  def empty?({:ksubset, _, _} = s), do: ksubset_none?(s)
  def empty?({:seq_set, _}), do: false
  def empty?({:fun_set, d, r}), do: not empty?(d) and empty?(r)
  def empty?({:record_set, fields}), do: Enum.any?(fields, fn {_, s} -> empty?(s) end)
  def empty?({:times, sets}), do: Enum.any?(sets, &empty?/1)
  def empty?({kind, _} = s) when kind in [:cup, :union], do: first(s) == :none
  def empty?({kind, _, _} = s) when kind in [:cap, :diff, :filter], do: first(s) == :none
  def empty?(v), do: error("Shouldn't call isEmpty() on value #{show(v)}")

  # The first element of a lazy set, as TLC enumerates it, or :none.
  defp first(%MapSet{} = s), do: s |> MapSet.to_list() |> List.first(:none)
  defp first({:interval, a, b}), do: if(a <= b, do: a, else: :none)

  defp first({:diff, a, b}) do
    if not enumerable?(a),
      do: error("Attempted to enumerate S \\ T when S:\n#{show(a)}\nis not enumerable.")

    a |> enum() |> Enum.find(:none, &(not member?(&1, b)))
  end

  defp first({:cap, a, b}) do
    cond do
      enumerable?(a) ->
        a |> enum() |> Enum.find(:none, &member?(&1, b))

      enumerable?(b) ->
        b |> enum() |> Enum.find(:none, &member?(&1, a))

      true ->
        error(
          "Attempted to enumerate S \\cap T when S:\n#{show(a)}\nand T:\n#{show(b)}\nare not both enumerable"
        )
    end
  end

  defp first({:cup, [a, b]} = s) do
    if not (enumerable?(a) and enumerable?(b)),
      do:
        error(
          "Attempted to enumerate S \\cup T when S:\n#{show(a)}\nand T:\n#{show(b)}\nare not both enumerable"
        )

    s |> elem(1) |> Enum.find_value(:none, fn x -> if (f = first_of(x)) != :none, do: f end)
  end

  defp first({:cup, sets}),
    do: Enum.find_value(sets, :none, fn x -> if (f = first_of(x)) != :none, do: f end)

  defp first({:union, s}) do
    elems = enum(s)

    if not Enum.all?(elems, &enumerable?/1),
      do: error("Attempted to enumerate UNION(s), but some element of s is nonenumerable.")

    Enum.find_value(elems, :none, fn x -> if (f = first_of(x)) != :none, do: f end)
  end

  defp first({:filter, inner, pred}) do
    if not enumerable?(inner),
      do:
        error(
          "Attempted to enumerate { x \\in S : p(x) } when S:\n#{show(inner)}\nis not enumerable"
        )

    inner |> enum() |> Enum.find(:none, pred)
  end

  defp first(s), do: s |> enum() |> List.first(:none)

  defp first_of(s), do: if(empty?(s), do: :none, else: first(s))

  # TLC can enumerate the set (Nat, Int, STRING, and Seq(S) are not).
  defp enumerable?(s) when s in [:nat, :int, :string, :any], do: false
  defp enumerable?({:seq_set, _}), do: false
  defp enumerable?(s), do: not infinite?(s)

  @doc "Tells if a value is a function (also a sequence or a record)."
  def fun?({:seq, _}), do: true
  def fun?({:fun, _}), do: true
  def fun?({:lazy_fun, _, _}), do: true
  def fun?(_), do: false

  # -- Equality and membership --

  @doc """
  TLA+ equality, with the rules of TLC: two values of different kinds (an
  integer and a set, for example) cannot be compared, and the comparison
  is an error. A model value is not equal to a value of another kind; a
  typed model value (`A_x`) cannot be compared with a value of another
  kind or with a model value of another type.
  """
  def eq?(a, b) when is_integer(a) and is_integer(b), do: a == b
  def eq?(a, b) when is_binary(a) and is_binary(b), do: a == b
  # The same value (not a lazy set: TLC compares the parts of those; a set
  # or a function is sorted for the comparison).
  def eq?(a, a) when not is_tuple(a) and not is_struct(a, MapSet), do: true
  def eq?(a, a) when is_tuple(a) and elem(a, 0) in [:seq, :mv], do: true

  def eq?(%MapSet{} = a, a) do
    normalize!(a)
    true
  end

  def eq?({:fun, m} = a, a) do
    m |> Map.keys() |> MapSet.new() |> normalize!()
    true
  end

  def eq?(a, b) do
    case {kind(a), kind(b)} do
      {:mv, :mv} -> model_values_eq?(a, b)
      {:mv, _} -> model_value_other(a, b)
      {_, :mv} -> model_value_other(b, a)
      {:set, :set} -> set_eq?(a, b)
      {:fun, :fun} -> fun_eq?(a, b)
      {k, k} -> canon(a) == canon(b)
      {:other, _} -> canon(a) == canon(b)
      {_, :other} -> canon(a) == canon(b)
      {k, _} -> error(mismatch(k, a, b))
    end
  end

  # Set equality with the rules of TLC: sets of functions, records, and
  # tuples compare their parts; Nat, Int, STRING, and Seq(S) compare with
  # sets of the same form only; other lazy sets are enumerated.
  defp set_eq?({:fun_set, d1, r1}, {:fun_set, d2, r2}) do
    u1 = empty?(d1)
    u2 = empty?(d2)

    cond do
      u1 or u2 ->
        u1 == u2

      empty?(r1) or empty?(r2) ->
        empty?(r1) == empty?(r2)

      true ->
        eq?(d1, d2) and eq?(r1, r2)
    end
  end

  defp set_eq?({:record_set, f1} = a, {:record_set, f2} = b) do
    cond do
      empty?(a) ->
        empty?(b)

      empty?(b) ->
        false

      length(f1) != length(f2) ->
        false

      true ->
        Enum.zip(Enum.sort(f1), Enum.sort(f2))
        |> Enum.all?(fn {{n1, s1}, {n2, s2}} -> n1 == n2 and eq?(s1, s2) end)
    end
  end

  defp set_eq?({:times, s1} = a, {:times, s2} = b) do
    cond do
      empty?(a) -> empty?(b)
      empty?(b) -> false
      length(s1) != length(s2) -> false
      true -> Enum.zip(s1, s2) |> Enum.all?(fn {x, y} -> eq?(x, y) end)
    end
  end

  defp set_eq?({:ksubset, k1, s1} = a, {:ksubset, k2, s2} = b) do
    cond do
      ksubset_none?(a) or ksubset_none?(b) -> ksubset_none?(a) and ksubset_none?(b)
      k1 == 0 and k2 == 0 -> true
      true -> k1 == k2 and eq?(s1, s2)
    end
  end

  defp set_eq?({:ksubset, _, _} = a, b) do
    cond do
      finite?(a) and not infinite?(b) -> elements_eq?(canon(a), canon(b))
      not infinite?(b) -> false
      true -> error("cannot enumerate the infinite set #{show(a)}")
    end
  end

  defp set_eq?(a, {:ksubset, _, _} = b), do: set_eq?(b, a)

  defp set_eq?({:seq_set, s1}, {:seq_set, s2}), do: eq?(s1, s2)
  defp set_eq?({:subset, s1}, {:subset, s2}), do: eq?(s1, s2)

  defp set_eq?(a, b) when elem(a, 0) == :seq_set or elem(b, 0) == :seq_set,
    do:
      error(
        "Attempted to compare overridden value #{show(a)} with non-overridden value:\n#{show(b)}"
      )

  defp set_eq?(a, b) when a in @builtin_sets or b in @builtin_sets do
    if a in @builtin_sets and b in @builtin_sets,
      do: a == b,
      else:
        error(
          "Attempted to compare overridden value #{show(a)} with non-overridden value:\n#{show(b)}"
        )
  end

  defp set_eq?(a, b) do
    cond do
      infinite?(a) -> error("cannot enumerate the infinite set #{show(a)}")
      infinite?(b) -> error("cannot enumerate the infinite set #{show(b)}")
      true -> elements_eq?(canon(a), canon(b))
    end
  end

  # TLC compares the elements one by one (so values of different kinds
  # are an error).
  defp elements_eq?(ca, cb) do
    normalize!(ca)
    normalize!(cb)

    cond do
      ca == cb ->
        true

      not (is_struct(ca, MapSet) and is_struct(cb, MapSet)) ->
        false

      MapSet.size(ca) != MapSet.size(cb) ->
        false

      true ->
        ca
        |> MapSet.to_list()
        |> sort()
        |> Enum.zip(cb |> MapSet.to_list() |> sort())
        |> Enum.all?(fn {x, y} -> eq?(x, y) end)
    end
  end

  # TLC cannot compare a record with a tuple.
  defp fun_eq?({:fun, m} = a, {:seq, t} = b) when tuple_size(t) > 0 do
    if Enum.all?(Map.keys(m), &is_binary/1),
      do:
        error("Attempted to check equality of record:\n#{show(a)}\nwith non-record\n#{show(b)}"),
      else: canon(a) == canon(b)
  end

  defp fun_eq?({:seq, t} = a, {:fun, m} = b) when tuple_size(t) > 0 do
    if Enum.all?(Map.keys(m), &is_binary/1) and map_size(m) == tuple_size(t),
      do: error("Attempted to compare an integer with non-integer:\n#{show(b)}."),
      else: canon(a) == canon(b)
  end

  defp fun_eq?(a, b) do
    # TLC sorts the domains to compare two functions.
    if is_tuple(a) and elem(a, 0) == :fun,
      do: a |> elem(1) |> Map.keys() |> MapSet.new() |> normalize!()

    if is_tuple(b) and elem(b, 0) == :fun,
      do: b |> elem(1) |> Map.keys() |> MapSet.new() |> normalize!()

    canon(a) == canon(b)
  end

  defp kind(v) when is_integer(v), do: :int
  defp kind(v) when is_boolean(v), do: :bool
  defp kind(v) when is_binary(v), do: :str
  defp kind({:mv, _}), do: :mv

  defp kind(v) do
    cond do
      fun?(v) -> :fun
      set?(v) -> :set
      true -> :other
    end
  end

  defp mismatch(:int, a, b),
    do: "Attempted to check equality of integer #{show(a)} with non-integer:\n#{show(b)}"

  defp mismatch(:bool, a, b),
    do: "Attempted to compare equality of boolean #{show(a)} with non-boolean:\n#{show(b)}"

  defp mismatch(:str, a, b),
    do: "Attempted to check equality of string #{show(a)} with non-string:\n#{show(b)}"

  defp mismatch(:set, a, b),
    do: "Attempted to check equality of the set #{show(a)} with the value:\n#{show(b)}"

  defp mismatch(:fun, a, b),
    do: "Attempted to check equality of the function #{show(a)} with the value:\n#{show(b)}"

  @doc "The type of a model value (`A_x` has the type `A`), or `nil`."
  def model_value_type({:mv, <<t, ?_, _, _::binary>>}), do: t
  def model_value_type({:mv, _}), do: nil

  defp model_values_eq?(a, b) do
    ta = model_value_type(a)
    tb = model_value_type(b)

    if ta && tb && ta != tb,
      do:
        error(
          "Attempted to check equality of the differently-typed model values #{show(a)} and #{show(b)}"
        )

    a == b
  end

  defp model_value_other(mv, other) do
    if model_value_type(mv),
      do:
        error(
          "Attempted to check equality of typed model value #{show(mv)} and non-model value\n#{show(other)}"
        )

    false
  end

  @doc """
  Checks that the elements of a set (or the domain of a function) can be
  ordered with the rules of TLC: a typed model value cannot be in a set
  with a value of another kind or a model value of another type.
  """
  def check_order!(values) do
    typed = for {:mv, _} = v <- values, t = model_value_type(v), uniq: true, do: {t, v}

    case typed do
      [] ->
        :ok

      [{t, v} | _] ->
        Enum.each(values, fn
          {:mv, _} = w ->
            u = model_value_type(w)

            if u && u != t,
              do:
                error(
                  "Attempted to compare the differently-typed model values #{show(w)} and #{show(v)}"
                )

          w ->
            error(
              "Attempted to compare the typed model value #{show(v)} and non-model value\n#{show(w)}"
            )
        end)
    end
  end

  @doc "`x \\in s`."
  def member?(x, %MapSet{} = s) do
    c = canon(x)

    if MapSet.member?(s, c) do
      # TLC compares the value with the elements before it: the first
      # element of another kind is an error (the check uses the first
      # element only).
      case first_element(s) do
        ^c -> true
        nil -> true
        {:mv, _} -> true
        _ when elem(c, 0) == :mv -> true
        e -> not_member(c, MapSet.new([e])) or true
      end
    else
      not_member(c, s)
    end
  end

  def member?(x, {:interval, a, b} = s),
    do: if(is_integer(x), do: x >= a and x <= b, else: bad_member(x, s))

  def member?(x, :nat), do: if(is_integer(x), do: x >= 0, else: bad_member(x, :nat))
  def member?(x, :int), do: is_integer(x) or bad_member(x, :int)
  def member?(x, :string), do: is_binary(x)
  def member?(_x, :any), do: true

  def member?(x, {:subset, s} = set) do
    if set?(x),
      do: Enum.all?(enum(x), &member?(&1, s)),
      else: bad_member(x, set)
  end

  def member?(x, {:fun_set, d, r} = s) do
    if fun?(x),
      do: eq?(domain(x), d) and Enum.all?(enum(domain(x)), &member?(apply_fun(x, &1), r)),
      else: bad_member(x, s)
  end

  def member?(x, {:seq_set, s} = set) do
    case x do
      {:seq, t} -> Enum.all?(Tuple.to_list(t), &member?(&1, s))
      _ -> if fun?(x), do: false, else: bad_member(x, set)
    end
  end

  def member?(x, {:record_set, fields}) do
    case x do
      {:fun, m} ->
        map_size(m) == length(fields) and
          Enum.all?(fields, fn {f, s} -> Map.has_key?(m, f) and member?(Map.fetch!(m, f), s) end)

      {:seq, {}} ->
        fields == []

      {:seq, _} ->
        error(
          "Attempted to check if non-record\n#{show(x)}\nis in the set of records:\n#{show({:record_set, fields})}"
        )

      _ ->
        if fun?(x), do: false, else: bad_member(x, {:record_set, fields})
    end
  end

  def member?(x, {:times, sets}) do
    case x do
      {:seq, t} when tuple_size(t) == length(sets) ->
        sets |> Enum.with_index() |> Enum.all?(fn {s, i} -> member?(elem(t, i), s) end)

      {:fun, m} ->
        if Enum.all?(Map.keys(m), &is_integer/1),
          do: false,
          else:
            error(
              "Attempted to check if non-tuple\n#{show(x)}\nis in the set of tuples:\n#{show({:times, sets})}"
            )

      _ ->
        if fun?(x), do: false, else: bad_member(x, {:times, sets})
    end
  end

  def member?(x, {:ksubset, k, s} = set) do
    cond do
      ksubset_none?(set) -> false
      not set?(x) -> false
      size(x) != k -> false
      true -> Enum.all?(enum(x), &member?(&1, s))
    end
  end

  def member?(x, {:union, s}), do: Enum.any?(enum(s), &member?(x, &1))
  def member?(x, {:diff, a, b}), do: member?(x, a) and not member?(x, b)
  def member?(x, {:cap, a, b}), do: member?(x, a) and member?(x, b)
  def member?(x, {:cup, sets}), do: Enum.any?(sets, &member?(x, &1))
  def member?(x, {:filter, s, pred}), do: member?(x, s) and pred.(x)
  def member?(_x, s), do: error("`\\in` needs a set, not #{show(s)}")

  # TLC compares the value with the elements of the set: a value of
  # another kind cannot be compared. The check uses one element.
  defp not_member(c, s) do
    case first_element(s) do
      nil ->
        false

      e ->
        case {kind(c), kind(e)} do
          {:mv, :mv} ->
            model_values_eq?(c, e)

          {:mv, _} ->
            model_value_other(c, s)

          {_, :mv} ->
            model_value_other(e, c)

          {k, k} ->
            false

          {:other, _} ->
            false

          {_, :other} ->
            false

          # TLC finds a value in a set in normal form (the value of a
          # constant definition) with a binary search: the error of the
          # comparison. In a set expression, TLC compares each element
          # with the value: the error of the equality.
          {k, _} ->
            if normal?(s),
              do: raise(Error, message: compare_message(k, c, e), fingerprint: true),
              else: not eq?(e, c)
        end
    end
  end

  @doc """
  Records the sets in a value of a constant definition: TLC keeps them in
  normal form (sorted), and some errors depend on it.
  """
  def register_normal(v) do
    sets = normal_sets(v, [])

    if sets != [] do
      reg = Process.get(:tla_normal_sets) || MapSet.new()
      Process.put(:tla_normal_sets, Enum.reduce(sets, reg, &MapSet.put(&2, &1)))
    end

    v
  end

  defp normal_sets(%MapSet{} = s, acc) do
    if MapSet.size(s) > 1000, do: [s | acc], else: Enum.reduce(s, [s | acc], &normal_sets/2)
  end

  defp normal_sets({:seq, t}, acc), do: t |> Tuple.to_list() |> Enum.reduce(acc, &normal_sets/2)
  defp normal_sets({:fun, m}, acc), do: m |> Map.values() |> Enum.reduce(acc, &normal_sets/2)
  defp normal_sets(_, acc), do: acc

  defp normal?(s), do: MapSet.member?(Process.get(:tla_normal_sets) || MapSet.new(), s)

  defp compare_message(:int, a, b),
    do: "Attempted to compare integer #{show(a)} with non-integer:\n#{show(b)}"

  defp compare_message(:str, a, b),
    do: "Attempted to compare string #{show(a)} with non-string:\n#{show(b)}"

  defp compare_message(:bool, a, b),
    do: "Attempted to compare boolean #{show(a)} with non-boolean:\n#{show(b)}"

  defp compare_message(:set, a, b),
    do: "Attempted to compare the set #{show(a)} with the value:\n#{show(b)}"

  defp compare_message(:fun, a, b),
    do: "Attempted to compare the function #{show(a)} with the value:\n#{show(b)}"

  defp first_element(%MapSet{map: map}) do
    case :maps.next(:maps.iterator(map)) do
      {e, _, _} -> e
      :none -> nil
    end
  end

  # A value of the wrong kind for a set: an error in TLC, except for an
  # untyped model value (it is not in the set).
  defp bad_member({:mv, _} = x, s) do
    if model_value_type(x),
      do: error("Attempted to check if the typed model value #{show(x)} is in #{show(s)}")

    false
  end

  defp bad_member(x, s),
    do: error("Attempted to check if the value:\n#{show(x)}\nis an element of #{show(s)}")

  # -- Enumeration --

  @doc """
  The elements of a finite set in the normal order of TLC (the order of
  CHOOSE). For a power set, a lazy stream: by size, then in order.
  """
  def ordered({:subset, s} = set) do
    size(set)
    elems = s |> enum() |> sort()

    Stream.flat_map(0..length(elems), fn k ->
      elems |> combinations_stream(k) |> Stream.map(&MapSet.new/1)
    end)
  end

  def ordered(s), do: s |> enum() |> sort()

  defp combinations_stream(_, 0), do: [[]]
  defp combinations_stream([], _), do: []

  defp combinations_stream([h | t], k) do
    Stream.flat_map([true, false], fn
      true -> Stream.map(combinations_stream(t, k - 1), &[h | &1])
      false -> combinations_stream(t, k)
    end)
  end

  @doc "The elements of a set, as a list. Raises for an infinite set."
  # TLC enumerates a set in its normal order. A map of more than 32 keys
  # has no order: sort it (the order of terms is the order of TLC for
  # integers and strings).
  def enum(%MapSet{} = s) do
    list = MapSet.to_list(s)

    cond do
      MapSet.size(s) < 2 -> list
      ranked?(first_element(s)) -> sort(list)
      MapSet.size(s) > 32 -> Enum.sort(list)
      true -> list
    end
  end

  def enum({:interval, a, b} = s) do
    check_interval_size!(s)
    Enum.to_list(a..b)
  end

  def enum({:subset, s} = set) do
    # TLC cannot enumerate a power set of 2^31 elements or more.
    size(set)

    s
    |> enum()
    |> Enum.reverse()
    |> Enum.reduce([MapSet.new()], fn x, acc -> acc ++ Enum.map(acc, &MapSet.put(&1, x)) end)
  end

  def enum({:fun_set, d, r}) do
    cond do
      empty?(d) ->
        [{:seq, {}}]

      empty?(r) ->
        []

      true ->
        values = enum(r)

        d
        |> enum()
        |> Enum.reduce([%{}], fn k, acc -> for m <- acc, v <- values, do: Map.put(m, k, v) end)
        |> Enum.map(&fun/1)
    end
  end

  def enum({:record_set, fields} = s) do
    if empty?(s), do: [], else: enum_fields(fields)
  end

  def enum({:times, sets} = s) do
    if empty?(s), do: [], else: enum_times(sets)
  end

  def enum({:union, s}), do: s |> enum() |> Enum.flat_map(&enum/1) |> Enum.uniq()

  def enum({:ksubset, k, s} = set) do
    cond do
      ksubset_none?(set) -> []
      k == 0 -> [MapSet.new()]
      true -> s |> enum() |> sort() |> combinations(k) |> Enum.map(&MapSet.new/1)
    end
  end

  def enum({:filter, s, pred}) do
    if infinite?(s), do: error("cannot enumerate the infinite set #{show(s)}")
    s |> enum() |> Enum.filter(pred)
  end

  def enum({kind, _, _} = s) when kind in [:diff, :cap],
    do: error("cannot enumerate the infinite set #{show(s)}")

  def enum({:cup, _} = s), do: error("cannot enumerate the infinite set #{show(s)}")

  def enum(s) when s in [:nat, :int, :string, :any, {:seq_set, nil}],
    do: error("cannot enumerate the infinite set #{show(s)}")

  def enum({:seq_set, _} = set),
    do: error("TLC encountered the non-enumerable quantifier bound\n#{show(set)}")

  def enum(v), do: error("expected a set, not #{show(v)}")

  defp enum_fields(fields) do
    fields
    |> Enum.reduce([%{}], fn {f, s}, acc ->
      values = enum(s)
      for m <- acc, v <- values, do: Map.put(m, f, v)
    end)
    |> Enum.map(&fun/1)
  end

  defp enum_times(sets) do
    sets
    |> Enum.reduce([[]], fn s, acc ->
      values = enum(s)
      for l <- acc, v <- values, do: [v | l]
    end)
    |> Enum.map(&(&1 |> Enum.reverse() |> List.to_tuple() |> then(fn t -> {:seq, t} end)))
  end

  @doc "The number of elements of a finite set."
  # TLC sorts the elements to count them: two different sets, one of
  # them not enumerable, cannot be compared.
  def size(%MapSet{} = s) do
    n = MapSet.size(s)

    if n > 1 do
      lazy = Enum.filter(s, &(lazy_set?(&1) and infinite?(&1)))

      if lazy != [] do
        [x | _] = lazy
        other = s |> Enum.reject(&(&1 == x)) |> hd()
        set_eq?(x, other)
      end
    end

    n
  end

  def size({:interval, a, b} = s) do
    check_interval_size!(s)
    max(b - a + 1, 0)
  end

  def size({:subset, s} = set) do
    n = size(s)
    if n >= 31, do: error("Overflow when computing the number of elements in:\n#{show(set)}")
    Integer.pow(2, n)
  end

  # The size of a set of functions: an empty domain gives 1, an empty
  # range 0, and a range of one element 1 (also for an infinite domain).
  def size({:fun_set, d, r}) do
    cond do
      empty?(d) -> 1
      empty?(r) -> 0
      size(r) == 1 -> 1
      true -> checked_product(List.duplicate(size(r), size(d)), {:fun_set, d, r})
    end
  end

  # TLC has 32-bit sizes.
  def size({:times, sets} = s),
    do: if(empty?(s), do: 0, else: checked_product(Enum.map(sets, &size/1), s))

  def size({:record_set, fields} = s),
    do: if(empty?(s), do: 0, else: checked_product(Enum.map(fields, &size(elem(&1, 1))), s))

  def size({:ksubset, k, s} = set) do
    cond do
      ksubset_none?(set) ->
        0

      k == 0 ->
        1

      true ->
        n = size(s)
        c = binomial(n, k)
        if c > 2_147_483_647, do: error("k=#{k} and n=#{n}")
        c
    end
  end

  def size({:seq_set, _} = set),
    do: error("Attempted to compute cardinality of the value\n#{show(set)}")

  def size(s), do: length(enum(s))

  defp checked_product(sizes, s) do
    Enum.reduce(sizes, 1, fn n, acc ->
      p = acc * n

      if p > 2_147_483_647,
        do: error("Overflow when computing the number of elements in #{show_lazy(s)}")

      p
    end)
  end

  defp large?({kind, _, _} = v) when kind in [:ksubset, :fun_set], do: big_size?(v)
  defp large?({kind, _} = v) when kind in [:subset, :record_set, :times], do: big_size?(v)
  defp large?(_), do: false

  defp big_size?(v) do
    case safe_size(v) do
      n when is_integer(n) -> n > 100_000
      _ -> true
    end
  end

  # The checker keeps a small interval as a set of integers: print it as
  # an interval again (TLC keeps the interval).
  defp show_base(%MapSet{} = s) do
    l = s |> MapSet.to_list() |> Enum.sort()

    case l do
      [a | _] when is_integer(a) ->
        b = List.last(l)
        if is_integer(b) and l == Enum.to_list(a..b), do: "#{a}..#{b}", else: show(s)

      _ ->
        show(s)
    end
  end

  defp show_base(s), do: show(s)

  defp ksubset_none?({:ksubset, k, s}), do: k < 0 or (finite?(s) and size(s) < k)

  defp binomial(n, k) when k > n, do: 0

  defp binomial(n, k),
    do: Enum.reduce(1..min(k, n - k)//1, 1, fn i, acc -> div(acc * (n - i + 1), i) end)

  defp combinations(list, k), do: combinations(list, length(list), k)

  defp combinations(_, _, 0), do: [[]]
  defp combinations(_, n, k) when k > n, do: []
  defp combinations(list, n, n), do: [list]

  defp combinations([x | rest], n, k),
    do: Enum.map(combinations(rest, n - 1, k - 1), &[x | &1]) ++ combinations(rest, n - 1, k)

  # TLC has 32-bit sizes.
  defp check_interval_size!({:interval, a, b}) do
    if b - a + 1 > 2_147_483_647,
      do:
        error(
          "Size of interval value exceeds the maximum representable size (32bits): #{a}..#{b}."
        )
  end

  # -- Set operations --

  @doc """
  Checks that the elements of a finite set can be sorted with the rules of
  TLC: elements of different kinds (an integer and a string, for example)
  cannot. TLC sorts a set when an operation makes a new set from it (but
  not for a set literal), so a set with elements of different kinds is an
  error there. Gives the set.
  """
  def normalize!(%MapSet{} = s) do
    if MapSet.size(s) > 1 do
      kinds =
        Enum.reduce_while(s, nil, fn x, acc ->
          case {kind(x), acc} do
            {:mv, _} -> {:cont, acc}
            {:other, _} -> {:cont, acc}
            {k, nil} -> {:cont, {k, x}}
            {k, {k, _}} -> {:cont, acc}
            {_k, {k0, x0}} -> {:halt, {:mixed, k0, x0, x}}
          end
        end)

      case kinds do
        {:mixed, k0, x0, x} -> raise Error, message: compare_message(k0, x0, x)
        _ -> s
      end
    else
      s
    end
  end

  def normalize!(s), do: s

  # A set operation on two sets compares the elements of one with the
  # elements of the other (TLC): elements of different kinds are an error.
  # Gives the first set.
  defp cross_check!(a, b) do
    if MapSet.size(a) > 0 and MapSet.size(b) > 0, do: normalize!(MapSet.union(a, b))
    a
  end

  @doc "`normalize!/1` for all the sets in a value (TLC sorts them to print it)."
  def deep_normalize!(%MapSet{} = s) do
    normalize!(s)
    Enum.each(s, &deep_normalize!/1)
    s
  end

  def deep_normalize!({:seq, t} = v) do
    t |> Tuple.to_list() |> Enum.each(&deep_normalize!/1)
    v
  end

  def deep_normalize!({:fun, m} = v) do
    m |> Map.keys() |> MapSet.new() |> normalize!()
    Enum.each(m, fn {k, x} -> deep_normalize!(k) && deep_normalize!(x) end)
    v
  end

  def deep_normalize!(v), do: v

  def union(a, b) do
    cond do
      not infinite?(a) and not infinite?(b) ->
        cross_check!(to_set(a), to_set(b))
        MapSet.union(to_set(a), to_set(b))

      # S \cup {} is S (also for an infinite S).
      empty?(b) ->
        a

      empty?(a) ->
        b

      true ->
        {:cup, [a, b]}
    end
  end

  def intersection(a, b) do
    case {infinite?(a), infinite?(b)} do
      {false, false} -> MapSet.intersection(cross_check!(to_set(a), to_set(b)), to_set(b))
      {false, true} -> a |> to_set() |> MapSet.filter(&member?(&1, b))
      {true, false} -> b |> to_set() |> MapSet.filter(&member?(&1, a))
      {true, true} -> {:cap, a, b}
    end
  end

  def difference(a, b) when not is_struct(a, MapSet) do
    if infinite?(a), do: {:diff, a, b}, else: difference(to_set(a), b)
  end

  def difference(%MapSet{} = a, b) do
    if match?(%MapSet{}, b), do: cross_check!(a, b)

    if match?(%MapSet{}, b),
      do: MapSet.difference(a, b),
      else: MapSet.reject(a, &member?(&1, b))
  end

  # SUBSET A \\subseteq SUBSET B is A \\subseteq B (no enumeration of the
  # power sets).
  def subseteq?({:subset, a}, {:subset, b}), do: subseteq?(a, b)

  def subseteq?(a, b) do
    normalize!(a)
    normalize!(b)
    Enum.all?(enum(a), &member?(&1, b))
  end

  @doc "A finite set as a MapSet."
  def to_set(%MapSet{} = s), do: s
  def to_set(s), do: MapSet.new(enum(s))

  # -- Functions --

  @doc "`f[x]`."
  def apply_fun({:seq, t}, i) when is_integer(i) and i >= 1 and i <= tuple_size(t),
    do: elem(t, i - 1)

  def apply_fun({:fun, m} = f, x) do
    case Map.fetch(m, canon(x)) do
      {:ok, v} ->
        v

      :error ->
        # TLC compares the argument with each element of the domain (in
        # order): an element of another kind gives an error.
        m |> Map.keys() |> sort() |> Enum.each(&eq?(&1, x))
        error("#{show(x)} is not in the domain of #{show(f)}")
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

  def update({:lazy_fun, d, g} = f, x, v) do
    if infinite?(d) do
      k = canon(x)
      v = canon(v)
      {:lazy_fun, d, fn y -> if canon(y) == k, do: v, else: g.(y) end}
    else
      update(canon(f), x, v)
    end
  end

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

  def sort(values), do: Enum.sort_by(values, &sort_key/1)

  @doc """
  The rank of a string (or of the name of a model value): TLC orders them
  by the order in which it first made them (see
  `Accord.TLA.Checker.Context`). A string that is new gets the next rank.
  """
  def rank(s) do
    ranks = Process.get(:tla_string_ranks) || %{}

    case ranks do
      %{^s => r} ->
        r

      _ ->
        r = map_size(ranks)
        Process.put(:tla_string_ranks, Map.put(ranks, s, r))
        r
    end
  end

  # -- The order of the fields of records --

  # TLC keeps a record (or a function that `@@` makes) in the order of
  # its construction until it puts the record in normal form (in a state,
  # or in a sorted set). The checker keeps the order of construction of
  # each set of fields: `show/1` uses it, `show_normal/1` does not.
  @max_orders 10_000

  @doc "Records the order of construction of the keys of a function."
  def note_order(keys) when length(keys) > 1 and length(keys) <= 32 do
    orders = Process.get(:tla_field_orders) || %{}
    key = Enum.sort(keys)

    if map_size(orders) < @max_orders and not Map.has_key?(orders, key),
      do: Process.put(:tla_field_orders, Map.put(orders, key, keys))

    :ok
  end

  def note_order(_keys), do: :ok

  @doc "The keys of a function in the order of its construction (when known)."
  def written_keys(f) do
    keys = f |> pairs() |> Enum.map(&elem(&1, 0))

    case Map.get(Process.get(:tla_field_orders) || %{}, Enum.sort(keys)) do
      nil -> Enum.sort_by(keys, &sort_key/1)
      written -> written
    end
  end

  defp order_pairs(pairs) do
    written =
      if Process.get(:tla_show_normal),
        do: nil,
        else:
          Map.get(
            Process.get(:tla_field_orders) || %{},
            pairs |> Enum.map(&elem(&1, 0)) |> Enum.sort()
          )

    case written do
      nil ->
        Enum.sort_by(pairs, &sort_key(elem(&1, 0)))

      keys ->
        m = Map.new(pairs)
        Enum.map(keys, &{&1, Map.fetch!(m, &1)})
    end
  end

  @doc """
  Tells if the enumeration of a lazy set cannot give an error: a power
  set or a product of finite sets whose elements have one kind.
  """
  def safe_lazy?(v), do: safe_parts?(v) and sized?(v)

  defp safe_parts?({:subset, s}), do: safe_part?(s)
  defp safe_parts?({:ksubset, _, s}), do: safe_part?(s)
  defp safe_parts?({:fun_set, d, r}), do: safe_part?(d) and safe_part?(r)
  defp safe_parts?({:record_set, fields}), do: Enum.all?(fields, fn {_, s} -> safe_part?(s) end)
  defp safe_parts?({:times, sets}), do: Enum.all?(sets, &safe_part?/1)
  defp safe_parts?(_), do: false

  # The size has no overflow (TLC enumerates the set).
  defp sized?(v) do
    size(v)
    true
  rescue
    Error -> false
  end

  defp safe_part?(%MapSet{} = s) do
    normalize!(s)
    true
  rescue
    Error -> false
  end

  defp safe_part?({:interval, _, _}), do: true
  defp safe_part?(s), do: safe_parts?(s) and sized?(s)

  @doc "Writes a value in normal form, as TLC prints the values of a state."
  def show_normal(v), do: normal(fn -> show(v) end)

  defp normal(fun) do
    old = Process.get(:tla_show_normal)
    Process.put(:tla_show_normal, true)

    try do
      fun.()
    after
      Process.put(:tla_show_normal, old)
    end
  end

  # Values whose order in TLC is not the order of Erlang terms (they
  # contain strings or model values).
  defp ranked?(v) when is_binary(v), do: true
  defp ranked?({:mv, _}), do: true
  defp ranked?({:seq, t}), do: tuple_size(t) > 0 and ranked?(elem(t, 0))

  defp ranked?({:fun, m}) do
    case :maps.next(:maps.iterator(m)) do
      {k, v, _} -> ranked?(k) or ranked?(v)
      :none -> false
    end
  end

  defp ranked?(%MapSet{} = s), do: MapSet.size(s) > 0 and ranked?(first_element(s))
  defp ranked?(_), do: false

  # The order of TLC: a model value is less than any other value; strings
  # (and model values) go in the order of `rank/1`; sets by size, then
  # elements; functions (and tuples and records) by size, then domain,
  # then values.
  defp sort_key(v) when is_boolean(v), do: {3, v}
  defp sort_key(v) when is_integer(v), do: {0, v}
  defp sort_key(v) when is_binary(v), do: {1, rank(v)}
  defp sort_key({:mv, n}), do: {-1, rank(n)}

  defp sort_key(%MapSet{} = s),
    do: {4, MapSet.size(s), s |> MapSet.to_list() |> Enum.map(&sort_key/1) |> Enum.sort()}

  defp sort_key({:seq, t}) do
    n = tuple_size(t)
    {6, n, Enum.map(1..n//1, &{0, &1}), t |> Tuple.to_list() |> Enum.map(&sort_key/1)}
  end

  defp sort_key({:fun, m}) do
    pairs = m |> Enum.map(fn {k, v} -> {sort_key(k), v} end) |> Enum.sort_by(&elem(&1, 0))
    {6, map_size(m), Enum.map(pairs, &elem(&1, 0)), Enum.map(pairs, &sort_key(elem(&1, 1)))}
  end

  defp sort_key(other), do: {9, inspect(other)}

  # -- Printing --

  @doc "Writes a value in the form that TLC prints."
  def show(true), do: "TRUE"
  def show(false), do: "FALSE"
  def show(n) when is_integer(n), do: Integer.to_string(n)
  def show(s) when is_binary(s), do: inspect(s)
  def show({:mv, n}), do: n

  def show(%MapSet{} = s) do
    elems = s |> MapSet.to_list() |> sort()
    # TLC sorts a set of two or more elements to print it: the records in
    # it are in normal form (see `show_normal/1`).
    shown =
      if length(elems) > 1,
        do: normal(fn -> Enum.map(elems, &show/1) end),
        else: Enum.map(elems, &show/1)

    "{" <> Enum.join(shown, ", ") <> "}"
  end

  def show({:seq, t}), do: "<<" <> (t |> Tuple.to_list() |> Enum.map_join(", ", &show/1)) <> ">>"

  def show({:fun, m}) do
    pairs = m |> Map.to_list() |> order_pairs()

    if Enum.all?(Map.keys(m), &is_binary/1) do
      "[" <> Enum.map_join(pairs, ", ", fn {k, v} -> "#{k} |-> #{show(v)}" end) <> "]"
    else
      "(" <> Enum.map_join(pairs, " @@ ", fn {k, v} -> "#{show(k)} :> #{show(v)}" end) <> ")"
    end
  end

  def show({:interval, a, b}), do: "#{a}..#{b}"
  def show(:nat), do: "Nat"
  def show(:int), do: "Int"
  def show(:string), do: "STRING"
  def show(:any), do: "the set of all values"
  # As TLC: a set of records, tuples, or functions with fewer than 2000
  # elements prints as its elements; a larger one prints in its lazy form.
  # The sizes come from the parts, in order (an error when a part has no
  # size).
  def show({:record_set, fields} = s),
    do: show_sized(s, product_size(Enum.map(fields, &elem(&1, 1))))

  def show({:times, sets} = s), do: show_sized(s, product_size(sets))

  def show({:fun_set, d, r} = s) do
    sz =
      if empty?(d) do
        1
      else
        dsz = size(d)
        rsz = size(r)

        Enum.reduce_while(1..dsz//1, 1, fn _, acc ->
          if acc <= 2_147_483_647, do: {:cont, acc * rsz}, else: {:halt, acc}
        end)
      end

    show_sized(s, sz)
  end

  def show({:ksubset, k, s} = set) do
    n = size(set)

    cond do
      n == 0 -> "{}"
      n < 64 -> set |> enum() |> MapSet.new() |> show()
      true -> "{s \\in SUBSET (#{show_base(s)}) : Cardinality(s) = #{k}}"
    end
  end

  def show({:subset, s}), do: "SUBSET #{show(s)}"
  def show({:seq_set, s}), do: "Seq(#{show(s)})"
  def show({:union, s}), do: "UNION #{show(s)}"

  def show({:diff, a, b}), do: "(#{show(a)} \\ #{show(b)})"
  def show({:cap, a, b}), do: "(#{show(a)} \\cap #{show(b)})"
  def show({:cup, sets}), do: "(" <> Enum.map_join(sets, " \\cup ", &show/1) <> ")"
  def show({:filter, s, _}), do: "{x \\in #{show(s)} : ...}"
  def show({:lazy_fun, d, _}), do: "[x \\in #{show(d)} |-> ...]"
  def show({:op_value, name, _, _}), do: "operator #{name}"
  def show(other), do: inspect(other)

  defp show_sized(s, sz),
    do: if(sz < 2000, do: s |> enum() |> MapSet.new() |> show(), else: show_lazy(s))

  defp product_size(parts) do
    Enum.reduce_while(parts, 1, fn p, acc ->
      case size(p) do
        0 -> {:halt, 0}
        n -> {:cont, if(acc <= 2_147_483_647, do: acc * n, else: acc)}
      end
    end)
  end

  defp show_lazy({:fun_set, d, r}), do: "[#{show(d)} -> #{show(r)}]"
  defp show_lazy({:times, sets}), do: "(" <> Enum.map_join(sets, " \\X ", &show/1) <> ")"

  defp show_lazy({:record_set, fields}),
    do: "[" <> Enum.map_join(fields, ", ", fn {f, s} -> "#{f}: #{show(s)}" end) <> "]"

  @doc "Raises an evaluation error."
  @spec error(String.t()) :: no_return()
  def error(message), do: raise(Error, message: message)
end
