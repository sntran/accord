defmodule Accord.TLA.Checker.Random do
  @moduledoc """
  The random values of TLC (`RandomElement`, the `Randomization`
  module), with the same algorithms and the same random number generator
  (`java.util.Random`) as TLC. With the same seed, the checker gets the
  same values as TLC with one worker.

  As in TLC, the evaluation of the constants and of the initial states
  uses one stream of numbers from the seed of the run. In the next-state
  relation, the stream of a state starts again from the seed XOR the
  fingerprint of the state (see `Accord.TLA.Checker.Fingerprint`). Thus
  the successors of a state do not depend on the order of the search.

  The state of the generator is in the process dictionary.
  """

  import Bitwise

  alias Accord.TLA.Checker.{Fingerprint, Value}
  import Value, only: [error: 1]

  @multiplier 0x5DEECE66D
  @mask48 (1 <<< 48) - 1

  # tlc2.util.RandomGenerator.primes: all the primes in this range.
  @primes 1_277_011..1_295_953
          |> Enum.filter(fn n -> Enum.all?(2..trunc(:math.sqrt(n)), &(rem(n, &1) != 0)) end)
          |> List.to_tuple()

  # -- The generator --

  @doc """
  Starts the generator of a run with `seed` (a random seed when it is
  `nil`, as TLC without `-seed`).
  """
  def setup(seed \\ nil) do
    seed = seed || :rand.uniform(1 <<< 62)
    Process.put(:tla_random, %{seed: seed, s: scramble(seed), at: nil})
    Process.delete(:tla_random_state)
    :ok
  end

  @doc "The seed of the run."
  def seed, do: generator().seed

  @doc """
  Sets the state of the next-state relation: `id` identifies the state,
  `values` are the values of its variables. `nil` for the initial states.
  """
  def at_state(nil), do: Process.delete(:tla_random_state)
  def at_state({_id, _values} = current), do: Process.put(:tla_random_state, current)

  defp generator do
    g =
      case Process.get(:tla_random) do
        nil ->
          setup()
          Process.get(:tla_random)

        g ->
          g
      end

    case Process.get(:tla_random_state) do
      {id, values} when g.at != id ->
        seed = bxor(Fingerprint.state(values), g.seed)
        %{g | s: scramble(seed), at: id}

      _ ->
        g
    end
  end

  defp scramble(seed), do: bxor(seed, @multiplier) &&& @mask48

  # java.util.Random#next(bits): a signed 32-bit value for bits = 32.
  defp next(bits) do
    g = generator()
    {r, s} = step(g.s, bits)
    Process.put(:tla_random, %{g | s: s})
    r
  end

  defp step(s, bits) do
    s = s * @multiplier + 0xB &&& @mask48
    r = s >>> (48 - bits)
    {if(bits == 32 and r >= 0x80000000, do: r - 0x100000000, else: r), s}
  end

  @doc "java.util.Random#nextDouble."
  def next_double, do: double(&next/1)

  defp double(next) do
    a = next.(26)
    b = next.(27)
    ((a <<< 27) + b) * :math.pow(2, -53)
  end

  # -- A second generator: the choices of the simulation --

  # TLC's simulator has its own java.util.Random for its choices (the
  # initial state, the action, the successor), apart from the generator
  # of the random values.

  @doc "Starts the generator of the choices with `seed`."
  def choice_setup(seed), do: Process.put(:tla_random_choice, scramble(seed))

  defp choice_next(bits) do
    {r, s} = step(Process.get(:tla_random_choice), bits)
    Process.put(:tla_random_choice, s)
    r
  end

  @doc "nextDouble of the generator of the choices."
  def choice_double, do: double(&choice_next/1)

  @doc "nextLong of the generator of the choices."
  def choice_long, do: int64((choice_next(32) <<< 32) + choice_next(32))

  @doc "RandomGenerator.nextPrime of the generator of the choices."
  def choice_prime, do: prime(&choice_double/0)

  @doc "A java.util.Random(seed).nextLong(), as TLC's simulator makes the seed of a worker."
  def first_long(seed) do
    s = scramble(seed)
    {hi, s} = step(s, 32)
    {lo, _} = step(s, 32)
    int64((hi <<< 32) + lo)
  end

  @doc "java.util.Random#nextInt(bound)."
  def next_int(bound) when bound > 0 do
    r = next(31)
    m = bound - 1

    if (bound &&& m) == 0 do
      (bound * r) >>> 31
    else
      next_int_loop(r, bound, m)
    end
  end

  defp next_int_loop(u, bound, m) do
    r = rem(u, bound)
    # u - r + m < 0 in 32-bit arithmetic.
    if int32(u - r + m) < 0, do: next_int_loop(next(31), bound, m), else: r
  end

  @doc "java.util.Random#nextLong."
  def next_long do
    hi = next(32)
    lo = next(32)
    int64((hi <<< 32) + lo)
  end

  defp int32(x) do
    x = x &&& 0xFFFFFFFF
    if x >= 0x80000000, do: x - 0x100000000, else: x
  end

  defp int64(x) do
    x = x &&& 0xFFFFFFFFFFFFFFFF
    if x >= 0x8000000000000000, do: x - 0x10000000000000000, else: x
  end

  # RandomGenerator.nextPrime.
  defp next_prime, do: prime(&next_double/0)

  defp prime(double) do
    n = tuple_size(@primes)

    index =
      Enum.reduce_while(Stream.repeatedly(fn -> nil end), n, fn _, _ ->
        i = floor(double.() * n)
        if i == n, do: {:cont, n}, else: {:halt, i}
      end)

    elem(@primes, index)
  end

  # -- TLC!RandomElement --

  @doc "TLC!RandomElement(s)."
  def element({:fun_set, d, r}) do
    keys = d |> Value.normalize!() |> enum_sorted()
    Value.fun(Map.new(keys, fn k -> {Value.canon(k), element(r)} end))
  end

  def element({:record_set, fields}) do
    fields
    |> Enum.sort_by(&elem(&1, 0), &(Value.compare(&1, &2) != :gt))
    |> Enum.map(fn {name, s} -> {name, element(s)} end)
    |> Value.record()
  end

  def element({:times, sets}), do: sets |> Enum.map(&element/1) |> Value.tuple()

  def element({:interval, a, b}) do
    n = max(b - a + 1, 0)
    i = floor(next_double() * n)

    if i < n,
      do: a + i,
      else:
        error(
          "Attempted to retrieve out-of-bounds element from the interval value #{Value.show({:interval, a, b})}."
        )
  end

  def element(s) do
    if Value.infinite?(s),
      do:
        error(
          "The argument of RandomElement should be a finite set, but instead it is:\n#{Value.show(s)}"
        )

    elems = s |> Value.normalize!() |> enum_sorted() |> List.to_tuple()
    n = tuple_size(elems)
    i = floor(next_double() * n)
    if i < n, do: elem(elems, i), else: error("RandomElement of the empty set")
  end

  # -- Randomization!RandomSubset --

  @doc "Randomization!RandomSubset(k, s): `k` elements of `s` (TLC's getRandomSubset)."
  def subset(k, s) when k < 0, do: subset_negative(k, s)

  def subset(k, {kind, _, _} = s) when kind == :fun_set, do: product_subset(k, s)
  def subset(k, {kind, _} = s) when kind in [:record_set, :times], do: product_subset(k, s)

  def subset(k, {:interval, a, b}) do
    n = max(b - a + 1, 0)
    k |> indexes(n) |> Enum.map(&(a + &1)) |> Value.set()
  end

  def subset(k, s) do
    elems = s |> Value.normalize!() |> enum_sorted() |> List.to_tuple()
    k |> indexes(tuple_size(elems)) |> Enum.map(&elem(elems, &1)) |> Value.set()
  end

  # TLC makes a vector with a negative capacity.
  defp subset_negative(k, _s), do: error("#{k}")

  # EnumerableValue.SubsetEnumerator: k indexes in 0..n-1, from a linear
  # congruential generator with the period m >= n.
  defp indexes(_k, n) when n <= 0, do: []

  defp indexes(k, n) do
    {m, a} = lcg(n)
    index = next_int(n)
    c = next_prime()

    {list, _} =
      Enum.map_reduce(1..k//1, index, fn _, x ->
        x = lcg_next(x, a, c, m, n)
        {x, x}
      end)

    list
  end

  defp lcg_next(x, a, c, m, n) do
    x = rem(a * x + c, m)
    if x >= n, do: lcg_next(x, a, c, m, n), else: x
  end

  # EnumerableValue.computeOptimalMandA: the smallest m >= max(n, 9) that
  # is not a multiple of 4 and not square-free; a - 1 is the product of
  # the prime factors of m.
  defp lcg(n) do
    key = {:tla_lcg, n}

    case Process.get(key) do
      nil ->
        v = lcg_search(max(n, 9))
        Process.put(key, v)
        v

      v ->
        v
    end
  end

  defp lcg_search(n) do
    factors = prime_factors(n)
    distinct = Enum.uniq(factors)

    if rem(n, 4) == 0 or length(distinct) == length(factors),
      do: lcg_search(n + 1),
      else: {n, Enum.product(distinct) + 1}
  end

  defp prime_factors(n), do: prime_factors(n, 2, [])
  defp prime_factors(1, _, acc), do: acc
  defp prime_factors(n, p, acc) when p * p > n, do: [n | acc]

  defp prime_factors(n, p, acc) do
    if rem(n, p) == 0,
      do: prime_factors(div(n, p), p, [p | acc]),
      else: prime_factors(n, p + 1, acc)
  end

  # SetOfFcnsOrRcdsValue: an index in the mixed radix of the sizes of the
  # constituent sets gives one element.
  defp product_subset(k, s) do
    if Value.empty?(s) do
      MapSet.new()
    else
      {constituents, build} = product(s)
      sizes = Enum.map(constituents, &tuple_size/1)
      total = Enum.product(sizes)

      idxs =
        if total > 0x7FFFFFFF do
          # BigIntegerSubsetEnumerator: (x * i + a) mod size.
          a = abs(next_long())
          x = 0x7FFFFFFFFFFFFFFF - 24
          for i <- 0..(k - 1)//1, do: Integer.mod(x * i + a, total)
        else
          indexes(k, total)
        end

      idxs |> Enum.map(&build.(element_at(&1, constituents, sizes))) |> Value.set()
    end
  end

  defp element_at(idx, constituents, sizes) do
    {values, _} =
      constituents
      |> Enum.zip(sizes)
      |> Enum.reverse()
      |> Enum.map_reduce(idx, fn {c, size}, rest ->
        {elem(c, rem(rest, size)), div(rest, size)}
      end)

    Enum.reverse(values)
  end

  defp product({:fun_set, d, r}) do
    keys = d |> Value.normalize!() |> enum_sorted()
    range = r |> enum_sorted() |> List.to_tuple()

    {List.duplicate(range, length(keys)),
     fn values -> Value.fun(Map.new(Enum.zip(Enum.map(keys, &Value.canon/1), values))) end}
  end

  defp product({:record_set, fields}) do
    fields = Enum.sort_by(fields, &elem(&1, 0), &(Value.compare(&1, &2) != :gt))
    names = Enum.map(fields, &elem(&1, 0))

    {Enum.map(fields, fn {_, s} -> s |> enum_sorted() |> List.to_tuple() end),
     fn values -> Value.record(Enum.zip(names, values)) end}
  end

  defp product({:times, sets}) do
    {Enum.map(sets, fn s -> s |> enum_sorted() |> List.to_tuple() end), &Value.tuple/1}
  end

  # -- Randomization!RandomSetOfSubsets and RandomSubsetSet --

  @doc """
  `k` picks of a subset of `s`: each element is in a pick with the
  probability `p` (TLC's CoinTossingSubsetEnumerator).
  """
  def set_of_subsets(k, p, s) do
    elems = s |> Value.normalize!() |> enum_sorted()

    for _ <- 1..k//1, into: MapSet.new() do
      elems |> Enum.filter(fn _ -> next_double() < p end) |> Value.set()
    end
  end

  defp enum_sorted(s), do: s |> Value.enum() |> Value.sort()
end
