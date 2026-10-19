defmodule Accord.TLA.Checker.Fingerprint do
  @moduledoc """
  The 64-bit fingerprints of TLC (`tlc2.util.FP64` with the first
  polynomial, as `-fp 0`) for values and states.

  The checker does not use these fingerprints to find the states that it
  saw. It uses them as TLC does to seed the random values of the
  next-state relation (see `Accord.TLA.Checker.Random`): the seed is the
  fingerprint of the current state XOR the seed of the run.

  Two parts are not the same as in TLC: TLC orders strings (and the
  fields of records) by the order in which its parser first saw them,
  and the fingerprint of a model value uses that order too. The checker
  orders strings by their text, and uses a hash of the name of a model
  value.
  """

  import Bitwise

  alias Accord.TLA.Checker.Value

  @mask64 0xFFFFFFFFFFFFFFFF

  # The first polynomial of FP64.Polys.
  @poly 0x911498AE0E66BAD6

  @table (fn ->
            one = 0x8000000000000000

            powers =
              Enum.scan(1..71, one, fn _, t ->
                mask = if (t &&& 1) != 0, do: @poly, else: 0
                bxor(t >>> 1, mask)
              end)

            powers = List.to_tuple([one | powers])

            for j <- 0..255 do
              Enum.reduce(0..7, 0, fn k, v ->
                if (j &&& 1 <<< k) != 0, do: bxor(v, elem(powers, 127 - 56 - k)), else: v
              end)
            end
            |> List.to_tuple()
          end).()

  # The kinds of values (tlc2.value.ValueConstants).
  @bool 0
  @int 1
  @string 3
  @set 5
  @fcn 9
  @model 21

  @doc "The fingerprint of nothing (FP64.New())."
  def new, do: @poly

  @doc "The fingerprint of a state (the values of the variables, in order)."
  def state(values) when is_tuple(values), do: state(Tuple.to_list(values))

  def state(values) when is_list(values) do
    Enum.reduce(values, @poly, &value(&2, &1))
  end

  def state(values) when is_map(values) do
    values |> Enum.sort() |> Enum.map(&elem(&1, 1)) |> state()
  end

  @doc "Extends the fingerprint `fp` with the value `v`."
  def value(fp, true), do: fp |> byte(@bool) |> byte(?t)
  def value(fp, false), do: fp |> byte(@bool) |> byte(?f)
  def value(fp, n) when is_integer(n), do: fp |> byte(@int) |> int(n)

  def value(fp, s) when is_binary(s) do
    chars = String.to_charlist(s)
    len = Enum.reduce(chars, 0, fn c, n -> if c > 0xFFFF, do: n + 2, else: n + 1 end)
    fp = fp |> byte(@string) |> int(len)
    Enum.reduce(chars, fp, &byte(&2, &1 &&& 0xFF))
  end

  def value(fp, {:mv, name}), do: fp |> byte(@model) |> int(:erlang.phash2(name))

  def value(fp, %MapSet{} = s) do
    elems = s |> MapSet.to_list() |> Value.sort()
    fp = fp |> byte(@set) |> int(length(elems))
    Enum.reduce(elems, fp, &value(&2, &1))
  end

  def value(fp, {:seq, t}) do
    fp = fp |> byte(@fcn) |> int(tuple_size(t))

    t
    |> Tuple.to_list()
    |> Enum.with_index(1)
    |> Enum.reduce(fp, fn {v, i}, fp -> fp |> byte(@int) |> int(i) |> value(v) end)
  end

  def value(fp, {:fun, m}) do
    keys = m |> Map.keys() |> Value.sort()
    fp = fp |> byte(@fcn) |> int(length(keys))
    Enum.reduce(keys, fp, fn k, fp -> fp |> value(k) |> value(Map.fetch!(m, k)) end)
  end

  def value(fp, v) do
    case Value.canon(v) do
      ^v -> value(fp, Value.to_set(v))
      c -> value(fp, c)
    end
  end

  # FP64.Extend(fp, byte).
  defp byte(fp, b) do
    bxor(fp >>> 8, elem(@table, bxor(b, fp) &&& 0xFF)) &&& @mask64
  end

  # FP64.Extend(fp, int): the four bytes, low byte first.
  defp int(fp, x) do
    x = x &&& 0xFFFFFFFF

    fp
    |> byte(x &&& 0xFF)
    |> byte(x >>> 8 &&& 0xFF)
    |> byte(x >>> 16 &&& 0xFF)
    |> byte(x >>> 24 &&& 0xFF)
  end
end
