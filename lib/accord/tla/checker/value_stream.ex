defmodule Accord.TLA.Checker.ValueStream do
  @moduledoc """
  The binary format of TLC for values (`.vos` files of
  `IOUtils!IOSerialize` and `IOUtils!IODeserialize`).

  Each value starts with a kind byte. Integers are 32-bit big-endian. A
  string has two integers that TLC does not use when it reads a file,
  the length, and the bytes. A set, a record, a function, and a tuple
  give their elements. A value that occurs again is a reference to its
  first occurrence (kind 26 and an index).

  The writer does not write references, and it cannot write model
  values (their index is local to a TLC process).
  """

  alias Accord.TLA.Checker.Value
  import Value, only: [error: 1]

  @bool 0
  @int 1
  @string 3
  @record 4
  @set 5
  @tuple 7
  @fcn 9
  @model 21
  @interval 23
  @dummy 26

  @doc "Reads one value from a binary. With `compressed`, the binary is gzip data."
  def decode(binary, compressed \\ false) do
    binary = if compressed, do: :zlib.gunzip(binary), else: binary
    {value, _rest, _handles} = read(binary, %{})
    value
  rescue
    e in [MatchError, FunctionClauseError, ErlangError] ->
      error("IODeserialize: the file is not a TLC value stream (#{Exception.message(e)})")
  end

  @doc "Writes one value as a binary. With `compressed`, gzip data."
  def encode(value, compressed \\ false) do
    binary = value |> write() |> IO.iodata_to_binary()
    if compressed, do: :zlib.gzip(binary), else: binary
  end

  # -- Reading --

  defp read(<<@bool, b, rest::binary>>, h), do: {b != 0, rest, h}
  defp read(<<@int, n::signed-32, rest::binary>>, h), do: {n, rest, h}

  defp read(<<@string, rest::binary>>, h) do
    {s, rest} = read_unique_string(rest)
    {s, rest, assign(h, s)}
  end

  defp read(<<@interval, a::signed-32, b::signed-32, rest::binary>>, h),
    do: {Value.interval(a, b), rest, h}

  defp read(<<@model, _::16, _::binary>>, _h),
    do: error("IODeserialize: model values in a value stream are not supported")

  defp read(<<@set, len::signed-32, rest::binary>>, h) do
    {idx, h} = reserve(h)
    {elems, rest, h} = read_n(rest, abs(len), h)
    v = Value.set(elems)
    {v, rest, Map.put(h, idx, v)}
  end

  defp read(<<@tuple, rest::binary>>, h) do
    {idx, h} = reserve(h)
    {len, rest} = read_nat(rest)
    {elems, rest, h} = read_n(rest, len, h)
    v = Value.tuple(elems)
    {v, rest, Map.put(h, idx, v)}
  end

  defp read(<<@record, len::signed-32, rest::binary>>, h) do
    {idx, h} = reserve(h)

    {fields, rest, h} =
      Enum.reduce(1..abs(len)//1, {[], rest, h}, fn _, {acc, rest, h} ->
        {name, rest, h} =
          case rest do
            <<@dummy, rest::binary>> ->
              {i, rest} = read_nat(rest)
              {Map.fetch!(h, i), rest, h}

            <<_kind, rest::binary>> ->
              {i, h} = reserve(h)
              {name, rest} = read_unique_string(rest)
              {name, rest, Map.put(h, i, name)}
          end

        {v, rest, h} = read(rest, h)
        {[{name, v} | acc], rest, h}
      end)

    v = Value.record(Enum.reverse(fields))
    {v, rest, Map.put(h, idx, v)}
  end

  defp read(<<@fcn, rest::binary>>, h) do
    {idx, h} = reserve(h)
    {len, rest} = read_nat(rest)

    {v, rest, h} =
      case rest do
        <<0, low::signed-32, _high::signed-32, rest::binary>> ->
          {values, rest, h} = read_n(rest, len, h)
          keys = Enum.to_list(low..(low + len - 1)//1)
          {Value.fun(Map.new(Enum.zip(keys, values))), rest, h}

        <<_info, rest::binary>> ->
          {pairs, rest, h} = read_n(rest, 2 * len, h)
          map = pairs |> Enum.chunk_every(2) |> Map.new(fn [k, v] -> {Value.canon(k), v} end)
          {Value.fun(map), rest, h}
      end

    {v, rest, Map.put(h, idx, v)}
  end

  defp read(<<@dummy, rest::binary>>, h) do
    {i, rest} = read_nat(rest)
    {Map.fetch!(h, i), rest, h}
  end

  defp read(<<kind, _::binary>>, _h),
    do: error("IODeserialize: a value of kind #{kind} is not supported")

  defp read_n(rest, n, h) do
    {acc, rest, h} =
      Enum.reduce(1..n//1, {[], rest, h}, fn _, {acc, rest, h} ->
        {v, rest, h} = read(rest, h)
        {[v | acc], rest, h}
      end)

    {Enum.reverse(acc), rest, h}
  end

  defp read_unique_string(<<_tok::32, _loc::32, len::signed-32, rest::binary>>) do
    <<bytes::binary-size(len), rest::binary>> = rest
    {bytes, rest}
  end

  defp read_nat(<<n::signed-16, rest::binary>>) when n >= 0, do: {n, rest}

  defp read_nat(<<hi::signed-16, lo::16, rest::binary>>) do
    import Bitwise
    {-(hi <<< 16 ||| lo), rest}
  end

  # The handle table: each object gets the next index.
  defp reserve(h) do
    idx = Map.get(h, :next, 0)
    {idx, Map.put(h, :next, idx + 1)}
  end

  defp assign(h, v) do
    {idx, h} = reserve(h)
    Map.put(h, idx, v)
  end

  # -- Writing --

  defp write(true), do: <<@bool, 1>>
  defp write(false), do: <<@bool, 0>>
  defp write(n) when is_integer(n), do: <<@int, n::signed-32>>
  defp write(s) when is_binary(s), do: [<<@string>>, unique_string(s)]

  defp write(%MapSet{} = s) do
    elems = s |> MapSet.to_list() |> Value.sort()
    [<<@set, length(elems)::signed-32>> | Enum.map(elems, &write/1)]
  end

  defp write({:seq, t}) do
    elems = Tuple.to_list(t)
    [<<@tuple>>, nat(length(elems)) | Enum.map(elems, &write/1)]
  end

  defp write({:fun, m}) do
    pairs = Enum.sort_by(Map.to_list(m), &elem(&1, 0), &(Value.compare(&1, &2) != :gt))

    if Enum.all?(pairs, fn {k, _} -> is_binary(k) end) do
      [
        <<@record, length(pairs)::signed-32>>
        | Enum.map(pairs, fn {k, v} -> [<<@string>>, unique_string(k), write(v)] end)
      ]
    else
      [
        <<@fcn>>,
        nat(length(pairs)),
        <<1>> | Enum.map(pairs, fn {k, v} -> [write(k), write(v)] end)
      ]
    end
  end

  defp write({:interval, a, b}), do: <<@interval, a::signed-32, b::signed-32>>
  defp write({:mv, _} = v), do: error("IOSerialize cannot write the model value #{Value.show(v)}")
  defp write(v), do: v |> Value.canon() |> write_canon()

  defp write_canon(v) when is_tuple(v) and elem(v, 0) in [:lazy_fun],
    do: error("IOSerialize cannot write #{Value.show(v)}")

  defp write_canon(v), do: write(v)

  defp unique_string(s), do: <<0::32, -1::signed-32, byte_size(s)::signed-32, s::binary>>

  defp nat(n) when n <= 0x7FFF, do: <<n::signed-16>>
  defp nat(n), do: <<-n::signed-32>>
end
