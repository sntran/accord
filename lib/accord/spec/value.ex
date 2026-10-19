defmodule Accord.Spec.Value do
  @moduledoc """
  Changes Elixir terms into TLA+ values of `Accord.TLA.Checker.Value`,
  and back.

  | Elixir                         | TLA+                                    |
  |--------------------------------|-----------------------------------------|
  | integer, `true`, `false`       | the same                                |
  | binary                         | string                                  |
  | atom                           | model value of the same name, else string |
  | tuple                          | tuple `<<...>>`                         |
  | list                           | sequence                                |
  | map with atom keys             | record                                  |
  | other map                      | function                                |
  | `MapSet`                       | set                                     |
  """

  alias Accord.TLA.Checker.Value

  @doc """
  The TLA+ value of an Elixir term. `model_values` maps names to the model
  values of the config (see `Accord.TLA.Checker.Machine.model_values/1`).
  """
  @spec to_tla(term(), %{String.t() => term()}) :: term()
  def to_tla(term, model_values \\ %{})

  def to_tla(v, _mv) when is_integer(v) or is_boolean(v) or is_binary(v), do: v

  def to_tla(nil, _mv), do: "nil"

  def to_tla(a, mv) when is_atom(a) do
    name = Atom.to_string(a)
    Map.get(mv, name, name)
  end

  def to_tla(%MapSet{} = s, mv), do: Value.set(Enum.map(s, &to_tla(&1, mv)))

  def to_tla(t, mv) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.map(&to_tla(&1, mv)) |> Value.tuple()

  def to_tla(l, mv) when is_list(l), do: l |> Enum.map(&to_tla(&1, mv)) |> Value.tuple()

  def to_tla(%{} = m, mv) do
    m
    |> Map.new(fn
      {k, v} when is_atom(k) and k not in [nil, true, false] -> {Atom.to_string(k), to_tla(v, mv)}
      {k, v} -> {Value.canon(to_tla(k, mv)), to_tla(v, mv)}
    end)
    |> Value.fun()
  end

  def to_tla(other, _mv), do: raise(ArgumentError, "no TLA+ value for #{inspect(other)}")

  @doc """
  An Elixir term for a TLA+ value: a string, a model value (as its name,
  a string), a list for a sequence, a map for any other function, and a
  `MapSet` for a set.
  """
  @spec from_tla(term()) :: term()
  def from_tla(v) when is_integer(v) or is_boolean(v) or is_binary(v), do: v
  def from_tla({:mv, name}), do: name
  def from_tla(%MapSet{} = s), do: MapSet.new(s, &from_tla/1)
  def from_tla({:seq, t}), do: t |> Tuple.to_list() |> Enum.map(&from_tla/1)
  def from_tla({:fun, m}), do: Map.new(m, fn {k, v} -> {from_tla(k), from_tla(v)} end)
  def from_tla(other), do: other
end
