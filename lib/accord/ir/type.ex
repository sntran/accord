defmodule Accord.IR.Type do
  @moduledoc """
  Type representation for protocol contracts.

  A tagged union of simple types, compound types, and literal values.
  Used for both message argument validation and reply matching.
  """

  @type t ::
          :string
          | :integer
          | :pos_integer
          | :non_neg_integer
          | :atom
          | :binary
          | :boolean
          | :term
          | :map
          | {:list, t()}
          | {:tuple, [t()]}
          | {:struct, module()}
          | {:literal, term()}
          | {:union, [t()]}
          | {:tagged, atom(), t() | [t()]}

  @doc """
  Parses a type specification from quoted Elixir AST.

  Handles built-in types like `integer()`, compound types like `[integer()]`,
  struct types like `%Card{}`, union types like `atom() | integer()`, and
  literal values like `:ok` or `42`.
  """
  @spec parse(Macro.t()) :: t()
  def parse({:integer, _, args}) when args in [nil, []], do: :integer
  def parse({:pos_integer, _, args}) when args in [nil, []], do: :pos_integer
  def parse({:non_neg_integer, _, args}) when args in [nil, []], do: :non_neg_integer
  def parse({:atom, _, args}) when args in [nil, []], do: :atom
  def parse({:binary, _, args}) when args in [nil, []], do: :binary
  def parse({:boolean, _, args}) when args in [nil, []], do: :boolean
  def parse({:term, _, args}) when args in [nil, []], do: :term
  def parse({:map, _, args}) when args in [nil, []], do: :map

  # String.t()
  def parse({{:., _, [{:__aliases__, _, [:String]}, :t]}, _, []}), do: :string

  # Struct: %ModuleName{}
  def parse({:%, _, [{:__aliases__, _, parts}, {:%{}, _, []}]}) do
    {:struct, Module.concat(parts)}
  end

  # List: [element_type]
  def parse([element_type]) do
    {:list, parse(element_type)}
  end

  # Tuple: {a, b, c, ...}
  def parse({:{}, _, elements}) do
    {:tuple, Enum.map(elements, &parse/1)}
  end

  # Two-element tuple special case (Elixir AST doesn't use :{} for 2-tuples).
  def parse({a, b}) when not is_atom(a) or a not in [:%, :|, :"::", :.] do
    {:tuple, [parse(a), parse(b)]}
  end

  # Union: type_a | type_b
  def parse({:|, _, [left, right]}) do
    left_types = flatten_union(parse(left))
    right_types = flatten_union(parse(right))
    {:union, left_types ++ right_types}
  end

  # Literal atom
  def parse(atom) when is_atom(atom) do
    {:literal, atom}
  end

  # Literal integer
  def parse(int) when is_integer(int) do
    {:literal, int}
  end

  # Variable reference — treat as :term (used in pattern positions).
  def parse({name, _, context}) when is_atom(name) and is_atom(context) do
    :term
  end

  defp flatten_union({:union, types}), do: types
  defp flatten_union(type), do: [type]

  @doc """
  Whether every value of `sub` is also a value of `sup`.

  The subtyping relation behind protocol compatibility checking
  (`Accord.Compat`): argument types may widen across versions
  (contravariance) and reply types may narrow (covariance), both
  expressed through this predicate.

  Conservative: `false` means "not provably a subtype" — unknown
  combinations never silently pass.
  """
  @spec subtype?(t(), t()) :: boolean()
  def subtype?(type, type), do: true
  def subtype?(_sub, :term), do: true

  # Literals against their carriers.
  def subtype?({:literal, v}, sup) when is_integer(v) do
    case sup do
      :integer -> true
      :pos_integer -> v > 0
      :non_neg_integer -> v >= 0
      _ -> subtype_union?({:literal, v}, sup)
    end
  end

  def subtype?({:literal, v}, sup) when is_boolean(v) do
    sup in [:boolean, :atom] or subtype_union?({:literal, v}, sup)
  end

  def subtype?({:literal, v}, sup) when is_atom(v) do
    sup == :atom or subtype_union?({:literal, v}, sup)
  end

  def subtype?({:literal, v}, sup) when is_binary(v) do
    sup in [:binary, :string] or subtype_union?({:literal, v}, sup)
  end

  # Integer hierarchy.
  def subtype?(:pos_integer, sup) when sup in [:non_neg_integer, :integer], do: true
  def subtype?(:non_neg_integer, :integer), do: true

  # Booleans are atoms; strings and binaries coincide at runtime.
  def subtype?(:boolean, :atom), do: true
  def subtype?(:string, :binary), do: true
  def subtype?(:binary, :string), do: true

  # Compound types: covariant elements.
  def subtype?({:list, sub}, {:list, sup}), do: subtype?(sub, sup)

  def subtype?({:tuple, subs}, {:tuple, sups}) when length(subs) == length(sups) do
    subs |> Enum.zip(sups) |> Enum.all?(fn {s, p} -> subtype?(s, p) end)
  end

  def subtype?({:tagged, tag, sub_inner}, {:tagged, tag, sup_inner}) do
    subtype_inner?(List.wrap(sub_inner), List.wrap(sup_inner))
  end

  # Unions: every member of a sub-union must fit; a non-union fits a
  # union when it fits some member.
  def subtype?({:union, subs}, sup) do
    Enum.all?(subs, &subtype?(&1, sup))
  end

  def subtype?(sub, {:union, _} = sup), do: subtype_union?(sub, sup)

  def subtype?(_sub, _sup), do: false

  defp subtype_union?(sub, {:union, sups}), do: Enum.any?(sups, &subtype?(sub, &1))
  defp subtype_union?(_sub, _sup), do: false

  defp subtype_inner?(subs, sups) when length(subs) == length(sups) do
    subs |> Enum.zip(sups) |> Enum.all?(fn {s, p} -> subtype?(s, p) end)
  end

  defp subtype_inner?(_, _), do: false

  @doc """
  Whether two types can share a value.

  Reply-branch selection is first-match on the *value*, so two branches
  whose types overlap resolve order-dependently. `Accord.Compat` uses
  this to detect when a static, order-blind reply comparison would be
  unsound.

  Conservative toward `true`: it returns `false` only when the types are
  *provably* disjoint, so an overlap is never missed (an unmissed overlap
  is what keeps the compat check sound).
  """
  @spec overlap?(t(), t()) :: boolean()
  def overlap?(type, type), do: true
  def overlap?(:term, _), do: true
  def overlap?(_, :term), do: true

  # Literals: two literals overlap iff equal; a literal overlaps a type
  # iff that single value inhabits the type.
  def overlap?({:literal, a}, {:literal, b}), do: a == b
  def overlap?({:literal, _} = lit, type), do: subtype?(lit, type)
  def overlap?(type, {:literal, _} = lit), do: subtype?(lit, type)

  # Unions overlap a type when any member does.
  def overlap?({:union, types}, other), do: Enum.any?(types, &overlap?(&1, other))
  def overlap?(other, {:union, types}), do: Enum.any?(types, &overlap?(other, &1))

  # Tagged tuples overlap only with the same tag and overlapping payload.
  def overlap?({:tagged, tag, left}, {:tagged, tag, right}) do
    inner_overlap?(List.wrap(left), List.wrap(right))
  end

  def overlap?({:tagged, _, _}, {:tagged, _, _}), do: false

  # Tuples overlap element-wise at equal arity.
  def overlap?({:tuple, left}, {:tuple, right}) when length(left) == length(right) do
    left |> Enum.zip(right) |> Enum.all?(fn {a, b} -> overlap?(a, b) end)
  end

  def overlap?({:tuple, _}, {:tuple, _}), do: false

  # Any two lists share the empty list.
  def overlap?({:list, _}, {:list, _}), do: true

  # Scalar carriers: same base kind overlaps; provably-different base
  # kinds are disjoint; anything structural (map/struct) stays
  # conservative (`true`) rather than risk missing an overlap.
  def overlap?(left, right) do
    case {base_kind(left), base_kind(right)} do
      {kind, kind} -> true
      {left_kind, right_kind} when left_kind != nil and right_kind != nil -> false
      _ -> true
    end
  end

  defp inner_overlap?(left, right) when length(left) == length(right) do
    left |> Enum.zip(right) |> Enum.all?(fn {a, b} -> overlap?(a, b) end)
  end

  defp inner_overlap?(_, _), do: false

  # Provably-disjoint scalar kinds; nil means "not classified, assume it
  # can overlap". Structs and maps deliberately fall through to nil.
  defp base_kind(:integer), do: :number
  defp base_kind(:pos_integer), do: :number
  defp base_kind(:non_neg_integer), do: :number
  defp base_kind(:atom), do: :atom
  defp base_kind(:boolean), do: :atom
  defp base_kind(:binary), do: :binary
  defp base_kind(:string), do: :binary
  defp base_kind({:list, _}), do: :list
  defp base_kind({:tuple, _}), do: :tuple
  defp base_kind({:tagged, _, _}), do: :tuple
  defp base_kind(_), do: nil

  @doc """
  Converts a type to a human-readable string.
  """
  @spec to_string(t()) :: String.t()
  def to_string(:string), do: "String.t()"
  def to_string(:integer), do: "integer()"
  def to_string(:pos_integer), do: "pos_integer()"
  def to_string(:non_neg_integer), do: "non_neg_integer()"
  def to_string(:atom), do: "atom()"
  def to_string(:binary), do: "binary()"
  def to_string(:boolean), do: "boolean()"
  def to_string(:term), do: "term()"
  def to_string(:map), do: "map()"
  def to_string({:list, elem}), do: "[#{__MODULE__.to_string(elem)}]"

  def to_string({:tuple, elems}),
    do: "{#{Enum.map_join(elems, ", ", &__MODULE__.to_string/1)}}"

  def to_string({:struct, mod}), do: "%#{inspect(mod)}{}"
  def to_string({:literal, val}), do: inspect(val)
  def to_string({:union, types}), do: Enum.map_join(types, " | ", &__MODULE__.to_string/1)

  def to_string({:tagged, tag, payload}) when is_list(payload) do
    args = Enum.map_join(payload, ", ", &__MODULE__.to_string/1)
    "{#{inspect(tag)}, #{args}}"
  end

  def to_string({:tagged, tag, payload}) do
    "{#{inspect(tag)}, #{__MODULE__.to_string(payload)}}"
  end
end
