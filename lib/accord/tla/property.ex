defmodule Accord.TLA.Property do
  @moduledoc """
  TLA+ property representation.

  Produced by the `BuildProperties` pass. Each property maps to a TLA+
  formula — either an INVARIANT (state predicate), a temporal PROPERTY,
  or an auxiliary definition.

  `:runtime_only` marks checks the model cannot express (`ordered`,
  `precedence`, keyed correspondence): they render as a visible comment
  block in the spec and are reported by `mix accord.check`, so a green
  check never silently implies they were verified.
  """

  @type kind :: :invariant | :temporal | :auxiliary | :runtime_only

  @type t :: %__MODULE__{
          name: String.t(),
          kind: kind(),
          formula: String.t(),
          comment: String.t() | nil
        }

  @enforce_keys [:name, :kind, :formula]
  defstruct [
    :name,
    :kind,
    :formula,
    :comment
  ]
end
