defmodule Accord.TLA.StateSpace do
  @moduledoc """
  TLA+ state space representation.

  Produced by the `BuildStateSpace` pass. Contains the VARIABLES, type
  invariant, and Init predicate for the TLA+ module.
  """

  @type variable :: %{
          name: String.t(),
          type: String.t(),
          init: String.t()
        }

  @type correspondence :: %{
          open: atom(),
          close: [atom()],
          counter_var: String.t()
        }

  @type t :: %__MODULE__{
          module_name: String.t(),
          variables: [variable()],
          type_invariant: String.t(),
          init: String.t(),
          states: [String.t()],
          correspondences: [correspondence()],
          constants: [String.t()],
          state_constraint: String.t() | nil,
          symmetry_exprs: [String.t()]
        }

  @enforce_keys [:module_name, :variables, :type_invariant, :init, :states]
  defstruct [
    :module_name,
    :variables,
    :type_invariant,
    :init,
    :states,
    correspondences: [],
    constants: [],
    state_constraint: nil,
    symmetry_exprs: []
  ]
end
