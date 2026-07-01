defmodule Accord.Monitor.Compiled do
  @moduledoc """
  Compiled protocol data ready for runtime monitoring.

  Contains the validated IR, the flattened transition table, initial
  track state, and the full list of properties.
  """

  alias Accord.IR
  alias Accord.Monitor.TransitionTable

  @type t :: %__MODULE__{
          ir: IR.t(),
          transition_table: TransitionTable.t(),
          track_init: map(),
          state_timeouts: %{atom() => {pos_integer(), atom()}}
        }

  @enforce_keys [:ir, :transition_table, :track_init]
  defstruct [:ir, :transition_table, :track_init, state_timeouts: %{}]
end
