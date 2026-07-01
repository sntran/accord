defmodule Accord.IR.State do
  @moduledoc """
  A named state in a protocol state machine.

  `state_timeout` is a monitor-initiated transition: entering the state
  arms a timer (`{milliseconds, target}`), and if the session is still
  here when it fires, the monitor moves to the target state without any
  message exchange — a circuit breaker's cooldown, a lease expiring
  client-side. In the untimed TLA+ model it becomes an internal action
  that may fire whenever the state is occupied, weakly fair under
  liveness checking (a physical timer always eventually fires).
  """

  @type t :: %__MODULE__{
          name: atom(),
          terminal: boolean(),
          transitions: [Accord.IR.Transition.t()],
          state_timeout: {pos_integer(), atom()} | nil,
          span: Pentiment.Span.t() | nil
        }

  @enforce_keys [:name]
  defstruct [:name, :span, terminal: false, transitions: [], state_timeout: nil]
end
