defmodule Accord.IR.Track do
  @moduledoc """
  A tracked accumulator in a protocol.

  Tracks are named state variables that persist across transitions and
  can be read by guards and mutated by updates.

  ## Shared tracks

  A track declared with `shared: true` models state that lives on the
  server and is observed by every session (a fence counter, a lock
  holder). In multi-session model checking (`sessions: N`), shared
  tracks are a single variable all session actions read and write, while
  regular tracks are per-session.

  Shared tracks are ghost state at runtime: each monitor instance keeps
  its own copy updated only by its session's traffic, so runtime
  checking of shared-track properties is weaker than the model — see
  ADR-009.
  """

  @type t :: %__MODULE__{
          name: atom(),
          type: Accord.IR.Type.t(),
          default: term(),
          shared: boolean(),
          domain: Accord.TLA.ModelConfig.domain() | nil,
          model_init: term(),
          abstract: nil | :monotonic,
          span: Pentiment.Span.t() | nil
        }

  @enforce_keys [:name, :type, :default]
  defstruct [
    :name,
    :type,
    :default,
    :span,
    shared: false,
    domain: nil,
    model_init: nil,
    abstract: nil
  ]
end
