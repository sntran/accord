defmodule Accord.IR.Transition do
  @moduledoc """
  A transition within a protocol state.

  Represents a message that can be sent in a given state, with type
  constraints on arguments, optional guard and update functions, and
  one or more branches mapping reply types to next states.

  ## Kinds

  - `:call` — client request with reply branches determining the next
    state. Guard/update take the reply into account.
  - `:cast` — client fire-and-forget; never changes state, no branches.
  - `:event` — server push (server → client); no branches, the target
    state lives in `to` (`:__same__` for anystate events), guard is
    `fn message, tracks` and update is `fn message, tracks`.

  The `from` field is reserved and currently unused.
  """

  @type guard_pair :: %{fun: function(), ast: Macro.t(), span: Pentiment.Span.t() | nil}

  @type t :: %__MODULE__{
          from: atom() | nil,
          to: atom() | nil,
          message_pattern: term(),
          message_types: [Accord.IR.Type.t()],
          message_arg_names: [String.t() | nil],
          message_arg_spans: [Pentiment.Span.t() | nil],
          kind: :call | :cast | :event,
          branches: [Accord.IR.Branch.t()],
          guard: guard_pair() | nil,
          update: guard_pair() | nil,
          call_timeout: pos_integer() | nil,
          span: Pentiment.Span.t() | nil,
          block_span: Pentiment.Span.t() | nil
        }

  @enforce_keys [:message_pattern, :kind]
  defstruct [
    :from,
    :to,
    :message_pattern,
    :kind,
    :guard,
    :update,
    :call_timeout,
    :span,
    :block_span,
    message_types: [],
    message_arg_names: [],
    message_arg_spans: [],
    branches: []
  ]
end
