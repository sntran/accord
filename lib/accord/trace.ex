defmodule Accord.Trace do
  @moduledoc """
  Runtime trace capture for trace validation.

  A monitor started with `trace_sink:` emits one `Accord.Trace.Event`
  per applied transition — calls, server events, and state timeouts.
  Replaying a captured trace against the generated TLA+ spec
  (`Accord.TLA.TraceSpec`) closes the loop the other checks cannot:
  TLC verifies the model against itself, and the property-based
  exerciser verifies the server against the monitor, but only trace
  validation can catch accord's own TLA+ compiler mistranslating a
  guard or an update — the trace is what actually happened; the spec
  must accept it.
  """

  defmodule Event do
    @moduledoc """
    One applied transition.

    `message` is `:__state_timeout__` for monitor-initiated transitions
    and `reply` is nil for server events and timeouts.
    """

    @type t :: %__MODULE__{
            seq: non_neg_integer(),
            prev_state: atom(),
            message: term(),
            reply: term() | nil,
            next_state: atom(),
            tracks: map()
          }

    @enforce_keys [:seq, :prev_state, :message, :next_state, :tracks]
    defstruct [:seq, :prev_state, :message, :reply, :next_state, :tracks]
  end

  @type sink :: (Event.t() -> any()) | pid() | nil

  @doc """
  Delivers an event to a sink: a function is invoked, a pid receives
  `{:accord_trace, event}`.
  """
  @spec emit(sink(), Event.t()) :: :ok
  def emit(nil, _event), do: :ok

  def emit(fun, event) when is_function(fun, 1) do
    fun.(event)
    :ok
  end

  def emit(pid, event) when is_pid(pid) do
    send(pid, {:accord_trace, event})
    :ok
  end

  @doc """
  Starts an agent-backed collector; read with `collected/1`.
  """
  @spec collector() :: {:ok, pid(), sink()}
  def collector do
    {:ok, agent} = Agent.start_link(fn -> [] end)
    sink = fn event -> Agent.update(agent, &[event | &1]) end
    {:ok, agent, sink}
  end

  @doc """
  The events collected so far, in emission order.
  """
  @spec collected(pid()) :: [Event.t()]
  def collected(agent) do
    agent |> Agent.get(& &1) |> Enum.reverse()
  end
end
