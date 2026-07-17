defmodule Accord.Examples.Demand.Producer do
  @moduledoc """
  A demand-respecting producer for the Demand protocol.

  Buffers demand from `:ask` calls; `emit/2` pushes `{:events, n}`
  through the attached monitor. The correct producer clamps emissions to
  outstanding demand; `OverEagerProducer` does not.
  """
  use GenServer

  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts)
  end

  def attach_monitor(pid, monitor), do: GenServer.call(pid, {:attach_monitor, monitor})

  @doc """
  Pushes up to `n` events, clamped to outstanding demand.
  """
  def emit(pid, n), do: GenServer.call(pid, {:emit, n})

  @impl true
  def init(_opts), do: {:ok, %{demand: 0, monitor: nil}}

  @impl true
  def handle_call({:attach_monitor, monitor}, _from, state) do
    {:reply, :ok, %{state | monitor: monitor}}
  end

  def handle_call({:ask, n}, _from, state) do
    {:reply, :ok, %{state | demand: state.demand + n}}
  end

  def handle_call({:emit, n}, _from, state) do
    emitted = min(n, state.demand)

    if emitted > 0 and state.monitor do
      Accord.event(state.monitor, {:events, emitted})
    end

    {:reply, {:emitted, emitted}, %{state | demand: state.demand - emitted}}
  end

  def handle_call(:cancel, _from, state), do: {:reply, :cancelled, state}
end

defmodule Accord.Examples.Demand.OverEagerProducer do
  @moduledoc """
  A producer that ignores demand and pushes whatever it has.

  The monitor's event guard (`n <= tracks.demand`) rejects the
  over-delivery with server blame.
  """
  use GenServer

  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts)
  end

  def attach_monitor(pid, monitor), do: GenServer.call(pid, {:attach_monitor, monitor})

  def emit(pid, n), do: GenServer.call(pid, {:emit, n})

  @impl true
  def init(_opts), do: {:ok, %{monitor: nil}}

  @impl true
  def handle_call({:attach_monitor, monitor}, _from, state) do
    {:reply, :ok, %{state | monitor: monitor}}
  end

  def handle_call({:ask, _n}, _from, state), do: {:reply, :ok, state}

  def handle_call({:emit, n}, _from, state) do
    if state.monitor, do: Accord.event(state.monitor, {:events, n})
    {:reply, {:emitted, n}, state}
  end

  def handle_call(:cancel, _from, state), do: {:reply, :cancelled, state}
end
