defmodule Accord.Examples.JobQueue.Server do
  @moduledoc """
  A correct single-lease queue for the JobQueue protocol.

  Issues strictly increasing fence tokens. `expire_lease/1` simulates
  the visibility timeout: the queue revokes the lease and pushes
  `{:lease_expired, token}` through the monitor (`attach_monitor/2`),
  where it is validated like any other message.
  """
  use GenServer

  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts)
  end

  @doc """
  Tells the queue which monitor to push events through.
  """
  def attach_monitor(pid, monitor), do: GenServer.call(pid, {:attach_monitor, monitor})

  @doc """
  Fires the visibility timeout for the current lease.
  """
  def expire_lease(pid), do: GenServer.call(pid, :expire_lease)

  @impl true
  def init(_opts) do
    {:ok, %{fence: 0, leased: nil, monitor: nil}}
  end

  @impl true
  def handle_call({:attach_monitor, monitor}, _from, state) do
    {:reply, :ok, %{state | monitor: monitor}}
  end

  def handle_call(:expire_lease, _from, %{leased: nil} = state) do
    {:reply, :no_lease, state}
  end

  def handle_call(:expire_lease, _from, %{leased: token} = state) do
    if state.monitor, do: Accord.event(state.monitor, {:lease_expired, token})
    {:reply, :expired, %{state | leased: nil}}
  end

  def handle_call(:checkout, _from, %{leased: nil} = state) do
    token = state.fence + 1
    {:reply, {:job, token}, %{state | fence: token, leased: token}}
  end

  def handle_call(:checkout, _from, state) do
    {:reply, :empty, state}
  end

  def handle_call({:heartbeat, token}, _from, %{leased: token} = state) do
    {:reply, :extended, state}
  end

  def handle_call({:ack, token}, _from, %{leased: token} = state) do
    {:reply, :done, %{state | leased: nil}}
  end

  def handle_call({:ack, _stale}, _from, state) do
    {:reply, {:stale, state.fence}, state}
  end

  def handle_call({:nack, token}, _from, %{leased: token} = state) do
    {:reply, :requeued, %{state | leased: nil}}
  end

  def handle_call(:stop, _from, state) do
    {:reply, :stopped, state}
  end
end

defmodule Accord.Examples.JobQueue.StaleTokenServer do
  @moduledoc """
  A buggy queue that re-issues an old fence token after expiry.

  Re-using a token violates the checkout branch's
  `where: token > tracks.fence` constraint — the monitor reports
  `:constraint_failed` with server blame the moment the stale lease is
  handed out, answering "who leaked the lease" mechanically.
  """
  use GenServer

  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts)
  end

  @impl true
  def init(_opts) do
    # Always hands out token 1, no matter how many leases came before.
    {:ok, %{leased: nil}}
  end

  @impl true
  def handle_call(:checkout, _from, state) do
    {:reply, {:job, 1}, %{state | leased: 1}}
  end

  def handle_call({:ack, token}, _from, %{leased: token} = state) do
    {:reply, :done, %{state | leased: nil}}
  end

  def handle_call({:nack, token}, _from, %{leased: token} = state) do
    {:reply, :requeued, %{state | leased: nil}}
  end

  def handle_call(:stop, _from, state) do
    {:reply, :stopped, state}
  end
end
