defmodule Accord.Examples.Payment.Server do
  @moduledoc """
  A correct payment server for the Payment protocol.

  Approves authorizations by default; `decline_next/1` queues a decline.
  """
  use GenServer

  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts)
  end

  def decline_next(pid), do: GenServer.call(pid, :decline_next)

  @impl true
  def init(_opts) do
    {:ok, %{authorized: 0, captured: 0, refunded: 0, decline: false}}
  end

  @impl true
  def handle_call(:decline_next, _from, state) do
    {:reply, :ok, %{state | decline: true}}
  end

  def handle_call({:authorize, _amount}, _from, %{decline: true} = state) do
    {:reply, :declined, %{state | decline: false}}
  end

  def handle_call({:authorize, amount}, _from, state) do
    {:reply, :approved, %{state | authorized: amount}}
  end

  def handle_call({:capture, amount}, _from, state) do
    {:reply, :ok, %{state | captured: state.captured + amount}}
  end

  def handle_call(:finalize, _from, state), do: {:reply, :finalized, state}
  def handle_call(:void, _from, state), do: {:reply, :voided, state}

  def handle_call({:refund, amount}, _from, state) do
    {:reply, :ok, %{state | refunded: state.refunded + amount}}
  end

  def handle_call(:close, _from, state), do: {:reply, :closed, state}
end
