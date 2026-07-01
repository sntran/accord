defmodule Accord.Examples.CircuitBreaker.Server do
  @moduledoc """
  A correct breaker implementation for the CircuitBreaker protocol.

  The protected downstream is simulated with an injectable outcome queue
  (`push_outcomes/2`): each `:request` consumes the next outcome
  (`:ok` or `:error`), defaulting to `:ok`. The breaker translates the
  third consecutive failure into `:tripped`, as the contract demands.
  """
  use GenServer

  @threshold 3

  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts)
  end

  @doc """
  Queues downstream outcomes for subsequent requests.
  """
  def push_outcomes(pid, outcomes) when is_list(outcomes) do
    GenServer.call(pid, {:push_outcomes, outcomes})
  end

  @impl true
  def init(_opts) do
    {:ok, %{failures: 0, state: :closed, outcomes: []}}
  end

  @impl true
  def handle_call({:push_outcomes, outcomes}, _from, state) do
    {:reply, :ok, %{state | outcomes: state.outcomes ++ outcomes}}
  end

  def handle_call(:request, _from, %{state: :closed} = state) do
    {outcome, rest} = next_outcome(state.outcomes)

    case outcome do
      :ok ->
        {:reply, :ok, %{state | failures: 0, outcomes: rest}}

      :error ->
        failures = state.failures + 1

        if failures >= @threshold do
          {:reply, :tripped, %{state | failures: failures, state: :open, outcomes: rest}}
        else
          {:reply, :error, %{state | failures: failures, outcomes: rest}}
        end
    end
  end

  def handle_call(:request, _from, %{state: :open} = state) do
    {:reply, {:rejected, :circuit_open}, state}
  end

  def handle_call(:request, _from, %{state: :half_open} = state) do
    {outcome, rest} = next_outcome(state.outcomes)

    case outcome do
      :ok -> {:reply, :ok, %{state | failures: 0, state: :closed, outcomes: rest}}
      :error -> {:reply, :error, %{state | state: :open, outcomes: rest}}
    end
  end

  def handle_call(:shutdown, _from, state) do
    {:reply, :down, state}
  end

  defp next_outcome([]), do: {:ok, []}
  defp next_outcome([outcome | rest]), do: {outcome, rest}
end

defmodule Accord.Examples.CircuitBreaker.MislabelingServer do
  @moduledoc """
  A buggy breaker that replies `:error` at the threshold instead of
  `:tripped` — the mislabeled reply violates the `:error` branch's
  `where: failures < 2` constraint, and the monitor blames the server
  (`:constraint_failed`). The same contract rule, caught at the reply
  boundary instead of by the invariant.
  """
  use GenServer

  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts)
  end

  @impl true
  def init(_opts), do: {:ok, %{}}

  @impl true
  # Always claims a plain :error, even on the trip.
  def handle_call(:request, _from, state), do: {:reply, :error, state}
  def handle_call(:shutdown, _from, state), do: {:reply, :down, state}
end
