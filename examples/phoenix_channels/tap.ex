defmodule Accord.Examples.PhoenixChannels.Tap do
  @moduledoc """
  Holds one accord channel monitor per `{connection, topic}` and routes tapped
  Phoenix channel messages to it, collecting violations.

  The wrapping serializer (`Accord.Examples.PhoenixChannels.Serializer`) calls
  `observe/3` for every message in both directions, passing the connection
  process (`self()` inside the serializer, which runs in the per-connection
  transport process) so concurrent connections stay isolated. Each struct is
  mapped to a channel-protocol message tag and fed to the right monitor as a
  `cast` (client → server) or server-push `event` (server → client). Violations
  land in `Accord.Test.ViolationCollector`.

  This is example/dev infrastructure. Start one `Tap` (named) before driving
  traffic, then read `violations/0`.
  """
  use GenServer

  alias Accord.Examples.PhoenixChannels.Channel.Protocol
  alias Accord.Monitor
  alias Accord.Test.ViolationCollector
  alias Phoenix.Socket.{Broadcast, Message, Reply}

  @spec start_link(keyword()) :: GenServer.on_start()
  def start_link(_opts \\ []), do: GenServer.start_link(__MODULE__, nil, name: __MODULE__)

  @doc "Reset the collector and drop all per-channel monitors. Call before a run."
  @spec reset() :: :ok
  def reset do
    ViolationCollector.init()
    if pid = Process.whereis(__MODULE__), do: GenServer.call(pid, :reset)
    :ok
  end

  @doc """
  Tap one message. `direction` is `:client` (decoded inbound) or `:server`
  (encoded outbound); `struct` is a `Phoenix.Socket.Message`/`Reply`/`Broadcast`.
  A no-op if no `Tap` is running (so the serializer is safe to leave configured
  outside tests).

  Monitors are keyed by **topic**. Keying by connection is unreliable here: a
  channel's push replies are encoded in the channel process while its join reply
  is encoded in the connection process, so `self()` is not stable across a
  channel's messages. Per-topic keying means one connection at a time per topic
  (sufficient for the demo); concurrent connections on the same topic would
  share a monitor.
  """
  @spec observe(:client | :server, struct()) :: :ok
  def observe(direction, struct) do
    if pid = Process.whereis(__MODULE__) do
      GenServer.cast(pid, {:observe, direction, struct})
    end

    :ok
  end

  @doc "Sync every monitor, then drain and return the collected violations."
  @spec violations() :: [Accord.Violation.t()]
  def violations do
    if pid = Process.whereis(__MODULE__), do: GenServer.call(pid, :sync)
    ViolationCollector.drain()
  end

  @impl true
  def init(nil) do
    # A sink for each monitor's upstream/downstream: forwarded messages are
    # discarded (the tap only cares about violations, and the real forwarding is
    # Phoenix's own — we are a passive observer).
    sink = spawn_link(&drain/0)
    {:ok, %{monitors: %{}, join_refs: %{}, sink: sink}}
  end

  @impl true
  def handle_call(:reset, _from, state) do
    for {_key, mon} <- state.monitors, Process.alive?(mon), do: GenServer.stop(mon, :normal, 100)
    {:reply, :ok, %{state | monitors: %{}, join_refs: %{}}}
  end

  def handle_call(:sync, _from, state) do
    # Round-trip each monitor so any queued cast/event is processed before the
    # caller drains the collector.
    for {_key, mon} <- state.monitors, Process.alive?(mon), do: :sys.get_state(mon)
    {:reply, :ok, state}
  end

  @impl true
  def handle_cast({:observe, direction, struct}, state) do
    case classify(direction, struct) do
      :ignore ->
        {:noreply, state}

      {topic, tag} ->
        {tag, state} = apply_join_ref_discipline(direction, struct, topic, tag, state)
        {mon, state} = monitor_for(topic, state)
        feed(mon, direction, tag)
        {:noreply, state}
    end
  end

  # join_ref discipline (§ socket.ex:810). A channel remembers the join_ref it was
  # joined with; a later client message carrying a *different*, non-nil join_ref is
  # stale (from a prior join after a rejoin) and Phoenix **silently drops it** — no
  # reply, no log. The tap records the join_ref at join and rewrites a stale client
  # message to `:stale_message`, which the model does not accept in any state — so
  # the silent drop surfaces as a client-blame violation. join_refs are arbitrary
  # strings (not model-checkable), so this obligation is runtime-only.
  defp apply_join_ref_discipline(:client, %Message{join_ref: jr}, topic, :phx_join, state) do
    {:phx_join, put_in(state.join_refs[topic], jr)}
  end

  defp apply_join_ref_discipline(:client, %Message{join_ref: jr}, topic, tag, state)
       when tag in [:push, :push_noreply, :phx_leave] do
    recorded = Map.get(state.join_refs, topic)

    if recorded != nil and jr not in [nil, "", recorded] do
      {:stale_message, state}
    else
      {tag, state}
    end
  end

  defp apply_join_ref_discipline(_direction, _struct, _topic, tag, state), do: {tag, state}

  # --- struct -> {topic, message tag} ---------------------------------------

  # Heartbeats live on the reserved "phoenix" topic and are connection
  # keepalive, not part of any channel's lifecycle.
  defp classify(_dir, %{topic: "phoenix"}), do: :ignore

  defp classify(:client, %Message{topic: topic, event: event, ref: ref}) do
    case event do
      "phx_join" -> {topic, :phx_join}
      "phx_leave" -> {topic, :phx_leave}
      # A custom event: with a ref it expects a reply; without, fire-and-forget.
      _ -> {topic, if(ref in [nil, ""], do: :push_noreply, else: :push)}
    end
  end

  defp classify(:server, %Reply{topic: topic, status: status}) do
    {topic, if(status == :ok, do: :phx_reply_ok, else: :phx_reply_error)}
  end

  defp classify(:server, %Message{topic: topic, event: "phx_close"}), do: {topic, :phx_close}
  defp classify(:server, %Message{topic: topic, event: "phx_error"}), do: {topic, :phx_error}
  defp classify(:server, %Message{topic: topic}), do: {topic, :s_push}
  defp classify(:server, %Broadcast{topic: topic}), do: {topic, :s_push}
  defp classify(_dir, _other), do: :ignore

  defp feed(mon, :client, tag), do: Monitor.cast(mon, tag)
  defp feed(mon, :server, tag), do: Accord.event(mon, tag)

  defp monitor_for(key, state) do
    case Map.fetch(state.monitors, key) do
      {:ok, mon} ->
        {mon, state}

      :error ->
        {:ok, mon} =
          Protocol.Monitor.start_link(
            upstream: state.sink,
            downstream: state.sink,
            violation_policy: {ViolationCollector, :handle}
          )

        {mon, %{state | monitors: Map.put(state.monitors, key, mon)}}
    end
  end

  defp drain do
    receive do
      _ -> drain()
    end
  end
end
