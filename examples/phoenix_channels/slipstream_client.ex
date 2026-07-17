defmodule Accord.Examples.PhoenixChannels.SlipstreamClient do
  @moduledoc """
  A minimal [Slipstream](https://hexdocs.pm/slipstream) client used to drive the
  instrumented Phoenix endpoint from a *different* client implementation than the
  example's raw WebSocket client. It forwards lifecycle events to a parent process
  and accepts `join`/`push`/`leave` commands, so a test can script a session and
  synchronize on the replies while the tapping serializer checks conformance.

  Slipstream is an independent, third-party channel client; a clean run here means
  the monitor is faithful across implementations, not just against our own client.
  """
  use Slipstream

  @spec start_link(keyword()) :: GenServer.on_start()
  def start_link(opts), do: Slipstream.start_link(__MODULE__, opts)

  @doc "Ask the client to join a topic."
  def join_topic(pid, topic), do: GenServer.cast(pid, {:join, topic})
  @doc "Ask the client to push an event (expects a reply)."
  def push_event(pid, topic, event, params \\ %{}), do: GenServer.cast(pid, {:push, topic, event, params})
  @doc "Ask the client to leave a topic."
  def leave_topic(pid, topic), do: GenServer.cast(pid, {:leave, topic})

  @impl Slipstream
  def init(opts) do
    parent = Keyword.fetch!(opts, :parent)
    uri = Keyword.fetch!(opts, :uri)
    socket = connect!(uri: uri) |> assign(:parent, parent)
    {:ok, socket}
  end

  @impl Slipstream
  def handle_connect(socket) do
    notify(socket, :connected)
    {:ok, socket}
  end

  @impl Slipstream
  def handle_join(topic, _reply, socket) do
    notify(socket, {:joined, topic})
    {:ok, socket}
  end

  @impl Slipstream
  def handle_reply(ref, reply, socket) do
    notify(socket, {:reply, ref, reply})
    {:ok, socket}
  end

  @impl Slipstream
  def handle_message(topic, event, payload, socket) do
    notify(socket, {:message, topic, event, payload})
    {:ok, socket}
  end

  @impl Slipstream
  def handle_topic_close(topic, reason, socket) do
    notify(socket, {:topic_close, topic, reason})
    {:ok, socket}
  end

  @impl Slipstream
  def handle_leave(topic, socket) do
    notify(socket, {:left, topic})
    {:ok, socket}
  end

  @impl Slipstream
  def handle_cast({:join, topic}, socket), do: {:noreply, join(socket, topic)}

  def handle_cast({:push, topic, event, params}, socket) do
    _ = push(socket, topic, event, params)
    {:noreply, socket}
  end

  def handle_cast({:leave, topic}, socket), do: {:noreply, leave(socket, topic)}

  defp notify(socket, event), do: send(socket.assigns.parent, {:slipstream, event})
end
