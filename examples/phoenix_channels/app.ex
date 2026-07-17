defmodule Accord.Examples.PhoenixChannels.RoomChannel do
  @moduledoc """
  A correct channel. Joins any `room:*` topic, replies to a `ping`, accepts a
  fire-and-forget `notify`, and can emit a server-initiated push. Every request
  gets exactly one reply — so a session against this channel raises no violations.
  """
  use Phoenix.Channel

  @impl true
  def join("room:" <> _sub, _params, socket), do: {:ok, socket}

  @impl true
  def handle_in("ping", _payload, socket) do
    {:reply, {:ok, %{pong: true}}, socket}
  end

  # A push the client does not expect a reply to (client sends it with no ref).
  def handle_in("notify", _payload, socket), do: {:noreply, socket}

  # Trigger a server-initiated push back to this client (no client ref).
  def handle_in("subscribe", _payload, socket) do
    push(socket, "server_event", %{hello: "world"})
    {:reply, {:ok, %{}}, socket}
  end
end

defmodule Accord.Examples.PhoenixChannels.BuggyChannel do
  @moduledoc """
  A channel with a real protocol bug: it replies **twice** to one request.

  `handle_in("work", ...)` captures a `socket_ref` and — imagine a naive retry
  that fires the reply again without guarding against having already replied —
  calls `reply/2` twice for the same `ref`. Phoenix does not prevent this: two
  `phx_reply` frames go out for one request. The monitor catches the second one
  as an excess reply (nothing outstanding) and blames the server.
  """
  use Phoenix.Channel

  @impl true
  def join("buggy:" <> _sub, _params, socket), do: {:ok, socket}

  @impl true
  def handle_in("work", _payload, socket) do
    ref = socket_ref(socket)
    # BUG: two replies for one request.
    reply(ref, {:ok, %{attempt: 1}})
    reply(ref, {:ok, %{attempt: 2}})
    {:noreply, socket}
  end
end

defmodule Accord.Examples.PhoenixChannels.UserSocket do
  @moduledoc false
  use Phoenix.Socket

  channel "room:*", Accord.Examples.PhoenixChannels.RoomChannel
  channel "buggy:*", Accord.Examples.PhoenixChannels.BuggyChannel

  @impl true
  def connect(_params, socket, _connect_info), do: {:ok, socket}

  @impl true
  def id(_socket), do: nil
end

defmodule Accord.Examples.PhoenixChannels.Endpoint do
  @moduledoc """
  A minimal Phoenix endpoint whose socket uses the tapping serializer, so every
  channel message on every connection is checked by the accord monitor. Started
  with an ephemeral port by the demo/test; configure via `Application.put_env/3`
  before `start_link/0` (there is no config file in this workspace).
  """
  use Phoenix.Endpoint, otp_app: :accord

  socket "/socket", Accord.Examples.PhoenixChannels.UserSocket,
    websocket: [
      serializer: [{Accord.Examples.PhoenixChannels.Serializer, "~> 2.0.0"}],
      check_origin: false
    ],
    longpoll: false
end
