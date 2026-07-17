defmodule Accord.Examples.PhoenixChannels.Serializer do
  @moduledoc """
  A `Phoenix.Socket.Serializer` that wraps the real v2 JSON serializer and taps
  every channel message into `Accord.Examples.PhoenixChannels.Tap`.

  The serializer is the ideal monitor seam: its three callbacks are the single
  point where channel structs become wire bytes and back, below the channel
  layer and above the transport (so it is transport-agnostic — WebSocket and
  longpoll both pass through it). It is also the whole integration surface — you
  wire the monitor into any Phoenix app with one line:

      socket "/socket", MySocket,
        websocket: [serializer: [{Accord.Examples.PhoenixChannels.Serializer, "2.0.0"}]]

  Encoding/decoding behaviour is delegated verbatim to `Phoenix.Socket.V2.
  JSONSerializer`; the wrapper only observes. `self()` inside these callbacks is
  the per-connection transport process, so the tap keys monitors by connection.
  """
  @behaviour Phoenix.Socket.Serializer

  alias Accord.Examples.PhoenixChannels.Tap
  alias Phoenix.Socket.V2

  @impl true
  def fastlane!(broadcast) do
    Tap.observe(:server, broadcast)
    V2.JSONSerializer.fastlane!(broadcast)
  end

  @impl true
  def encode!(message_or_reply) do
    Tap.observe(:server, message_or_reply)
    V2.JSONSerializer.encode!(message_or_reply)
  end

  @impl true
  def decode!(raw_message, opts) do
    message = V2.JSONSerializer.decode!(raw_message, opts)
    Tap.observe(:client, message)
    message
  end
end
