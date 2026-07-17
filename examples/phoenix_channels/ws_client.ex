defmodule Accord.Examples.PhoenixChannels.WsClient do
  @moduledoc """
  A minimal raw WebSocket client for driving a Phoenix Channels endpoint in the
  demo/test. It speaks just enough of RFC 6455 — the upgrade handshake and masked
  text frames — to send channel envelopes (the v2 JSON array
  `[join_ref, ref, topic, event, payload]`) and read the server's frames. Being
  raw, it can send sequences a real client library refuses to: a push before
  join, a stale join_ref, a malformed envelope.

  Only what the demo needs. JSON via `Jason`.
  """

  import Bitwise

  @type sock :: :gen_tcp.socket()

  @doc "Open a WebSocket connection to the endpoint's channel socket (v2)."
  @spec connect(:inet.port_number()) :: sock()
  def connect(port) do
    {:ok, sock} = :gen_tcp.connect(~c"localhost", port, [:binary, active: false])
    key = Base.encode64(:crypto.strong_rand_bytes(16))

    request = [
      "GET /socket/websocket?vsn=2.0.0 HTTP/1.1\r\n",
      "Host: localhost:#{port}\r\n",
      "Upgrade: websocket\r\n",
      "Connection: Upgrade\r\n",
      "Sec-WebSocket-Key: #{key}\r\n",
      "Sec-WebSocket-Version: 13\r\n\r\n"
    ]

    :ok = :gen_tcp.send(sock, request)
    "HTTP/1.1 101" <> _ = read_handshake(sock, "")
    sock
  end

  @doc "Send a `phx_join` for a topic; returns the join_ref used."
  @spec join(sock(), String.t(), String.t()) :: String.t()
  def join(sock, topic, ref) do
    send_frame(sock, [ref, ref, topic, "phx_join", %{}])
    ref
  end

  @doc "Send a custom event carrying a ref (expects a reply)."
  @spec push(sock(), String.t() | nil, String.t(), String.t(), map()) :: :ok
  def push(sock, join_ref, topic, event, ref) do
    send_frame(sock, [join_ref, ref, topic, event, %{}])
  end

  @doc "Send a fire-and-forget event (no ref)."
  @spec push_noreply(sock(), String.t() | nil, String.t(), String.t()) :: :ok
  def push_noreply(sock, join_ref, topic, event) do
    send_frame(sock, [join_ref, nil, topic, event, %{}])
  end

  @doc "Send a `phx_leave`."
  @spec leave(sock(), String.t() | nil, String.t(), String.t()) :: :ok
  def leave(sock, join_ref, topic, ref) do
    send_frame(sock, [join_ref, ref, topic, "phx_leave", %{}])
  end

  @doc "Send a raw v2 envelope verbatim (for adversarial/malformed sequences)."
  @spec send_raw(sock(), list()) :: :ok
  def send_raw(sock, array), do: send_frame(sock, array)

  @doc """
  Read the next channel message as the decoded array
  `[join_ref, ref, topic, event, payload]`. Skips ping/pong/close control frames.
  """
  @spec recv(sock()) :: list()
  def recv(sock) do
    case recv_frame(sock) do
      {0x1, payload} -> Jason.decode!(payload)
      {opcode, _} when opcode in [0x8, 0x9, 0xA] -> recv(sock)
      {_other, _} -> recv(sock)
    end
  end

  @doc "Read `n` channel messages (e.g. to await replies before draining)."
  @spec recv_many(sock(), non_neg_integer()) :: [list()]
  def recv_many(_sock, 0), do: []
  def recv_many(sock, n), do: [recv(sock) | recv_many(sock, n - 1)]

  @doc "Close the connection."
  @spec close(sock()) :: :ok
  def close(sock), do: :gen_tcp.close(sock)

  # --- framing ---------------------------------------------------------------

  defp send_frame(sock, array) do
    payload = Jason.encode!(array)
    len = byte_size(payload)
    mask = :crypto.strong_rand_bytes(4)

    length_bytes =
      cond do
        len < 126 -> <<0x80 ||| len::8>>
        len < 0x10000 -> <<0x80 ||| 126::8, len::16>>
        true -> <<0x80 ||| 127::8, len::64>>
      end

    # 0x81 = FIN + text opcode.
    :gen_tcp.send(sock, [<<0x81>>, length_bytes, mask, apply_mask(payload, mask)])
  end

  defp recv_frame(sock) do
    {:ok, <<_fin::1, _rsv::3, opcode::4, _mask::1, len0::7>>} = :gen_tcp.recv(sock, 2, 3000)

    len =
      case len0 do
        126 -> (fn {:ok, <<l::16>>} -> l end).(:gen_tcp.recv(sock, 2, 3000))
        127 -> (fn {:ok, <<l::64>>} -> l end).(:gen_tcp.recv(sock, 8, 3000))
        l -> l
      end

    payload = if len > 0, do: (fn {:ok, p} -> p end).(:gen_tcp.recv(sock, len, 3000)), else: ""
    {opcode, payload}
  end

  # RFC 6455 masking: XOR each payload byte with masking-key[i % 4].
  defp apply_mask(payload, mask) do
    keys = :binary.bin_to_list(mask)

    payload
    |> :binary.bin_to_list()
    |> Enum.with_index()
    |> Enum.map(fn {byte, i} -> bxor(byte, Enum.at(keys, rem(i, 4))) end)
    |> :binary.list_to_bin()
  end

  defp read_handshake(sock, acc) do
    if String.contains?(acc, "\r\n\r\n") do
      acc
    else
      {:ok, chunk} = :gen_tcp.recv(sock, 1, 3000)
      read_handshake(sock, acc <> chunk)
    end
  end
end
