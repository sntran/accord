defmodule Accord.Examples.Http2.RawClient do
  @moduledoc """
  A minimal raw-frame HTTP/2 (h2c, cleartext) client for the tap-proxy demo and
  test. It writes frames directly to a socket so it can send sequences a
  conformant client library would refuse to — in particular a trailing HEADERS
  frame without END_STREAM. Header blocks are HPACK-encoded via `HPAX`; the rest
  is hand-written framing.

  Only what the demo needs: connect (with the preface + SETTINGS handshake), send
  request HEADERS / DATA / trailer HEADERS, and read the response body.
  """

  import Bitwise

  @preface "PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n"

  # The second element is an opaque HPAX encode context (HPAX exports no public
  # type for it).
  @type conn :: {:gen_tcp.socket(), term()}

  @doc "Open a cleartext HTTP/2 connection and complete the preface/SETTINGS handshake."
  @spec connect(:inet.port_number()) :: conn()
  def connect(port) do
    {:ok, sock} = :gen_tcp.connect(~c"localhost", port, [:binary, active: false])
    :ok = :gen_tcp.send(sock, @preface)
    {:ok, <<len::24, 4, 0, 0::32>>} = :gen_tcp.recv(sock, 9)
    if len > 0, do: {:ok, _} = :gen_tcp.recv(sock, len)
    :ok = :gen_tcp.send(sock, <<0, 0, 0, 4, 1, 0::32>>)
    :ok = :gen_tcp.send(sock, <<0, 0, 0, 4, 0, 0::32>>)
    {:ok, <<0, 0, 0, 4, 1, 0::32>>} = :gen_tcp.recv(sock, 9)
    {sock, HPAX.new(4096)}
  end

  @doc "Send a HEADERS frame with an arbitrary header list."
  @spec headers(conn(), pos_integer(), boolean(), [{String.t(), String.t()}]) :: conn()
  def headers({sock, ctx}, stream_id, end_stream, header_list) do
    {block, ctx} = header_list |> Enum.map(fn {k, v} -> {:store, k, v} end) |> HPAX.encode(ctx)
    flags = if end_stream, do: 0x05, else: 0x04
    frame(sock, 0x1, flags, stream_id, block)
    {sock, ctx}
  end

  @doc "Send request pseudo-headers for `POST /echo`."
  @spec post_echo(conn(), pos_integer(), boolean(), :inet.port_number()) :: conn()
  def post_echo(conn, stream_id, end_stream, port) do
    headers(conn, stream_id, end_stream, [
      {":method", "POST"},
      {":path", "/echo"},
      {":scheme", "http"},
      {":authority", "localhost:#{port}"}
    ])
  end

  @doc "Send a DATA frame."
  @spec data(conn(), pos_integer(), boolean(), iodata()) :: conn()
  def data({sock, _} = conn, stream_id, end_stream, body) do
    frame(sock, 0x0, if(end_stream, do: 0x01, else: 0x00), stream_id, body)
    conn
  end

  @doc "Send a connection-level PING (used to provoke a response from the server)."
  @spec ping(conn()) :: conn()
  def ping({sock, _} = conn) do
    frame(sock, 0x6, 0x00, 0, <<0, 0, 0, 0, 0, 0, 0, 0>>)
    conn
  end

  @doc "Read one frame, discarding its payload; returns `{type, flags, stream_id}`."
  @spec recv_frame(conn()) :: {non_neg_integer(), non_neg_integer(), non_neg_integer()}
  def recv_frame({sock, _}) do
    {:ok, <<len::24, type::8, flags::8, _r::1, sid::31>>} = :gen_tcp.recv(sock, 9, 2000)
    if len > 0, do: {:ok, _} = :gen_tcp.recv(sock, len, 2000)
    {type, flags, sid}
  end

  @doc "Read frames until a PING ACK arrives (the server answered our PING)."
  @spec await_ping_ack(conn()) :: :ok
  def await_ping_ack(conn) do
    case recv_frame(conn) do
      {0x6, flags, _sid} when (Bitwise.band(flags, 0x01)) == 0x01 -> :ok
      _other -> await_ping_ack(conn)
    end
  end

  @doc "Read response DATA frames until END_STREAM, returning the assembled body."
  @spec read_body(conn()) :: binary()
  def read_body({sock, _}), do: read_body(sock, "")

  defp read_body(sock, acc) do
    {:ok, <<len::24, type::8, flags::8, _r::1, _sid::31>>} = :gen_tcp.recv(sock, 9, 2000)
    payload = if len > 0, do: recv_exact(sock, len), else: <<>>
    acc = if type == 0x0, do: acc <> payload, else: acc

    if type == 0x0 and band(flags, 0x01) == 0x01 do
      acc
    else
      read_body(sock, acc)
    end
  end

  defp recv_exact(sock, len) do
    {:ok, payload} = :gen_tcp.recv(sock, len, 2000)
    payload
  end

  defp frame(sock, type, flags, stream_id, payload) do
    payload = IO.iodata_to_binary(payload)

    :ok =
      :gen_tcp.send(sock, [
        <<byte_size(payload)::24, type::8, flags::8, 0::1, stream_id::31>>,
        payload
      ])
  end
end
