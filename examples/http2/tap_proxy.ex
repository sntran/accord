defmodule Accord.Examples.Http2.TapProxy do
  @moduledoc """
  A passive TCP proxy that sits between an HTTP/2 client and a running Bandit
  server, relaying bytes verbatim while *tapping* the frame stream into a live
  accord monitor per stream.

  For each direction it parses the HTTP/2 frame layer — just the 9-byte frame
  headers (length, type, flags, stream id), no HPACK — which is exactly what the
  stream state machine dispatches on (frame type + END_STREAM). Each stream frame
  is fed to a per-stream `Accord.Examples.Http2.Stream.Protocol` monitor as a
  `cast` (client → server) or a server-push `event` (server → client). The
  monitor validates the frame against the RFC state machine and records a
  violation when it does not fit — which is how the proxy catches a divergence in
  the real server, without being in the data path itself (bytes are forwarded
  first, unmodified).

  This is example/dev infrastructure, not part of accord's core. It exists to
  demonstrate the runtime monitor applied to a real wire protocol.

  ## Usage

      Accord.Test.ViolationCollector.init()
      {:ok, proxy} = TapProxy.start_link(bandit_port)
      port = TapProxy.port(proxy)
      # ... drive an HTTP/2 client against `port` ...
      violations = TapProxy.violations(proxy)

  Connection-level frames (stream id 0: SETTINGS, PING, GOAWAY, the connection
  WINDOW_UPDATE) are not part of the per-stream machine and are relayed but not
  tapped. Frame types the stream machine does not model (PRIORITY, CONTINUATION,
  PUSH_PROMISE) are likewise relayed untapped rather than reported as spurious
  violations.
  """
  use GenServer

  import Bitwise

  alias Accord.Examples.Http2.Stream.Protocol
  alias Accord.Monitor
  alias Accord.Test.ViolationCollector

  @preface "PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n"

  @type t :: pid()

  @spec start_link(:inet.port_number()) :: {:ok, pid()}
  def start_link(bandit_port), do: GenServer.start_link(__MODULE__, bandit_port)

  @doc "The ephemeral port the proxy listens on."
  @spec port(t()) :: :inet.port_number()
  def port(proxy), do: GenServer.call(proxy, :port)

  @doc """
  Synchronizes every stream monitor (so any in-flight frame is processed) and
  returns the violations collected so far, most recent last.
  """
  @spec violations(t()) :: [Accord.Violation.t()]
  def violations(proxy), do: GenServer.call(proxy, :violations)

  @impl true
  def init(bandit_port) do
    {:ok, lsock} =
      :gen_tcp.listen(0, [:binary, active: false, reuseaddr: true, packet: :raw])

    {:ok, port} = :inet.port(lsock)
    sink = spawn_link(&drain/0)
    parent = self()
    _acceptor = spawn_link(fn -> accept_loop(lsock, parent) end)

    {:ok,
     %{
       lsock: lsock,
       port: port,
       bandit_port: bandit_port,
       sink: sink,
       client: nil,
       server: nil,
       cbuf: "",
       sbuf: "",
       preface_done: false,
       monitors: %{}
     }}
  end

  @impl true
  def handle_call(:port, _from, state), do: {:reply, state.port, state}

  def handle_call(:violations, _from, state) do
    # Sync each monitor so casts/events already sent are handled before draining.
    for {_sid, mon} <- state.monitors, do: :sys.get_state(mon)
    {:reply, ViolationCollector.drain(), state}
  end

  @impl true
  def handle_info({:client_connected, csock}, state) do
    {:ok, ssock} =
      :gen_tcp.connect(~c"localhost", state.bandit_port, [:binary, active: :once])

    :ok = :inet.setopts(csock, active: :once)
    {:noreply, %{state | client: csock, server: ssock}}
  end

  def handle_info({:tcp, csock, data}, %{client: csock, server: ssock} = state) do
    :ok = :gen_tcp.send(ssock, data)
    state = tap_client(state, data)
    :inet.setopts(csock, active: :once)
    {:noreply, state}
  end

  def handle_info({:tcp, ssock, data}, %{server: ssock, client: csock} = state) do
    :ok = :gen_tcp.send(csock, data)
    state = tap_server(state, data)
    :inet.setopts(ssock, active: :once)
    {:noreply, state}
  end

  def handle_info({:tcp_closed, _sock}, state) do
    # Keep monitors and collected violations available for `violations/1`.
    {:noreply, state}
  end

  def handle_info({:tcp_error, _sock, _reason}, state), do: {:noreply, state}

  # --- tapping ---------------------------------------------------------------

  defp tap_client(state, data) do
    buf = state.cbuf <> data
    {preface_done, buf} = consume_preface(state.preface_done, buf)

    if preface_done do
      {frames, rest} = extract_frames(buf, [])
      state = Enum.reduce(frames, state, &tap_frame(&1, :client, &2))
      %{state | preface_done: true, cbuf: rest}
    else
      %{state | cbuf: buf}
    end
  end

  defp tap_server(state, data) do
    buf = state.sbuf <> data
    {frames, rest} = extract_frames(buf, [])
    state = Enum.reduce(frames, state, &tap_frame(&1, :server, &2))
    %{state | sbuf: rest}
  end

  defp consume_preface(true, buf), do: {true, buf}
  defp consume_preface(false, <<@preface, rest::binary>>), do: {true, rest}
  defp consume_preface(false, buf), do: {false, buf}

  # Peel complete frames (9-byte header + payload) off the front of the buffer.
  defp extract_frames(
         <<len::24, type::8, flags::8, _r::1, sid::31, _payload::binary-size(len), rest::binary>>,
         acc
       ) do
    extract_frames(rest, [{type, flags, sid} | acc])
  end

  defp extract_frames(buffer, acc), do: {Enum.reverse(acc), buffer}

  # Connection-level frames (stream id 0) are relayed but not part of the
  # per-stream machine.
  defp tap_frame({_type, _flags, 0}, _dir, state), do: state

  defp tap_frame({type, flags, sid}, dir, state) do
    case frame_message(type, flags, dir) do
      :ignore ->
        state

      {kind, message} ->
        {mon, state} = monitor_for(sid, state)
        feed(mon, kind, message)
        state
    end
  end

  defp feed(mon, :cast, message), do: Monitor.cast(mon, message)
  defp feed(mon, :event, message), do: Accord.event(mon, message)

  defp monitor_for(sid, state) do
    case Map.fetch(state.monitors, sid) do
      {:ok, mon} ->
        {mon, state}

      :error ->
        {:ok, mon} =
          Protocol.Monitor.start_link(
            upstream: state.sink,
            downstream: state.sink,
            violation_policy: {ViolationCollector, :handle}
          )

        {mon, %{state | monitors: Map.put(state.monitors, sid, mon)}}
    end
  end

  # Frame type + END_STREAM flag -> stream-machine message, by direction. Types
  # the machine does not model are ignored (relayed, not tapped).
  defp frame_message(type, flags, :client) do
    es = band(flags, 0x01) == 0x01

    case type do
      # HEADERS
      0x1 -> {:cast, if(es, do: :headers_es, else: :headers)}
      # DATA
      0x0 -> {:cast, if(es, do: :data_es, else: :data)}
      # WINDOW_UPDATE (stream)
      0x8 -> {:cast, :window_update}
      # RST_STREAM
      0x3 -> {:cast, :rst_stream}
      _ -> :ignore
    end
  end

  defp frame_message(type, flags, :server) do
    es = band(flags, 0x01) == 0x01

    case type do
      0x1 -> {:event, if(es, do: :s_headers_es, else: :s_headers)}
      0x0 -> {:event, if(es, do: :s_data_es, else: :s_data)}
      0x8 -> {:event, :s_window_update}
      0x3 -> {:event, :s_rst_stream}
      _ -> :ignore
    end
  end

  defp accept_loop(lsock, parent) do
    case :gen_tcp.accept(lsock) do
      {:ok, csock} ->
        :ok = :gen_tcp.controlling_process(csock, parent)
        send(parent, {:client_connected, csock})
        accept_loop(lsock, parent)

      {:error, :closed} ->
        :ok
    end
  end

  # A no-op sink for the monitors' upstream/downstream: forwarded frames are
  # discarded (the real forwarding is the byte relay above).
  defp drain do
    receive do
      _ -> drain()
    end
  end
end
