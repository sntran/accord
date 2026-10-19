defmodule Accord.Examples.Http2Test do
  use ExUnit.Case, async: false

  @moduletag :capture_log

  alias Accord.Examples.Http2
  alias Accord.Monitor
  alias Accord.Test.{TLACheck, ViolationCollector}

  # A minimal upstream for the stream FSM: casts just forward, so a no-op server
  # is enough to exercise the monitor's validation and blame.
  defmodule NoopServer do
    use GenServer

    def start_link, do: GenServer.start_link(__MODULE__, nil)
    @impl true
    def init(state), do: {:ok, state}
    @impl true
    def handle_cast(_message, state), do: {:noreply, state}
    @impl true
    def handle_call(_message, _from, state), do: {:reply, :ok, state}
  end

  describe "stream FSM runtime (the monitor applies to a frame protocol)" do
    setup do
      ViolationCollector.init()
      {:ok, server} = NoopServer.start_link()

      {:ok, monitor} =
        Http2.Stream.Protocol.Monitor.start_link(
          upstream: server,
          downstream: self(),
          violation_policy: {ViolationCollector, :handle}
        )

      %{monitor: monitor}
    end

    test "a legal frame sequence advances the stream through its states", %{monitor: monitor} do
      # HEADERS opens the stream; DATA keeps it open; a terminating DATA
      # (END_STREAM) half-closes it.
      Monitor.cast(monitor, :headers)
      Monitor.cast(monitor, :data)
      Monitor.cast(monitor, :data_es)
      {state, _data} = :sys.get_state(monitor)

      assert state == :remote_closed
      assert ViolationCollector.drain() == []
    end

    test "a frame with no transition in the current state is client blame", %{monitor: monitor} do
      # DATA in :idle has no transition — the peer sent an illegal frame.
      Monitor.cast(monitor, :data)
      :sys.get_state(monitor)

      assert [violation] = ViolationCollector.drain()
      assert violation.kind == :invalid_message
      assert violation.blame == :client
    end

    test "a server-push frame is delivered downstream", %{monitor: monitor} do
      Monitor.cast(monitor, :headers)
      Accord.event(monitor, :s_data)
      :sys.get_state(monitor)

      assert_receive :s_data
      assert ViolationCollector.drain() == []
    end
  end

  describe "live divergence detection (accord between a client and Bandit)" do
    alias Accord.Examples.Http2.{EchoServer, RawClient, TapProxy}

    setup do
      {:ok, server, bandit_port} = EchoServer.start_link()
      on_exit(fn -> if Process.alive?(server), do: Process.exit(server, :shutdown) end)
      ViolationCollector.init()
      {:ok, proxy} = TapProxy.start_link(bandit_port)
      %{proxy: proxy, port: TapProxy.port(proxy)}
    end

    test "a well-formed request produces no violations", %{proxy: proxy, port: port} do
      # The monitor must be faithful to real traffic — a legitimate request,
      # including whatever flow-control frames Bandit sends, raises nothing.
      conn = RawClient.connect(port)
      conn = RawClient.post_echo(conn, 1, false, port)
      conn = RawClient.data(conn, 1, true, "OK")

      assert RawClient.read_body(conn) == "OK"
      assert TapProxy.violations(proxy) == []
    end

    test "a header block split across HEADERS + CONTINUATION is assembled, not flagged",
         %{proxy: proxy, port: port} do
      # §6.10: the request headers arrive as HEADERS (no END_HEADERS) + a
      # CONTINUATION. The tap assembles the block and emits one :headers message
      # only when END_HEADERS completes it — so this well-formed split request
      # raises nothing (faithfulness is earned, not had by ignoring CONTINUATION).
      conn = RawClient.connect(port)
      conn = RawClient.post_echo_split(conn, 1, port)
      conn = RawClient.data(conn, 1, true, "OK")

      assert RawClient.read_body(conn) == "OK"
      assert TapProxy.violations(proxy) == []
    end

    test "trailers without END_STREAM: Bandit fails to reset and accord blames the server (§8.1)",
         %{proxy: proxy, port: port} do
      conn = RawClient.connect(port)
      conn = RawClient.post_echo(conn, 1, false, port)
      conn = RawClient.data(conn, 1, false, "OK")
      # The divergent frame: a trailing HEADERS frame without END_STREAM.
      conn = RawClient.headers(conn, 1, false, [{"x-trailer", "t"}])
      conn = RawClient.data(conn, 1, true, "MORE")

      # Bandit answers 200 and folds the post-trailer DATA into the body, where
      # §8.1 requires it to reset the stream.
      assert RawClient.read_body(conn) == "OKMORE"

      # accord catches that directly: the malformed trailers put the stream in
      # :reset_expected, where the server owes a RST_STREAM — so Bandit's response
      # frames are server-blame violations. This is accord judging the server, not
      # inferring the bug from the body assertion above.
      # A server-push frame with no transition is an :invalid_event (blame
      # :server); accord expected :s_rst_stream and got a normal response.
      violations = TapProxy.violations(proxy)
      assert Enum.any?(violations, &(&1.blame == :server and &1.kind == :invalid_event))
      refute Enum.any?(violations, &(&1.blame == :client))
    end

    test "a lower stream id: Bandit fails to go away and accord blames the server (§5.1.1)",
         %{proxy: proxy, port: port} do
      conn = RawClient.connect(port)

      # Open and complete stream 3 — the connection's high-water mark.
      conn = RawClient.post_echo(conn, 3, false, port)
      conn = RawClient.data(conn, 3, true, "x")
      assert RawClient.read_body(conn) == "x"

      # A HEADERS on the lower stream 1 is a §5.1.1 protocol error. The
      # connection monitor's branching cast routes it to :goaway_expected, where
      # the server owes a GOAWAY. Bandit silently drops the frame instead.
      conn = RawClient.post_echo(conn, 1, false, port)

      # The drop is inaction, so we provoke: a compliant server would be going
      # away, but Bandit ACKs the PING — carrying on where it should have closed.
      conn = RawClient.ping(conn)
      assert :ok = RawClient.await_ping_ack(conn)

      # The PING ACK arriving in :goaway_expected is a server-blame violation.
      violations = TapProxy.violations(proxy)
      assert Enum.any?(violations, &(&1.blame == :server and &1.kind == :invalid_event))
    end
  end

  describe "model checking" do
    @describetag :tmp_dir

    test "the stream FSM verifies (§5.1)", %{tmp_dir: tmp_dir} do
      TLACheck.assert_passes(Http2.Stream.Protocol, tmp_dir: tmp_dir)
    end

    test "the stream-id fence verifies (§5.1.1)", %{tmp_dir: tmp_dir} do
      TLACheck.assert_passes(Http2.StreamId.Protocol, tmp_dir: tmp_dir)
    end

    test "the connection stream-id monitor verifies (§5.1.1)", %{tmp_dir: tmp_dir} do
      TLACheck.assert_passes(Http2.StreamIdMonitor.Protocol, tmp_dir: tmp_dir)
    end

    test "the send-window overflow guard verifies (§6.9.1)", %{tmp_dir: tmp_dir} do
      TLACheck.assert_passes(Http2.FlowControl.Protocol, tmp_dir: tmp_dir)
    end

    test "the connection GOAWAY gate verifies (§6.8)", %{tmp_dir: tmp_dir} do
      TLACheck.assert_passes(Http2.Connection.Protocol, tmp_dir: tmp_dir)
    end
  end
end
