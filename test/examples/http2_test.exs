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

  describe "model checking" do
    @describetag :tlc
    @describetag :tmp_dir

    test "the stream FSM verifies", %{tmp_dir: tmp_dir} do
      TLACheck.assert_passes(Http2.Stream.Protocol, tmp_dir: tmp_dir)
    end

    test "the trailers-without-END_STREAM bug is caught (§8.1)", %{tmp_dir: tmp_dir} do
      TLACheck.assert_fails(Http2.Stream.TrailersBug, :invariant, tmp_dir: tmp_dir)
    end

    test "the stream-id fence verifies (§5.1.1)", %{tmp_dir: tmp_dir} do
      TLACheck.assert_passes(Http2.StreamId.Protocol, tmp_dir: tmp_dir)
    end

    test "dropping the id guard lets two streams share an id", %{tmp_dir: tmp_dir} do
      TLACheck.assert_fails(Http2.StreamId.Unguarded, :invariant, tmp_dir: tmp_dir)
    end

    test "the send-window overflow guard verifies (§6.9.1)", %{tmp_dir: tmp_dir} do
      TLACheck.assert_passes(Http2.FlowControl.Protocol, tmp_dir: tmp_dir)
    end

    test "dropping the overflow guard lets the window overflow", %{tmp_dir: tmp_dir} do
      TLACheck.assert_fails(Http2.FlowControl.Unguarded, :invariant, tmp_dir: tmp_dir)
    end

    test "the connection GOAWAY gate verifies (§6.8)", %{tmp_dir: tmp_dir} do
      TLACheck.assert_passes(Http2.Connection.Protocol, tmp_dir: tmp_dir)
    end

    test "dropping the gate lets a stream open after GOAWAY", %{tmp_dir: tmp_dir} do
      TLACheck.assert_fails(Http2.Connection.Unguarded, :invariant, tmp_dir: tmp_dir)
    end
  end
end
