defmodule Accord.Monitor.EventTest do
  @moduledoc """
  Server-push events through the monitor.

  Everything a pushed event violates blames the server — it is the
  sender. Valid events are forwarded to the downstream pid.
  """
  use ExUnit.Case, async: false

  @moduletag :capture_log

  alias Accord.Monitor
  alias Accord.Test.ViolationCollector

  defmodule FeedServer do
    use GenServer

    def start_link, do: GenServer.start_link(__MODULE__, nil)

    @impl true
    def init(_), do: {:ok, %{}}

    @impl true
    def handle_call({:ask, _n}, _from, state), do: {:reply, :ok, state}
    def handle_call(:cancel, _from, state), do: {:reply, :cancelled, state}
  end

  defp start_feed(opts \\ []) do
    {:ok, server} = FeedServer.start_link()
    ViolationCollector.init()

    {:ok, monitor} =
      Monitor.start_link(
        Accord.Test.Feed.Protocol.__compiled__(),
        Keyword.merge(
          [
            upstream: server,
            downstream: self(),
            violation_policy: {ViolationCollector, :handle}
          ],
          opts
        )
      )

    monitor
  end

  defp monitor_state(monitor) do
    {state, _data} = :sys.get_state(monitor)
    state
  end

  defp demand(monitor) do
    {_state, data} = :sys.get_state(monitor)
    data.tracks.demand
  end

  describe "valid events" do
    test "a guarded event is validated, applied, and forwarded downstream" do
      monitor = start_feed()

      assert :ok = Monitor.call(monitor, {:ask, 2})
      assert demand(monitor) == 2

      Monitor.event(monitor, {:data, :item_1})
      assert_receive {:data, :item_1}

      assert demand(monitor) == 1
      assert ViolationCollector.drain() == []
    end

    test "an event goto changes the protocol state" do
      monitor = start_feed()

      Monitor.event(monitor, :halted)
      assert_receive :halted

      assert monitor_state(monitor) == :done
      assert ViolationCollector.drain() == []
    end

    test "anystate events stay in the current state" do
      monitor = start_feed()

      Monitor.event(monitor, :server_notice)
      assert_receive :server_notice

      assert monitor_state(monitor) == :subscribed
      assert ViolationCollector.drain() == []
    end

    test "nil downstream validates without forwarding" do
      monitor = start_feed(downstream: nil)

      assert :ok = Monitor.call(monitor, {:ask, 1})
      Monitor.event(monitor, {:data, :item})

      refute_receive {:data, :item}
      assert demand(monitor) == 0
      assert ViolationCollector.drain() == []
    end
  end

  describe "server blame" do
    test "unknown event tag is :invalid_event" do
      monitor = start_feed()

      Monitor.event(monitor, {:surprise, 1})
      # Synchronous barrier.
      _ = :sys.get_state(monitor)

      assert [violation] = ViolationCollector.drain()
      assert violation.kind == :invalid_event
      assert violation.blame == :server
      # Not forwarded.
      refute_receive {:surprise, 1}
    end

    test "pushing a call tag as an event is :invalid_event" do
      monitor = start_feed()

      Monitor.event(monitor, {:ask, 1})
      _ = :sys.get_state(monitor)

      assert [violation] = ViolationCollector.drain()
      assert violation.kind == :invalid_event
      assert violation.blame == :server
    end

    test "event guard failure blames the server" do
      monitor = start_feed()

      # No demand — pushing data violates the event guard.
      Monitor.event(monitor, {:data, :item})
      _ = :sys.get_state(monitor)

      assert [violation] = ViolationCollector.drain()
      assert violation.kind == :guard_failed
      assert violation.blame == :server
      refute_receive {:data, :item}
    end

    test "event after terminal state blames the server" do
      monitor = start_feed()

      Monitor.event(monitor, :halted)
      assert_receive :halted
      assert monitor_state(monitor) == :done

      Monitor.event(monitor, :server_notice)
      _ = :sys.get_state(monitor)

      assert [violation] = ViolationCollector.drain()
      assert violation.kind == :session_ended
      assert violation.blame == :server
    end
  end

  describe "direction enforcement" do
    test "calling an event tag as a call blames the client" do
      monitor = start_feed(violation_policy: :reject)

      assert {:accord_violation, violation} = Monitor.call(monitor, :halted)
      assert violation.kind == :invalid_message
      assert violation.blame == :client
    end
  end

  describe "role labeling" do
    defmodule RolesProtocol do
      use Accord.Protocol, tla: :off

      role :consumer
      role :producer

      initial :ready

      state :ready do
        on :ping, reply: :pong, goto: :ready
        event :tick, goto: :ready
      end
    end

    defmodule PongServer do
      use GenServer

      def start_link, do: GenServer.start_link(__MODULE__, nil)

      @impl true
      def init(_), do: {:ok, %{}}

      @impl true
      def handle_call(:ping, _from, state), do: {:reply, :pong, state}
    end

    test "client blame carries the first declared role" do
      {:ok, server} = PongServer.start_link()

      {:ok, monitor} =
        Monitor.start_link(RolesProtocol.__compiled__(),
          upstream: server,
          violation_policy: :reject
        )

      assert {:accord_violation, violation} = Monitor.call(monitor, :unknown)
      assert violation.blame == :client
      assert violation.context.role == :consumer
    end

    test "server blame carries the second declared role" do
      {:ok, server} = PongServer.start_link()
      ViolationCollector.init()

      {:ok, monitor} =
        Monitor.start_link(RolesProtocol.__compiled__(),
          upstream: server,
          violation_policy: {ViolationCollector, :handle}
        )

      Monitor.event(monitor, :surprise)
      _ = :sys.get_state(monitor)

      assert [violation] = ViolationCollector.drain()
      assert violation.blame == :server
      assert violation.context.role == :producer
    end

    test "without declared roles, no role is attached" do
      monitor = start_feed(violation_policy: :reject)

      assert {:accord_violation, violation} = Monitor.call(monitor, :unknown)
      refute Map.has_key?(violation.context, :role)
    end
  end

  describe "properties over events" do
    test "an event that violates an invariant still transitions and reports" do
      {:ok, server} = FeedServer.start_link()
      ViolationCollector.init()

      {:ok, monitor} =
        Monitor.start_link(Accord.Test.FeedUnguarded.Protocol.__compiled__(),
          upstream: server,
          downstream: self(),
          violation_policy: {ViolationCollector, :handle}
        )

      # No guard in the unguarded variant: demand goes to -1.
      Monitor.event(monitor, {:data, :item})
      assert_receive {:data, :item}

      assert [violation] = ViolationCollector.drain()
      assert violation.kind == :invariant_violated
      assert violation.blame == :property
      assert demand(monitor) == -1
    end
  end
end
