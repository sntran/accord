defmodule Accord.Examples.CircuitBreakerTest do
  use ExUnit.Case, async: false

  @moduletag :capture_log

  alias Accord.Examples.CircuitBreaker.{MislabelingServer, Protocol, Server}
  alias Accord.Monitor
  alias Accord.Test.TLACheck

  describe "conformance" do
    test "trip and reject — the cooldown then fires on its own" do
      {:ok, server} = Server.start_link()

      {:ok, monitor} =
        Protocol.Monitor.start_link(upstream: server, violation_policy: :crash)

      Server.push_outcomes(server, [:error, :error, :error])

      assert :error = Monitor.call(monitor, :request)
      assert :error = Monitor.call(monitor, :request)
      assert :tripped = Monitor.call(monitor, :request)
      assert {:rejected, :circuit_open} = Monitor.call(monitor, :request)
      assert {:open, _} = :sys.get_state(monitor)
      # The 30s state_timeout is armed; firing is exercised with a short
      # timer in test/accord/monitor/state_timeout_test.exs.
    end
  end

  describe "blame" do
    test "an unknown client message is client blame" do
      {:ok, server} = Server.start_link()

      {:ok, monitor} =
        Protocol.Monitor.start_link(upstream: server, violation_policy: :reject)

      assert {:accord_violation, violation} = Monitor.call(monitor, :force_reset)
      assert violation.blame == :client
      assert violation.kind == :invalid_message
    end

    test "server mislabeling the tripping failure is server blame" do
      {:ok, server} = MislabelingServer.start_link()

      {:ok, monitor} =
        Protocol.Monitor.start_link(upstream: server, violation_policy: :reject)

      assert :error = Monitor.call(monitor, :request)
      assert :error = Monitor.call(monitor, :request)

      # Third failure must be labeled :tripped; a plain :error violates
      # the where: failures < 2 constraint.
      assert {:accord_violation, violation} = Monitor.call(monitor, :request)
      assert violation.blame == :server
      assert violation.kind == :constraint_failed
    end
  end

  describe "model checking" do
    @describetag :tlc
    @describetag :tmp_dir

    test "the correct protocol verifies", %{tmp_dir: tmp_dir} do
      TLACheck.assert_passes(Protocol, tmp_dir: tmp_dir)
    end

    test "the stuck-counter bug is caught as an invariant violation", %{tmp_dir: tmp_dir} do
      TLACheck.assert_fails(
        Accord.Examples.CircuitBreaker.ProtocolStuckCounter,
        :invariant,
        tmp_dir: tmp_dir
      )
    end
  end
end
