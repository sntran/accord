defmodule Accord.Examples.PaymentTest do
  use ExUnit.Case, async: false

  @moduletag :capture_log

  alias Accord.Examples.Payment.{Protocol, Server}
  alias Accord.Monitor
  alias Accord.Test.{FaultyServer, TLACheck}

  defp start(opts \\ []) do
    {:ok, server} = Server.start_link()

    {:ok, monitor} =
      Protocol.Monitor.start_link(
        Keyword.merge([upstream: server, violation_policy: :reject], opts)
      )

    {server, monitor}
  end

  describe "conformance" do
    test "authorize, partial captures, finalize, refunds, close" do
      {_server, monitor} = start(violation_policy: :crash)

      assert :approved = Monitor.call(monitor, {:authorize, 4})
      assert :ok = Monitor.call(monitor, {:capture, 2})
      assert :ok = Monitor.call(monitor, {:capture, 2})
      assert :finalized = Monitor.call(monitor, :finalize)
      assert :ok = Monitor.call(monitor, {:refund, 1})
      assert :ok = Monitor.call(monitor, {:refund, 3})
      assert :closed = Monitor.call(monitor, :close)
    end

    test "void requires no captures" do
      {_server, monitor} = start(violation_policy: :crash)

      assert :approved = Monitor.call(monitor, {:authorize, 4})
      assert :voided = Monitor.call(monitor, :void)
    end
  end

  describe "blame" do
    test "over-capture is client blame on the guard" do
      {_server, monitor} = start()

      assert :approved = Monitor.call(monitor, {:authorize, 2})
      assert {:accord_violation, violation} = Monitor.call(monitor, {:capture, 3})
      assert violation.blame == :client
      assert violation.kind == :guard_failed
    end

    test "cumulative over-capture is caught even when each call fits" do
      {_server, monitor} = start()

      assert :approved = Monitor.call(monitor, {:authorize, 4})
      assert :ok = Monitor.call(monitor, {:capture, 3})
      assert {:accord_violation, violation} = Monitor.call(monitor, {:capture, 3})
      assert violation.kind == :guard_failed
    end

    test "refund before finalize is client blame" do
      {_server, monitor} = start()

      assert :approved = Monitor.call(monitor, {:authorize, 4})
      assert {:accord_violation, violation} = Monitor.call(monitor, {:refund, 1})
      assert violation.blame == :client
      assert violation.kind == :invalid_message
    end

    test "a server replying garbage on finalize is server blame" do
      {:ok, faulty} = FaultyServer.start_link(Server)

      {:ok, monitor} =
        Protocol.Monitor.start_link(upstream: faulty, violation_policy: :reject)

      assert :approved = Monitor.call(monitor, {:authorize, 4})
      assert :ok = Monitor.call(monitor, {:capture, 2})

      FaultyServer.inject_fault(faulty, :wrong_reply_type)
      assert {:accord_violation, violation} = Monitor.call(monitor, :finalize)
      assert violation.blame == :server
      assert violation.kind == :invalid_reply
    end
  end

  describe "model checking" do
    @describetag :tlc
    @describetag :tmp_dir

    test "the correct protocol verifies", %{tmp_dir: tmp_dir} do
      TLACheck.assert_passes(Protocol, tmp_dir: tmp_dir)
    end

    test "the per-call guard bug is caught as the double-capture", %{tmp_dir: tmp_dir} do
      TLACheck.assert_fails(
        Accord.Examples.Payment.ProtocolPercallGuard,
        :invariant,
        tmp_dir: tmp_dir
      )
    end
  end
end
