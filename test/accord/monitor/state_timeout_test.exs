defmodule Accord.Monitor.StateTimeoutTest do
  @moduledoc """
  State timeouts: DSL, validation, monitor firing semantics, and the
  TLA+ internal action.
  """
  use ExUnit.Case, async: false

  @moduletag :capture_log

  alias Accord.Monitor
  alias Accord.TLA.{Compiler, ModelConfig}

  defmodule TimerProtocol do
    use Accord.Protocol

    initial :active

    track :renewals, :non_neg_integer, default: 0, domain: 0..3

    state :active do
      state_timeout 50, goto: :expired

      # Renewals self-loop; the timeout is the ONLY exit, which is what
      # makes `active ~> expired` true. (Adding a `close` exit here would
      # give TLC a legitimate counterexample: close before expiry.)
      on :renew do
        guard fn :renew, tracks -> tracks.renewals < 3 end
        reply :ok
        goto :active
        update fn :renew, _reply, tracks -> %{tracks | renewals: tracks.renewals + 1} end
      end
    end

    state :expired do
      on :reopen, reply: :ok, goto: :active
      on :close, reply: :closed, goto: :done
    end

    state :done, terminal: true

    property :eventually_expires do
      liveness in_state(:active), leads_to: in_state(:expired)
    end
  end

  defmodule EchoServer do
    use GenServer

    def start_link, do: GenServer.start_link(__MODULE__, nil)

    @impl true
    def init(_), do: {:ok, %{}}

    @impl true
    def handle_call(:renew, _from, state), do: {:reply, :ok, state}
    def handle_call(:reopen, _from, state), do: {:reply, :ok, state}
    def handle_call(:close, _from, state), do: {:reply, :closed, state}
  end

  defp start_monitor do
    {:ok, server} = EchoServer.start_link()

    {:ok, monitor} =
      TimerProtocol.Monitor.start_link(upstream: server, violation_policy: :crash)

    monitor
  end

  defp wait_for_state(monitor, expected, attempts \\ 50) do
    {state, _data} = :sys.get_state(monitor)

    cond do
      state == expected -> :ok
      attempts == 0 -> flunk("never reached #{inspect(expected)}, still in #{inspect(state)}")
      true -> Process.sleep(10) && wait_for_state(monitor, expected, attempts - 1)
    end
  end

  describe "IR" do
    test "the state carries its timeout" do
      ir = TimerProtocol.__ir__()

      assert ir.states[:active].state_timeout == {50, :expired}
      assert ir.states[:expired].state_timeout == nil
    end
  end

  describe "monitor firing" do
    test "the initial state's timer is armed and fires" do
      monitor = start_monitor()

      wait_for_state(monitor, :expired)
    end

    test "self-loop transitions keep the running timer" do
      monitor = start_monitor()

      # Renewing stays in :active — the cooldown keeps ticking rather
      # than resetting, so the timeout still fires.
      assert :ok = Monitor.call(monitor, :renew)
      assert :ok = Monitor.call(monitor, :renew)

      wait_for_state(monitor, :expired)
    end

    test "leaving the state cancels the timer" do
      monitor = start_monitor()

      # Wait out the first expiry, then close from :expired — no timer
      # is armed there, and none fires afterwards.
      wait_for_state(monitor, :expired)
      assert :closed = Monitor.call(monitor, :close)
      Process.sleep(80)

      assert {:done, _} = :sys.get_state(monitor)
    end

    test "re-entering the state re-arms the timer" do
      monitor = start_monitor()

      wait_for_state(monitor, :expired)
      assert :ok = Monitor.call(monitor, :reopen)
      wait_for_state(monitor, :expired)
    end
  end

  describe "TLA+ emission" do
    test "the timeout is an internal action, weakly fair under liveness" do
      ir = TimerProtocol.__ir__()
      {:ok, result} = Compiler.compile(ir, %ModelConfig{domains: %{renewals: 0..3}})

      assert result.tla =~ "AfterActiveToExpired =="
      assert result.tla =~ ~s(state = "active")
      # The timer's weak fairness now lives inside the liveness property's
      # own implication rather than a shared FairSpec (H3).
      assert result.tla =~ "WF_vars(AfterActiveToExpired)"
      assert result.cfg =~ "SPECIFICATION Spec"
      refute result.cfg =~ "SPECIFICATION FairSpec"
    end

    test "a timeout on the trigger state discharges W005" do
      ir = TimerProtocol.__ir__()

      assert [] = Accord.Pass.ValidateProperties.warnings(ir)
    end
  end

  describe "validation" do
    test "timeout targeting an undefined state reports E002" do
      error =
        assert_raise CompileError, fn ->
          defmodule BadTarget do
            use Accord.Protocol, tla: :off

            initial :ready

            state :ready do
              state_timeout 50, goto: :nowhere
              on :stop, reply: :stopped, goto: :done
            end

            state :done, terminal: true
          end
        end

      assert error.description =~ "E002"
      assert error.description =~ ":nowhere"
    end

    test "timeout targeting the same state reports E005" do
      error =
        assert_raise CompileError, fn ->
          defmodule SelfTarget do
            use Accord.Protocol, tla: :off

            initial :ready

            state :ready do
              state_timeout 50, goto: :ready
              on :stop, reply: :stopped, goto: :done
            end

            state :done, terminal: true
          end
        end

      assert error.description =~ "E005"
    end

    test "duplicate timeouts in one state raise at compile time" do
      assert_raise CompileError, ~r/duplicate state_timeout/, fn ->
        defmodule DuplicateTimer do
          use Accord.Protocol, tla: :off

          initial :ready

          state :ready do
            state_timeout 50, goto: :done
            state_timeout 60, goto: :done
            on :stop, reply: :stopped, goto: :done
          end

          state :done, terminal: true
        end
      end
    end
  end

  describe "model checking" do
    @describetag :tmp_dir

    test "the timeout's fairness proves the liveness property", %{tmp_dir: tmp_dir} do
      Accord.Test.TLACheck.assert_passes(TimerProtocol,
        tmp_dir: tmp_dir,
        model_config: %ModelConfig{domains: %{renewals: 0..3}}
      )
    end
  end
end
