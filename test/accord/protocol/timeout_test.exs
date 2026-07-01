defmodule Accord.Protocol.TimeoutTest do
  @moduledoc """
  Per-transition `timeout:` — DSL parsing and monitor enforcement.
  """
  use ExUnit.Case, async: false

  @moduletag :capture_log

  alias Accord.Monitor

  defmodule TimeoutProtocol do
    use Accord.Protocol

    initial :ready

    state :ready do
      on :slow_op, reply: :done, goto: :ready, timeout: 50

      on :slow_block_op do
        reply :done
        goto :ready
        timeout 60
      end

      on :normal_op, reply: :done, goto: :ready
      on :stop, reply: :stopped, goto: :stopped
    end

    state :stopped, terminal: true

    anystate do
      on :quick_ping, reply: :pong, timeout: 40
    end
  end

  defmodule SlowServer do
    use GenServer

    def start_link, do: GenServer.start_link(__MODULE__, nil)

    @impl true
    def init(_), do: {:ok, %{}}

    @impl true
    def handle_call(:slow_op, _from, state) do
      Process.sleep(200)
      {:reply, :done, state}
    end

    def handle_call(:normal_op, _from, state), do: {:reply, :done, state}
    def handle_call(:stop, _from, state), do: {:reply, :stopped, state}
  end

  describe "DSL parsing" do
    test "keyword form sets call_timeout" do
      ir = TimeoutProtocol.__ir__()
      transition = find_transition(ir, :slow_op)

      assert transition.call_timeout == 50
    end

    test "block form timeout macro sets call_timeout" do
      ir = TimeoutProtocol.__ir__()
      transition = find_transition(ir, :slow_block_op)

      assert transition.call_timeout == 60
    end

    test "omitted timeout leaves call_timeout nil" do
      ir = TimeoutProtocol.__ir__()
      transition = find_transition(ir, :normal_op)

      assert transition.call_timeout == nil
    end

    test "anystate keyword form sets call_timeout" do
      ir = TimeoutProtocol.__ir__()
      [transition] = ir.anystate

      assert transition.call_timeout == 40
    end
  end

  describe "monitor enforcement" do
    test "per-transition timeout overrides the monitor default" do
      {:ok, server} = SlowServer.start_link()

      # Monitor default is generous; the transition's 50ms must win.
      {:ok, monitor} =
        Monitor.start_link(TimeoutProtocol.__compiled__(),
          upstream: server,
          call_timeout: 5_000,
          violation_policy: :reject
        )

      assert {:accord_violation, violation} = Monitor.call(monitor, :slow_op)
      assert violation.kind == :timeout
      assert violation.blame == :server
      assert violation.context.timeout_ms == 50
    end

    test "transitions without a timeout use the monitor default" do
      {:ok, server} = SlowServer.start_link()

      {:ok, monitor} =
        Monitor.start_link(TimeoutProtocol.__compiled__(),
          upstream: server,
          call_timeout: 5_000,
          violation_policy: :reject
        )

      assert :done = Monitor.call(monitor, :normal_op)
    end
  end

  defp find_transition(ir, tag) do
    ir.states
    |> Enum.flat_map(fn {_name, state} -> state.transitions end)
    |> Enum.find(fn t ->
      case t.message_pattern do
        ^tag -> true
        pattern when is_tuple(pattern) -> elem(pattern, 0) == tag
        _ -> false
      end
    end)
  end
end
