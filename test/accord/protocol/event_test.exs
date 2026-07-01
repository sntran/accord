defmodule Accord.Protocol.EventTest do
  @moduledoc """
  The `event` DSL: IR shape and compile-time rules.
  """
  use ExUnit.Case, async: true

  describe "IR shape" do
    test "state events carry kind :event and the goto target in :to" do
      ir = Accord.Test.Feed.Protocol.__ir__()

      data_event = find_transition(ir, :subscribed, :data)
      assert data_event.kind == :event
      assert data_event.to == :subscribed
      assert data_event.branches == []
      assert data_event.guard != nil
      assert data_event.update != nil

      halted_event = find_transition(ir, :subscribed, :halted)
      assert halted_event.kind == :event
      assert halted_event.to == :done
    end

    test "anystate events target :__same__" do
      ir = Accord.Test.Feed.Protocol.__ir__()

      assert [notice] = Enum.filter(ir.anystate, &(&1.kind == :event))
      assert notice.to == :__same__
    end

    test "event payload types are captured" do
      ir = Accord.Test.Feed.Protocol.__ir__()

      data_event = find_transition(ir, :subscribed, :data)
      assert data_event.message_types == [:term]
      assert data_event.message_arg_names == ["item"]
    end

    test "event updates are arity-2 (message, tracks)" do
      ir = Accord.Test.Feed.Protocol.__ir__()

      data_event = find_transition(ir, :subscribed, :data)
      assert is_function(data_event.update.fun, 2)
    end
  end

  describe "compile-time rules" do
    test "state events without goto raise CompileError" do
      assert_raise CompileError, ~r/state events must specify goto:/, fn ->
        defmodule NoGoto do
          use Accord.Protocol, tla: :off

          initial :ready

          state :ready do
            event :tick
          end
        end
      end
    end

    test "anystate events with goto raise CompileError" do
      assert_raise CompileError, ~r/anystate events cannot specify goto:/, fn ->
        defmodule AnystateGoto do
          use Accord.Protocol, tla: :off

          initial :ready
          state :ready, terminal: true

          anystate do
            event :tick, goto: :ready
          end
        end
      end
    end

    test "events declaring replies raise CompileError (E004)" do
      assert_raise CompileError, ~r/events cannot declare replies or branches/, fn ->
        defmodule EventReply do
          use Accord.Protocol, tla: :off

          initial :ready

          state :ready do
            event :tick do
              reply :ok
              goto :ready
            end
          end
        end
      end
    end

    test "events declaring timeout raise CompileError" do
      assert_raise CompileError, ~r/do not support timeout/, fn ->
        defmodule EventTimeout do
          use Accord.Protocol, tla: :off

          initial :ready

          state :ready do
            event :tick do
              goto :ready
              timeout 50
            end
          end
        end
      end
    end

    test "event goto to an undefined state reports E002" do
      error =
        assert_raise CompileError, fn ->
          defmodule EventBadTarget do
            use Accord.Protocol, tla: :off

            initial :ready

            state :ready do
              event :tick, goto: :nowhere
            end
          end
        end

      assert error.description =~ "E002"
      assert error.description =~ ":nowhere"
    end

    test "a call and an event sharing a tag in one state reports E020" do
      error =
        assert_raise CompileError, fn ->
          defmodule TagCollision do
            use Accord.Protocol, tla: :off

            initial :ready

            state :ready do
              on :tick, reply: :ok, goto: :ready
              event :tick, goto: :ready
            end
          end
        end

      assert error.description =~ "E020"
    end
  end

  describe "reachability through events" do
    test "states reachable only via events are not flagged unreachable" do
      # Feed's :done is reachable via the :halted event (and cancel);
      # compile succeeded without W001, but assert the graph directly.
      ir = Accord.Test.Feed.Protocol.__ir__()
      assert [] = Accord.Pass.ValidateReachability.warnings(ir)
    end
  end

  defp find_transition(ir, state_name, tag) do
    ir.states[state_name].transitions
    |> Enum.find(fn t ->
      case t.message_pattern do
        ^tag -> true
        pattern when is_tuple(pattern) -> elem(pattern, 0) == tag
        _ -> false
      end
    end)
  end
end
