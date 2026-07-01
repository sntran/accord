defmodule Accord.Protocol.SharedTrackTest do
  @moduledoc """
  The `shared:` track option and the `exclusive` check kind (3a: DSL,
  IR, validation, and single-session honesty).
  """
  use ExUnit.Case, async: true

  import ExUnit.CaptureIO

  describe "shared: tracks" do
    test "shared flag is captured in the IR" do
      warning =
        capture_io(:stderr, fn ->
          defmodule SharedProtocol do
            use Accord.Protocol

            initial :ready

            track :fence, :non_neg_integer, default: 0, shared: true
            track :local, :non_neg_integer, default: 0

            state :ready do
              on :stop, reply: :stopped, goto: :stopped
            end

            state :stopped, terminal: true
          end
        end)

      ir = __MODULE__.SharedProtocol.__ir__()
      assert %{shared: true} = Enum.find(ir.tracks, &(&1.name == :fence))
      assert %{shared: false} = Enum.find(ir.tracks, &(&1.name == :local))

      # W003: shared declared but single-session model checking.
      assert warning =~ "W003"
      assert warning =~ "shared track :fence"
    end
  end

  describe "exclusive checks" do
    test "exclusive is captured with kind :exclusive" do
      warning =
        capture_io(:stderr, fn ->
          defmodule ExclusiveProtocol do
            use Accord.Protocol

            initial :unlocked

            state :unlocked do
              on :acquire, reply: :ok, goto: :locked
            end

            state :locked do
              on :release, reply: :ok, goto: :unlocked
            end

            property :mutual_exclusion do
              exclusive :locked
            end
          end
        end)

      ir = __MODULE__.ExclusiveProtocol.__ir__()
      [prop] = ir.properties
      [check] = prop.checks
      assert check.kind == :exclusive
      assert check.spec.state == :locked

      assert warning =~ "W003"
      assert warning =~ "exclusive check"
    end

    test "the single-session spec annotates exclusive honestly" do
      capture_io(:stderr, fn ->
        defmodule ExclusiveSpecProtocol do
          use Accord.Protocol

          initial :unlocked

          state :unlocked do
            on :acquire, reply: :ok, goto: :locked
          end

          state :locked do
            on :release, reply: :ok, goto: :unlocked
          end

          property :mutual_exclusion do
            exclusive :locked
          end
        end
      end)

      {tla_path, cfg_path} = Accord.TLA.Files.paths(__MODULE__.ExclusiveSpecProtocol)
      tla = File.read!(tla_path)
      cfg = File.read!(cfg_path)

      assert tla =~ "requires multi-session checking"
      # Never asserted by TLC in a single-session model.
      refute cfg =~ "MutualExclusion"
    end

    test "exclusive referencing an undefined state reports E060" do
      error =
        assert_raise CompileError, fn ->
          defmodule BadExclusive do
            use Accord.Protocol, tla: :off

            initial :ready
            state :ready, terminal: true

            property :mutex do
              exclusive :nowhere
            end
          end
        end

      assert error.description =~ "E060"
      assert error.description =~ ":nowhere"
    end
  end

  describe "runtime passthrough" do
    test "exclusive checks are model-only at runtime" do
      capture_io(:stderr, fn ->
        defmodule RuntimeExclusive do
          use Accord.Protocol, tla: :off

          initial :unlocked

          state :unlocked do
            on :acquire, reply: :ok, goto: :locked
          end

          state :locked do
            on :release, reply: :ok, goto: :unlocked
          end

          property :mutual_exclusion do
            exclusive :locked
          end
        end
      end)

      defmodule OkServer do
        use GenServer
        def start_link, do: GenServer.start_link(__MODULE__, nil)
        @impl true
        def init(_), do: {:ok, %{}}
        @impl true
        def handle_call(_msg, _from, state), do: {:reply, :ok, state}
      end

      {:ok, server} = OkServer.start_link()

      {:ok, monitor} =
        Accord.Monitor.start_link(__MODULE__.RuntimeExclusive.__compiled__(),
          upstream: server,
          violation_policy: :crash
        )

      # The check never fires at runtime — a single monitor cannot
      # observe other sessions.
      assert :ok = Accord.Monitor.call(monitor, :acquire)
      assert :ok = Accord.Monitor.call(monitor, :release)
      assert :ok = Accord.Monitor.call(monitor, :acquire)
    end
  end
end
