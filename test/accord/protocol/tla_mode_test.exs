defmodule Accord.Protocol.TLAModeTest do
  @moduledoc """
  Tests for the `tla:` compilation mode option.

  Spec generation failures must never silently produce a checkable-looking
  protocol: `:strict` (the default) aborts compilation, `:warn` records the
  failure in `__tla_status__/0` and deletes any stale spec, `:off` skips
  generation entirely.
  """
  use ExUnit.Case, async: true

  import ExUnit.CaptureIO

  alias Accord.TLA.Files

  describe "tla: :off" do
    defmodule OffProtocol do
      use Accord.Protocol, tla: :off

      initial :ready

      state :ready do
        on :stop, reply: :stopped, goto: :stopped
      end

      state :stopped, terminal: true
    end

    test "reports :off status" do
      assert OffProtocol.__tla_status__() == :off
    end

    test "writes no spec files" do
      {tla_path, cfg_path} = Files.paths(OffProtocol)

      refute File.exists?(tla_path)
      refute File.exists?(cfg_path)
    end
  end

  describe "tla: :warn" do
    test "downgrades generation failure to a warning and records it" do
      mod = Module.concat(__MODULE__, WarnProtocol)

      # Simulate a stale spec from a previous successful compile: it must
      # be deleted, or `mix accord.check` would verify the old spec.
      Files.write(mod, %{tla: "---- MODULE stale ----", cfg: "SPECIFICATION Spec"})

      warning =
        capture_io(:stderr, fn ->
          defmodule WarnProtocol do
            use Accord.Protocol, tla: :warn

            initial :ready

            # Default 1000 is outside the built-in 0..3 domain, which fails
            # spec generation deterministically.
            track :n, :non_neg_integer, default: 1000

            state :ready do
              on :stop, reply: :stopped, goto: :stopped
            end

            state :stopped, terminal: true
          end
        end)

      assert warning =~ "TLA+ compilation failed"

      assert {:error, summary} = mod.__tla_status__()
      assert summary =~ "outside its model domain"

      {tla_path, cfg_path} = Files.paths(mod)
      refute File.exists?(tla_path)
      refute File.exists?(cfg_path)
    end
  end

  describe "tla: :strict (default)" do
    test "aborts compilation when spec generation fails" do
      assert_raise ArgumentError, ~r/outside its model domain/, fn ->
        defmodule StrictProtocol do
          use Accord.Protocol

          initial :ready

          track :n, :non_neg_integer, default: 1000

          state :ready do
            on :stop, reply: :stopped, goto: :stopped
          end

          state :stopped, terminal: true
        end
      end
    end

    test "reports :ok status when generation succeeds" do
      defmodule GoodProtocol do
        use Accord.Protocol

        initial :ready

        state :ready do
          on :stop, reply: :stopped, goto: :stopped
        end

        state :stopped, terminal: true
      end

      assert GoodProtocol.__tla_status__() == :ok

      {tla_path, cfg_path} = Files.paths(GoodProtocol)
      assert File.exists?(tla_path)
      assert File.exists?(cfg_path)
    end
  end

  describe "invalid tla: option" do
    test "raises CompileError" do
      assert_raise CompileError, ~r/invalid tla: option :sometimes/, fn ->
        defmodule InvalidModeProtocol do
          use Accord.Protocol, tla: :sometimes

          initial :ready

          state :ready, terminal: true
        end
      end
    end
  end
end
