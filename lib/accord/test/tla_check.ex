defmodule Accord.Test.TLACheck do
  @moduledoc """
  Test assertions for TLA+ model checking.

  Provides helpers for model checking protocol modules and asserting that
  the check either passes or fails with the expected violation kind.

  The check runs on `Accord.TLA.Engine`: the native checker by default (no
  Java), or TLC with `engine: :tlc` (or `ACCORD_TLA_ENGINE=tlc`).

  ## Usage in tests

      @moduletag :tmp_dir

      test "counter passes", %{tmp_dir: tmp_dir} do
        assert_passes(Accord.Test.Counter.Protocol, tmp_dir: tmp_dir)
      end

      test "invariant fails", %{tmp_dir: tmp_dir} do
        assert_fails(Accord.Test.InvariantFail.Protocol, :invariant, tmp_dir: tmp_dir)
      end

  ## TLC

  `tlc_available?/0` tells if TLC can run (Java and `tla2tools.jar`, in
  the same locations as `mix accord.check`). Only tests that compare with
  TLC need it.
  """

  alias Accord.TLA.{Compiler, Engine, ModelConfig}

  @doc """
  Returns `true` if Java and `tla2tools.jar` are both available.
  """
  @spec tlc_available?() :: boolean()
  def tlc_available?, do: Engine.tlc_available?()

  @doc """
  Compiles TLA+ from the protocol's IR, checks it, and asserts success.

  Raises `ExUnit.AssertionError` if model checking finds any violation.

  ## Options

  - `:tmp_dir` (required) — working directory for TLA+ files
  - `:engine` — `:native` (default) or `:tlc`
  - `:model_config` — a `%ModelConfig{}` struct (overrides file-based config)
  - `:model_config_path` — path to a model config file
  - `:check_deadlock` — when `false`, disables deadlock checking
    (default: `true` — generated specs give terminal states a
    `Terminating` self-stutter, so reported deadlocks are real)
  """
  @spec assert_passes(module(), keyword()) :: :ok
  def assert_passes(protocol_mod, opts) do
    tmp_dir = Keyword.fetch!(opts, :tmp_dir)
    result = run_check(protocol_mod, tmp_dir, opts)

    case result do
      {:ok, _stats} ->
        :ok

      {:error, violation, _stats} ->
        raise ExUnit.AssertionError,
          message:
            "expected model checking to pass, but got #{violation.kind} violation" <>
              if(violation.property, do: " (#{violation.property})", else: "") <>
              format_trace_summary(violation.trace)
    end
  end

  @doc """
  Compiles TLA+ from the protocol's IR, checks it, and asserts failure
  with the expected violation kind.

  Raises `ExUnit.AssertionError` if model checking passes or fails with
  a different violation kind.

  ## Options

  Same as `assert_passes/2`.
  """
  @spec assert_fails(module(), atom(), keyword()) :: :ok
  def assert_fails(protocol_mod, expected_kind, opts) do
    tmp_dir = Keyword.fetch!(opts, :tmp_dir)
    result = run_check(protocol_mod, tmp_dir, opts)

    case result do
      {:ok, _stats} ->
        raise ExUnit.AssertionError,
          message: "expected #{expected_kind} violation, but model checking passed"

      {:error, %{kind: ^expected_kind}, _stats} ->
        :ok

      {:error, %{kind: actual_kind} = violation, _stats} ->
        raise ExUnit.AssertionError,
          message:
            "expected #{expected_kind} violation, but got #{actual_kind}" <>
              if(violation.property, do: " (#{violation.property})", else: "") <>
              format_trace_summary(violation.trace)
    end
  end

  # -- Internals --

  defp run_check(protocol_mod, tmp_dir, opts) do
    ir = protocol_mod.__ir__()
    config = protocol_mod |> resolve_config(opts) |> ModelConfig.apply_inline(ir)
    {:ok, result} = Compiler.compile(ir, config)

    # The TLA+ filename must match the MODULE name inside the file.
    module_name = result.state_space.module_name
    tla_file = "#{module_name}.tla"
    cfg_file = "#{module_name}.cfg"

    File.write!(Path.join(tmp_dir, tla_file), result.tla)
    File.write!(Path.join(tmp_dir, cfg_file), result.cfg)

    check_deadlock = Keyword.get(opts, :check_deadlock, true)

    Engine.check(Path.join(tmp_dir, tla_file), Path.join(tmp_dir, cfg_file),
      deadlock: check_deadlock,
      engine: Keyword.get(opts, :engine)
    )
  end

  defp resolve_config(_protocol_mod, opts) do
    cond do
      config = Keyword.get(opts, :model_config) ->
        config

      path = Keyword.get(opts, :model_config_path) ->
        ModelConfig.load(protocol_config_path: path)

      true ->
        ModelConfig.load()
    end
  end

  defp format_trace_summary([]), do: ""

  defp format_trace_summary(trace) do
    steps =
      Enum.map_join(trace, " → ", fn entry ->
        entry.action || "Init"
      end)

    "\n  trace: #{steps}"
  end
end
