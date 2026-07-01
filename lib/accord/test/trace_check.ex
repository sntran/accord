defmodule Accord.Test.TraceCheck do
  @moduledoc """
  Asserts that a captured runtime trace replays against the generated
  TLA+ spec.

  This is the conformance oracle for accord's own TLA+ compiler: a
  guard the compiler mistranslated, an update it dropped, or a
  constraint it rendered wrongly will refuse to accept a trace the real
  monitor produced. Capture with the monitor's `trace_sink:` option
  (see `Accord.Trace.collector/0`), then:

      TraceCheck.assert_replays(MyProtocol, events, tmp_dir: tmp_dir)

  Requires `tla2tools.jar` (same lookup as `Accord.Test.TLACheck`);
  gate tests with `@tag :tlc`.
  """

  alias Accord.TLA.{TLCParser, TraceSpec}
  alias Accord.Trace.Event

  @doc """
  Asserts TLC replays the whole trace as a behavior of the spec.
  """
  @spec assert_replays(module(), [Event.t()], keyword()) :: :ok
  def assert_replays(protocol_mod, events, opts) do
    case run(protocol_mod, events, opts) do
      {:ok, _stats} ->
        :ok

      {:error, %{kind: :deadlock} = violation, _stats} ->
        raise ExUnit.AssertionError,
          message:
            "the spec rejected the runtime trace at step #{divergence_step(violation)} " <>
              "of #{length(events)} — no protocol action reproduces the recorded " <>
              "transition (translation bug or hand-built trace divergence)"

      {:error, violation, _stats} ->
        raise ExUnit.AssertionError,
          message: "trace replay failed with #{violation.kind}"
    end
  end

  @doc """
  Asserts the trace diverges from the spec, returning the failing step.
  """
  @spec assert_diverges(module(), [Event.t()], keyword()) :: {:diverged_at, pos_integer()}
  def assert_diverges(protocol_mod, events, opts) do
    case run(protocol_mod, events, opts) do
      {:error, %{kind: :deadlock} = violation, _stats} ->
        {:diverged_at, divergence_step(violation)}

      {:ok, _stats} ->
        raise ExUnit.AssertionError,
          message: "expected the trace to diverge from the spec, but it replayed fully"

      {:error, violation, _stats} ->
        raise ExUnit.AssertionError,
          message: "expected a divergence deadlock, got #{violation.kind}"
    end
  end

  # -- Internals --

  defp run(protocol_mod, events, opts) do
    tmp_dir = Keyword.fetch!(opts, :tmp_dir)

    {:ok, spec} = TraceSpec.generate(protocol_mod, events)
    base_name = spec.module_name |> String.replace_suffix("Trace", "")

    File.write!(Path.join(tmp_dir, "#{base_name}.tla"), spec.base_tla)
    File.write!(Path.join(tmp_dir, "#{base_name}.cfg"), spec.base_cfg)
    File.write!(Path.join(tmp_dir, "#{spec.module_name}.tla"), spec.trace_tla)
    File.write!(Path.join(tmp_dir, "#{spec.module_name}.cfg"), spec.trace_cfg)

    tlc_jar = find_tlc_jar() || raise "tla2tools.jar not found"

    args = [
      "-jar",
      tlc_jar,
      "-config",
      "#{spec.module_name}.cfg",
      "-cleanup",
      "#{spec.module_name}.tla"
    ]

    {output, _exit} = System.cmd("java", args, cd: tmp_dir, stderr_to_stdout: true)
    TLCParser.parse(output)
  end

  # The deadlock trace's last state carries the failing index in ti.
  defp divergence_step(%{trace: trace}) do
    trace
    |> List.last()
    |> case do
      %{assignments: %{"ti" => ti}} -> String.to_integer(ti)
      _ -> :unknown
    end
  end

  defp find_tlc_jar do
    cond do
      jar = System.get_env("TLA2TOOLS_JAR") -> if File.exists?(jar), do: jar
      File.exists?(Path.expand("~/.tla/tla2tools.jar")) -> Path.expand("~/.tla/tla2tools.jar")
      File.exists?("tla2tools.jar") -> Path.expand("tla2tools.jar")
      true -> nil
    end
  end
end
