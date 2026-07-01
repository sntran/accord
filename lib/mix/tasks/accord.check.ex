defmodule Mix.Tasks.Accord.Check do
  @moduledoc """
  Runs TLC model checking against generated TLA+ specs.

  Discovers protocol modules (those defining `__tla_span__/1`), locates
  their generated `.tla` and `.cfg` files in `_build/accord/`, shells out
  to TLC, parses results, and maps counterexamples back to Elixir source
  using `__tla_span__/1`.

  ## Usage

      mix accord.check                          # check all protocols
      mix accord.check Lock.Protocol            # check a specific protocol
      mix accord.check --workers 4              # TLC parallelism
      mix accord.check --strict                 # fail protocols with tla: :off
      mix accord.check --no-deadlock            # disable deadlock checking
      mix accord.check --dump                   # write raw TLC output on failure
      mix accord.check --force                  # ignore the pass cache

  Passing results are cached by content hash (spec, cfg, TLC jar,
  deadlock setting) in `_build/accord/.check_cache`; unchanged protocols
  skip TLC entirely. Failures are never cached.

  Protocols whose spec generation failed at compile time (`tla: :warn`)
  always count as failures: a protocol that cannot be checked is not
  verified. Protocols compiled with `tla: :off` are skipped unless
  `--strict` is given.

  Deadlock checking is on by default: generated specs give terminal
  states an explicit `Terminating` self-stutter, so a reported deadlock
  is a real stuck state (a non-terminal state with no enabled action —
  often guard or `where:` exhaustion at a domain boundary).

  ## Requirements

  TLC must be available. The task looks for `tla2tools.jar` at:

  1. `TLA2TOOLS_JAR` environment variable
  2. `~/.tla/tla2tools.jar`
  3. `tla2tools.jar` in the current directory

  Install TLC from https://github.com/tlaplus/tlaplus/releases
  """

  use Mix.Task

  alias Accord.TLA.{CheckCache, Files, TLCParser, ViolationReport}

  @shortdoc "Run TLC model checking on Accord protocols"

  @impl Mix.Task
  def run(args) do
    Mix.Task.run("compile", [])

    {opts, modules, _} =
      OptionParser.parse(args,
        strict: [
          workers: :integer,
          strict: :boolean,
          deadlock: :boolean,
          dump: :boolean,
          force: :boolean
        ]
      )

    workers = Keyword.get(opts, :workers)
    strict? = Keyword.get(opts, :strict, false)
    deadlock? = Keyword.get(opts, :deadlock, true)
    dump? = Keyword.get(opts, :dump, false)
    force? = Keyword.get(opts, :force, false)

    protocols =
      if modules == [] do
        discover_protocols()
      else
        Enum.map(modules, fn name ->
          # Safe: developer-provided CLI argument, not untrusted input.
          mod = Module.concat([String.to_atom(name)])

          unless Code.ensure_loaded?(mod) do
            Mix.raise("Unknown module: #{inspect(mod)}. Is the module compiled?")
          end

          mod
        end)
      end

    if protocols == [] do
      Mix.shell().info("No Accord protocols found.")
      :ok
    else
      Mix.shell().info("Checking #{length(protocols)} protocol(s)...\n")

      cache = if force?, do: %{}, else: CheckCache.load()

      {results, cache} =
        Enum.map_reduce(protocols, cache, fn mod, cache ->
          {result, cache} = check_protocol(mod, workers, strict?, deadlock?, dump?, cache)
          {{mod, result}, cache}
        end)

      CheckCache.save(cache)
      report_results(results)
    end
  end

  # -- Protocol Discovery --

  defp discover_protocols do
    Mix.Project.compile_path()
    |> Path.join("*.beam")
    |> Path.wildcard()
    |> Enum.flat_map(fn beam_path ->
      module =
        beam_path
        |> Path.basename(".beam")
        # Safe: beam file names correspond to already-loaded atoms.
        |> String.to_atom()

      if Code.ensure_loaded?(module) and function_exported?(module, :__tla_span__, 1) do
        [module]
      else
        []
      end
    end)
  rescue
    _ -> []
  end

  # -- Protocol Checking --

  defp check_protocol(mod, workers, strict?, deadlock?, dump?, cache) do
    with :ok <- ensure_loaded(mod),
         :ok <- ensure_protocol(mod),
         :ok <- ensure_tla_generated(mod, strict?),
         {tla_path, cfg_path} <- Files.paths(mod),
         :ok <- ensure_file(tla_path, :tla_not_found),
         :ok <- ensure_file(cfg_path, :cfg_not_found),
         {:ok, tlc_jar} <- require_tlc() do
      module_name = Files.tla_module_name(mod)
      key = CheckCache.key(tla_path, cfg_path, tlc_jar, deadlock?)

      if CheckCache.hit?(cache, module_name, key) do
        {{:cached, key}, cache}
      else
        case run_tlc(mod, tla_path, cfg_path, tlc_jar, workers, deadlock?, dump?) do
          {:ok, _stats} = ok -> {ok, CheckCache.put(cache, module_name, key)}
          other -> {other, cache}
        end
      end
    else
      error -> {error, cache}
    end
  end

  defp ensure_loaded(mod) do
    if Code.ensure_loaded?(mod), do: :ok, else: {:error, :module_not_found}
  end

  defp ensure_protocol(mod) do
    if function_exported?(mod, :__tla_span__, 1), do: :ok, else: {:error, :not_a_protocol}
  end

  # A protocol whose spec generation failed cannot be checked, and "cannot
  # check" must never read as "verified". Protocols with tla: :off are
  # deliberate opt-outs: skipped by default, failures under --strict.
  defp ensure_tla_generated(mod, strict?) do
    case tla_status(mod) do
      {:error, summary} -> {:error, {:tla_failed, summary}}
      :off when strict? -> {:error, :tla_off}
      :off -> {:skip, :tla_off}
      _ -> :ok
    end
  end

  defp tla_status(mod) do
    if function_exported?(mod, :__tla_status__, 0), do: mod.__tla_status__(), else: :ok
  end

  defp ensure_file(path, error_tag) do
    if File.exists?(path), do: :ok, else: {:error, error_tag}
  end

  defp require_tlc do
    case find_tlc() do
      nil -> {:error, :tlc_not_found}
      jar -> {:ok, jar}
    end
  end

  defp find_tlc do
    cond do
      env = System.get_env("TLA2TOOLS_JAR") ->
        if File.exists?(env), do: env

      File.exists?(Path.expand("~/.tla/tla2tools.jar")) ->
        Path.expand("~/.tla/tla2tools.jar")

      File.exists?("tla2tools.jar") ->
        Path.expand("tla2tools.jar")

      true ->
        nil
    end
  end

  defp run_tlc(_mod, tla_path, cfg_path, tlc_jar, workers, deadlock?, dump?) do
    tla_dir = Path.dirname(tla_path)
    tla_file = Path.basename(tla_path)

    base_args = [
      "-jar",
      tlc_jar,
      "-config",
      Path.basename(cfg_path)
    ]

    # TLC's -deadlock flag DISABLES deadlock checking. Generated specs
    # give terminal states a Terminating self-stutter, so deadlock
    # checking stays on by default; --no-deadlock is the escape hatch.
    disable_deadlock = if deadlock?, do: [], else: ["-deadlock"]

    # -cleanup removes TLC's states/ metadata directories, which would
    # otherwise accumulate in _build/accord/ across runs.
    args = base_args ++ disable_deadlock ++ ["-cleanup", tla_file]
    args = if workers, do: args ++ ["-workers", Integer.to_string(workers)], else: args

    started = System.monotonic_time(:millisecond)
    # TLC returns non-zero on violations; both paths parse the output.
    {output, _exit_code} = System.cmd("java", args, cd: tla_dir, stderr_to_stdout: true)
    duration_ms = System.monotonic_time(:millisecond) - started

    case TLCParser.parse(output) do
      {:ok, stats} ->
        {:ok, Map.put(stats, :duration_ms, duration_ms)}

      {:error, violation, stats} ->
        if dump?, do: dump_tlc_output(tla_path, output)
        {:error, violation, Map.put(stats, :duration_ms, duration_ms)}
    end
  rescue
    e in ErlangError ->
      {:error, :java_not_found, inspect(e)}
  end

  # Raw TLC output next to the spec, for digging past the parsed report.
  defp dump_tlc_output(tla_path, output) do
    log_path = Path.rootname(tla_path) <> ".tlc.log"
    File.write!(log_path, output)
    Mix.shell().info("#{IO.ANSI.faint()}  raw TLC output: #{log_path}#{IO.ANSI.reset()}")
    :ok
  end

  # -- Result Reporting --

  defp report_results(results) do
    groups =
      Enum.group_by(results, fn
        {_mod, {:ok, _}} -> :success
        {_mod, {:cached, _}} -> :success
        {_mod, {:skip, _}} -> :skip
        _ -> :failure
      end)

    successes = Map.get(groups, :success, [])
    skips = Map.get(groups, :skip, [])
    failures = Map.get(groups, :failure, [])

    # Report successes.
    for {mod, {:ok, stats}} <- successes do
      Mix.shell().info(
        "#{IO.ANSI.green()}✓#{IO.ANSI.reset()} #{inspect(mod)} — " <>
          "#{stats.distinct_states} distinct states (#{stats.states_generated} generated" <>
          if(stats.depth, do: ", depth #{stats.depth}", else: "") <>
          ")" <> format_duration(stats)
      )

      report_runtime_only_checks(mod)
    end

    for {mod, {:cached, _key}} <- successes do
      Mix.shell().info(
        "#{IO.ANSI.green()}✓#{IO.ANSI.reset()} #{inspect(mod)} — " <>
          "cached (unchanged since last pass; --force to re-run)"
      )

      report_runtime_only_checks(mod)
    end

    # Report skips (deliberate tla: :off opt-outs).
    for {mod, {:skip, :tla_off}} <- skips do
      Mix.shell().info(
        "#{IO.ANSI.faint()}–#{IO.ANSI.reset()} #{inspect(mod)} — skipped (tla: :off)"
      )
    end

    # Report failures.
    for {mod, result} <- failures do
      report_failure(mod, result)
    end

    if failures != [] do
      Mix.shell().info(
        "\n#{IO.ANSI.red()}#{length(failures)} protocol(s) failed.#{IO.ANSI.reset()}"
      )

      # Exit with failure status for CI.
      System.at_exit(fn _ -> :ok end)
      exit({:shutdown, 1})
    else
      Mix.shell().info(
        "\n#{IO.ANSI.green()}All #{length(successes)} protocol(s) passed.#{IO.ANSI.reset()}"
      )
    end
  end

  defp report_failure(mod, {:error, %{kind: _, trace: _} = violation, stats}) do
    label = violation_label(violation)

    Mix.shell().info(
      "#{IO.ANSI.red()}✗#{IO.ANSI.reset()} #{inspect(mod)} — #{label} " <>
        "(#{stats.distinct_states} states explored)"
    )

    formatted = ViolationReport.format(violation, mod)
    Mix.shell().info("\n" <> formatted)
  end

  defp report_failure(mod, {:error, reason}) do
    message =
      case reason do
        :module_not_found -> "module not found"
        :not_a_protocol -> "not an Accord protocol"
        {:tla_failed, summary} -> "TLA+ spec generation failed at compile time: #{summary}"
        :tla_off -> "TLA+ generation disabled (tla: :off) — failing under --strict"
        :tla_not_found -> ".tla file not found (run `mix compile` first)"
        :cfg_not_found -> ".cfg file not found (run `mix compile` first)"
        :tlc_not_found -> "TLC not found (set TLA2TOOLS_JAR or install to ~/.tla/)"
        :java_not_found -> "Java not found (TLC requires a JVM)"
        other -> inspect(other)
      end

    Mix.shell().info("#{IO.ANSI.red()}✗#{IO.ANSI.reset()} #{inspect(mod)} — #{message}")
  end

  defp report_failure(mod, {:error, reason, detail}) do
    Mix.shell().info("#{IO.ANSI.red()}✗#{IO.ANSI.reset()} #{inspect(mod)} — #{reason}: #{detail}")
  end

  defp format_duration(%{duration_ms: ms}) when is_integer(ms), do: " in #{ms}ms"
  defp format_duration(_stats), do: ""

  # A green check must never silently imply that runtime-only checks
  # (ordered, precedence, keyed correspondence) were model checked.
  defp report_runtime_only_checks(mod) do
    case runtime_only_checks(mod) do
      [] ->
        :ok

      descriptions ->
        Mix.shell().info(
          "  #{IO.ANSI.faint()}↳ enforced at runtime only: " <>
            "#{Enum.join(descriptions, ", ")}#{IO.ANSI.reset()}"
        )
    end
  end

  defp runtime_only_checks(mod) do
    if function_exported?(mod, :__ir__, 0) do
      for prop <- mod.__ir__().properties,
          check <- prop.checks,
          runtime_only_check?(check) do
        "#{check.kind}(#{prop.name})"
      end
    else
      []
    end
  end

  defp runtime_only_check?(%{kind: kind}) when kind in [:ordered, :precedence], do: true

  defp runtime_only_check?(%{kind: :correspondence, spec: spec}),
    do: Map.get(spec, :by) != nil

  defp runtime_only_check?(_), do: false

  defp violation_label(%{kind: :invariant, property: property}) do
    "invariant #{property || "unknown"} violated"
  end

  defp violation_label(%{kind: :action_property, property: property}) do
    "action property #{property || "unknown"} violated"
  end

  defp violation_label(%{kind: :deadlock}), do: "deadlock reached"
  defp violation_label(%{kind: :temporal}), do: "temporal property violated"
  defp violation_label(%{kind: :error}), do: "TLC error"
end
