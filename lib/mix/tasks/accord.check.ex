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
      mix accord.check --extra test/tla/LockProtocolChecks.tla

  Passing results are cached by content hash (spec, cfg, TLC jar,
  deadlock setting) in `_build/accord/.check_cache`; unchanged protocols
  skip TLC entirely. Failures are never cached.

  ## Unsound-verdict warnings

  TLC can report "no error found" while also warning that the verdict may
  be unsound — a state constraint or a symmetry set declared alongside a
  liveness property lets it miss violations (TLC's own §14.3.5 caveat).
  Such a run is reported with `⚠` and its warnings, and is **not** cached
  (it re-runs so the warning re-surfaces). Under `--strict` it counts as a
  failure, so CI can gate on it. A correspondence property emits a counter
  bound as a `CONSTRAINT`, so a protocol with both correspondence and
  liveness triggers this — its liveness is checked only over behaviors
  within the bound.

  ## Hand-written extension specs

  `--extra` checks a user-authored TLA+ module that `EXTENDS` a
  generated protocol module — custom invariants, refinement mappings,
  anything the DSL cannot express — without ever editing generated
  files, so regeneration is always safe:

      ---- MODULE LockProtocolChecks ----
      EXTENDS LockProtocol
      HolderNeedsToken == (holder /= NULL) => (fence_token > 0)
      ====

  A sibling `.cfg` provides SPECIFICATION/INVARIANT/PROPERTY lines
  (defaults to `SPECIFICATION Spec` if absent); the generated module's
  CONSTANT, SYMMETRY, and CONSTRAINT lines are appended automatically,
  so model values never need duplicating. The file name must match the
  MODULE name. Repeat the flag for multiple modules.

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
          force: :boolean,
          extra: :keep
        ]
      )

    workers = Keyword.get(opts, :workers)
    strict? = Keyword.get(opts, :strict, false)
    deadlock? = Keyword.get(opts, :deadlock, true)
    dump? = Keyword.get(opts, :dump, false)
    force? = Keyword.get(opts, :force, false)
    extras = Keyword.get_values(opts, :extra)

    # Collisions are detected across every protocol in the app, not just
    # the requested subset: a single requested module can share its flat
    # artifact with a sibling that compiled later, so the on-disk spec
    # might belong to the other module. Guard before trusting any check.
    assert_no_name_collisions(discover_protocols())

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

    if protocols == [] and extras == [] do
      Mix.shell().info("No Accord protocols found.")
      :ok
    else
      Mix.shell().info("Checking #{length(protocols) + length(extras)} module(s)...\n")

      cache = if force?, do: %{}, else: CheckCache.load()

      {results, cache} =
        Enum.map_reduce(protocols, cache, fn mod, cache ->
          {result, cache} = check_protocol(mod, workers, strict?, deadlock?, dump?, cache)
          {{mod, result}, cache}
        end)

      extra_results =
        Enum.map(extras, fn path ->
          check_extra(path, protocols, workers, strict?, deadlock?, dump?)
        end)

      CheckCache.save(cache)
      report_results(results ++ extra_results)
    end
  end

  # -- Hand-Written Extension Specs --

  # An extra module runs against the SAME generated artifacts: it is
  # copied into _build/accord/ so EXTENDS resolves, its cfg (or a
  # default) is merged with the generated module's CONSTANT/SYMMETRY/
  # CONSTRAINT lines, and violations are mapped through the extended
  # protocol's spans where possible. Extras are never cached.
  defp check_extra(path, protocols, workers, strict?, deadlock?, dump?) do
    with {:ok, content} <- File.read(path),
         module_name = Path.basename(path, ".tla"),
         {:ok, protocol_mod} <- resolve_extended_protocol(content, protocols) do
      {proto_tla, proto_cfg} = Files.paths(protocol_mod)

      if File.exists?(proto_tla) do
        dest_tla = Path.join(Path.dirname(proto_tla), "#{module_name}.tla")
        dest_cfg = Path.join(Path.dirname(proto_tla), "#{module_name}.cfg")
        File.write!(dest_tla, content)
        File.write!(dest_cfg, merged_extra_cfg(path, proto_cfg))

        result =
          case require_tlc() do
            {:ok, tlc_jar} ->
              # The merged cfg inherits SYMMETRY/CONSTRAINT from the
              # generated module; if the user's module adds liveness, TLC
              # warns the verdict is unsound — surface it like any other run.
              classify_tlc_run(
                run_tlc(protocol_mod, dest_tla, dest_cfg, tlc_jar, workers, deadlock?, dump?),
                strict?
              )

            error ->
              error
          end

        {{:extra, module_name, protocol_mod}, result}
      else
        {{:extra, module_name, protocol_mod}, {:error, :tla_not_found}}
      end
    else
      {:error, :no_known_extends} ->
        {{:extra, Path.basename(path, ".tla"), nil}, {:error, :no_known_extends}}

      {:error, reason} ->
        {{:extra, Path.basename(path, ".tla"), nil}, {:error, {:extra_unreadable, reason}}}
    end
  end

  # The first EXTENDS entry matching a generated protocol module name
  # identifies which protocol this module refines.
  defp resolve_extended_protocol(content, protocols) do
    by_name = Map.new(protocols, fn mod -> {Files.tla_module_name(mod), mod} end)

    extended =
      ~r/^EXTENDS\s+(.+)$/m
      |> Regex.scan(content, capture: :all_but_first)
      |> List.flatten()
      |> Enum.flat_map(&String.split(&1, ","))
      |> Enum.map(&String.trim/1)
      |> Enum.find(&Map.has_key?(by_name, &1))

    case extended do
      nil -> {:error, :no_known_extends}
      name -> {:ok, Map.fetch!(by_name, name)}
    end
  end

  # User cfg (or a bare SPECIFICATION) plus the generated module's
  # CONSTANT/SYMMETRY/CONSTRAINT lines — model values never need
  # duplicating by hand.
  defp merged_extra_cfg(extra_tla_path, proto_cfg_path) do
    user_cfg_path = Path.rootname(extra_tla_path) <> ".cfg"

    user_cfg =
      case File.read(user_cfg_path) do
        {:ok, content} -> content
        {:error, _} -> "SPECIFICATION Spec\n"
      end

    inherited =
      proto_cfg_path
      |> File.read!()
      |> String.split("\n")
      |> Enum.filter(fn line ->
        String.starts_with?(line, "CONSTANT") or
          String.starts_with?(line, "SYMMETRY") or
          String.starts_with?(line, "CONSTRAINT")
      end)
      |> Enum.reject(&String.contains?(user_cfg, &1))

    user_cfg <> "\n" <> Enum.join(inherited, "\n") <> "\n"
  end

  # -- Protocol Discovery --

  # A name collision means two protocols share one flat .tla/.cfg, so a
  # ✓ could describe a spec generated from a different module. That must
  # never pass silently — abort with the offending modules named.
  defp assert_no_name_collisions(protocols) do
    case Files.name_collisions(protocols) do
      [] ->
        :ok

      collisions ->
        detail =
          Enum.map_join(collisions, "\n", fn {name, mods} ->
            "  #{name}: #{Enum.map_join(mods, ", ", &inspect/1)}"
          end)

        Mix.raise(
          "Protocol modules map to the same TLA+ artifact name (they would " <>
            "overwrite each other in _build/accord/, and a check could verify " <>
            "the wrong spec). Rename one of each colliding pair:\n" <> detail
        )
    end
  end

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
        case classify_tlc_run(
               run_tlc(mod, tla_path, cfg_path, tlc_jar, workers, deadlock?, dump?),
               strict?
             ) do
          # Only a clean pass — no TLC warnings — is cached. A warned or
          # failed verdict must re-run every time so the warning re-surfaces.
          {:ok, _stats} = ok -> {ok, CheckCache.put(cache, module_name, key)}
          other -> {other, cache}
        end
      end
    else
      error -> {error, cache}
    end
  end

  # TLC can report "No error found" while also printing a warning that the
  # verdict may be unsound (symmetry or a state constraint under liveness
  # checking). Swallowing that warning is exactly how a false ✓ ships, so a
  # passing run that carries warnings is downgraded: a hard failure under
  # --strict, a surfaced-but-non-fatal `:warned` otherwise. Real failures
  # and infrastructure errors pass through untouched.
  defp classify_tlc_run({:ok, %{warnings: [_ | _] = warnings}}, true) do
    {:error, {:tlc_warnings, warnings}}
  end

  defp classify_tlc_run({:ok, %{warnings: [_ | _]} = stats}, false) do
    {:warned, stats}
  end

  defp classify_tlc_run(result, _strict?), do: result

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
        {_mod, {:warned, _}} -> :warned
        _ -> :failure
      end)

    successes = Map.get(groups, :success, [])
    skips = Map.get(groups, :skip, [])
    warned = Map.get(groups, :warned, [])
    failures = Map.get(groups, :failure, [])

    # Report successes.
    for {mod, {:ok, stats}} <- successes do
      Mix.shell().info(
        "#{IO.ANSI.green()}✓#{IO.ANSI.reset()} #{display_name(mod)} — " <>
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

    # Report passes that TLC flagged as possibly unsound (exit 0, but loud;
    # --strict turns these into failures instead).
    for {mod, {:warned, stats}} <- warned do
      report_warned(mod, stats)
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
      warned_note =
        if warned != [], do: " (#{length(warned)} with warnings — see above)", else: ""

      Mix.shell().info(
        "\n#{IO.ANSI.green()}All #{length(successes)} protocol(s) passed.#{IO.ANSI.reset()}" <>
          warned_note
      )
    end
  end

  defp report_warned(mod, stats) do
    Mix.shell().info(
      "#{IO.ANSI.yellow()}⚠#{IO.ANSI.reset()} #{display_name(mod)} — passed, but TLC warns the " <>
        "verdict may be unsound (#{stats.distinct_states} states explored)"
    )

    for warning <- stats.warnings do
      Mix.shell().info("#{IO.ANSI.yellow()}    #{warning}#{IO.ANSI.reset()}")
    end

    Mix.shell().info(
      "#{IO.ANSI.faint()}    re-run with --strict to treat this as a failure#{IO.ANSI.reset()}"
    )
  end

  defp report_failure(mod, {:error, %{kind: _, trace: _} = violation, stats}) do
    label = violation_label(violation)

    Mix.shell().info(
      "#{IO.ANSI.red()}✗#{IO.ANSI.reset()} #{display_name(mod)} — #{label} " <>
        "(#{stats.distinct_states} states explored)"
    )

    # Extra modules map violations through the protocol they extend —
    # user-defined invariant names simply have no spans.
    span_mod =
      case mod do
        {:extra, _name, protocol_mod} -> protocol_mod
        mod -> mod
      end

    formatted = ViolationReport.format(violation, span_mod)
    Mix.shell().info("\n" <> formatted)
  end

  defp report_failure(mod, {:error, reason}) do
    message =
      case reason do
        :module_not_found ->
          "module not found"

        :not_a_protocol ->
          "not an Accord protocol"

        {:tla_failed, summary} ->
          "TLA+ spec generation failed at compile time: #{summary}"

        :tla_off ->
          "TLA+ generation disabled (tla: :off) — failing under --strict"

        {:tlc_warnings, warnings} ->
          "TLC reported the verdict may be unsound — failing under --strict:\n" <>
            Enum.map_join(warnings, "\n", &"      #{&1}")

        :tla_not_found ->
          ".tla file not found (run `mix compile` first)"

        :cfg_not_found ->
          ".cfg file not found (run `mix compile` first)"

        :tlc_not_found ->
          "TLC not found (set TLA2TOOLS_JAR or install to ~/.tla/)"

        :java_not_found ->
          "Java not found (TLC requires a JVM)"

        :no_known_extends ->
          "EXTENDS no known generated protocol module"

        {:extra_unreadable, why} ->
          "cannot read extra module: #{inspect(why)}"

        other ->
          inspect(other)
      end

    Mix.shell().info("#{IO.ANSI.red()}✗#{IO.ANSI.reset()} #{display_name(mod)} — #{message}")
  end

  defp report_failure(mod, {:error, reason, detail}) do
    Mix.shell().info(
      "#{IO.ANSI.red()}✗#{IO.ANSI.reset()} #{display_name(mod)} — #{reason}: #{detail}"
    )
  end

  defp format_duration(%{duration_ms: ms}) when is_integer(ms), do: " in #{ms}ms"
  defp format_duration(_stats), do: ""

  defp display_name({:extra, name, protocol_mod}) when protocol_mod != nil,
    do: "#{name} (extends #{inspect(protocol_mod)})"

  defp display_name({:extra, name, _}), do: name
  defp display_name(mod), do: inspect(mod)

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

  defp runtime_only_checks({:extra, _name, _mod}), do: []

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
