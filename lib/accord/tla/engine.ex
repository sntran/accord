defmodule Accord.TLA.Engine do
  @moduledoc """
  Runs a model check of a `.tla` module with a `.cfg` model.

  Two engines give the same result shape (the shape of
  `Accord.TLA.TLCParser.parse/1`):

  - `:native` (the default) — `Accord.TLA.Checker`, in Elixir. It needs
    no Java.
  - `:tlc` — TLC from `tla2tools.jar`, for a comparison with the
    reference checker. It needs Java.

  The engine comes from the option `:engine`, else from the environment
  variable `ACCORD_TLA_ENGINE` (`native` or `tlc`), else `:native`.
  """

  alias Accord.TLA.{Checker, TLCParser}

  @type engine :: :native | :tlc

  @doc """
  Checks the module in `tla_path` with the config in `cfg_path`.

  Options:

  - `:engine` — `:native` or `:tlc`.
  - `:deadlock` — `false` stops the deadlock check (default `true`).
  - `:workers` — TLC workers (TLC only).
  - `:jar` — the path of `tla2tools.jar` (TLC only; default: `find_jar/0`).
  - `:paths` — more directories for modules (native only).

  Gives `{:ok, stats}` or `{:error, violation, stats}`; the stats have
  `:duration_ms`, `:engine`, and `:output` (the text report: the raw
  output of TLC, or the report of the native checker in the style of
  TLC). With TLC, `{:error, :tlc_not_found}` when there is no jar.
  """
  @spec check(Path.t(), Path.t(), keyword()) :: TLCParser.result() | {:error, :tlc_not_found}
  def check(tla_path, cfg_path, opts \\ []) do
    case engine(opts) do
      :native -> native(tla_path, cfg_path, opts)
      :tlc -> tlc(tla_path, cfg_path, opts)
    end
  end

  @doc "The engine that `check/3` uses for these options."
  @spec engine(keyword()) :: engine()
  def engine(opts \\ []) do
    case Keyword.get(opts, :engine) || System.get_env("ACCORD_TLA_ENGINE") do
      e when e in [:tlc, "tlc"] -> :tlc
      _ -> :native
    end
  end

  @doc """
  A short text that names the engine and its version, for cache keys.
  """
  @spec identity(keyword()) :: String.t()
  def identity(opts \\ []) do
    case engine(opts) do
      :native ->
        "native:" <>
          to_string(Application.spec(:accord, :vsn) || "dev") <> ":" <> native_fingerprint()

      :tlc ->
        case Keyword.get(opts, :jar) || find_jar() do
          nil ->
            "tlc:none"

          jar ->
            stat = File.stat!(jar, time: :posix)
            "tlc:#{jar}:#{stat.size}:#{stat.mtime}"
        end
    end
  end

  # The checker code itself: a new build of the checker must not reuse
  # the cached passes of an old one.
  @checker_modules [
    Checker,
    Checker.Lexer,
    Checker.Parser,
    Checker.Config,
    Checker.Context,
    Checker.Value,
    Checker.Eval,
    Checker.Stdlib,
    Checker.Community,
    Checker.Spec,
    Checker.Temporal,
    Checker.Search,
    Checker.Liveness,
    Checker.Constant,
    Checker.ValueStream
  ]

  defp native_fingerprint do
    :sha256
    |> :crypto.hash(Enum.map(@checker_modules, & &1.module_info(:md5)))
    |> Base.encode16()
    |> binary_part(0, 12)
  end

  @doc """
  Finds `tla2tools.jar`: the environment variable `TLA2TOOLS_JAR`, then
  `~/.tla/tla2tools.jar`, then `tla2tools.jar` in the current directory.
  """
  @spec find_jar() :: Path.t() | nil
  def find_jar do
    cond do
      jar = System.get_env("TLA2TOOLS_JAR") -> if File.exists?(jar), do: jar
      File.exists?(Path.expand("~/.tla/tla2tools.jar")) -> Path.expand("~/.tla/tla2tools.jar")
      File.exists?("tla2tools.jar") -> Path.expand("tla2tools.jar")
      true -> nil
    end
  end

  @doc "Tells if TLC can run here (Java and `tla2tools.jar`)."
  @spec tlc_available?() :: boolean()
  def tlc_available? do
    find_jar() != nil and java_available?()
  end

  defp java_available? do
    case System.cmd("java", ["-version"], stderr_to_stdout: true) do
      {_, 0} -> true
      _ -> false
    end
  rescue
    ErlangError -> false
  end

  # -- Native --

  defp native(tla_path, cfg_path, opts) do
    started = System.monotonic_time(:millisecond)

    full =
      Checker.run(tla_path,
        config: cfg_path,
        deadlock: Keyword.get(opts, :deadlock, true),
        paths: Keyword.get(opts, :paths, [])
      )

    duration = System.monotonic_time(:millisecond) - started
    output = Checker.format(full)

    case Checker.to_tlc(full) do
      {:ok, stats} ->
        {:ok, stats |> decorate(duration, :native) |> Map.put(:output, output)}

      {:error, violation, stats} ->
        {:error, violation, stats |> decorate(duration, :native) |> Map.put(:output, output)}
    end
  end

  # -- TLC --

  defp tlc(tla_path, cfg_path, opts) do
    case Keyword.get(opts, :jar) || find_jar() do
      nil -> {:error, :tlc_not_found}
      jar -> run_tlc(jar, tla_path, cfg_path, opts)
    end
  end

  defp run_tlc(jar, tla_path, cfg_path, opts) do
    dir = Path.dirname(tla_path)
    # Each run has its own temporary directory: two TLC processes that
    # share java.io.tmpdir can read the files of the other one.
    tmp = Path.join(System.tmp_dir!(), "accord-tlc-#{System.unique_integer([:positive])}")
    File.mkdir_p!(tmp)

    args =
      [
        "-XX:+UseParallelGC",
        "-Djava.io.tmpdir=#{tmp}",
        "-jar",
        jar,
        "-config",
        Path.expand(cfg_path)
      ] ++
        if(Keyword.get(opts, :deadlock, true), do: [], else: ["-deadlock"]) ++
        ["-cleanup", "-metadir", Path.join(tmp, "states")] ++
        if(w = Keyword.get(opts, :workers), do: ["-workers", Integer.to_string(w)], else: []) ++
        [Path.basename(tla_path)]

    started = System.monotonic_time(:millisecond)
    {output, _exit} = System.cmd("java", args, cd: dir, stderr_to_stdout: true)
    duration = System.monotonic_time(:millisecond) - started
    File.rm_rf(tmp)

    case TLCParser.parse(output) do
      {:ok, stats} ->
        {:ok, stats |> decorate(duration, :tlc) |> Map.put(:output, output)}

      {:error, violation, stats} ->
        {:error, violation, stats |> decorate(duration, :tlc) |> Map.put(:output, output)}
    end
  rescue
    e in ErlangError ->
      {:error,
       %{kind: :error, property: nil, message: "cannot run java: #{inspect(e)}", trace: []},
       %{states_generated: 0, distinct_states: 0, depth: nil, warnings: [], engine: :tlc}}
  end

  defp decorate(stats, duration, engine),
    do: stats |> Map.put(:duration_ms, duration) |> Map.put(:engine, engine)
end
