defmodule Accord.CrossCheck.TLC do
  @moduledoc """
  Runs TLC for the cross-check, and reads its output.

  Each run uses one worker (`-workers 1`), so that the search is a true
  breadth-first search and a counterexample has the minimum length.
  """

  alias Accord.CrossCheck.TLAValue
  alias Accord.TLA.TLCParser

  @type run :: %{
          status: :ok | :violated | :error | :timeout,
          kind: atom() | nil,
          property: String.t() | nil,
          message: String.t() | nil,
          trace: [%{action: String.t() | nil, vars: map()}],
          distinct: non_neg_integer() | nil,
          depth: non_neg_integer() | nil,
          states: [map()] | nil,
          edges: [{map(), map()}] | nil,
          constant: boolean(),
          loop: nil | :stutter | {:back_to, pos_integer()},
          output: String.t()
        }

  @doc """
  Finds `tla2tools.jar`, in the same places as `mix accord.check`.
  """
  @spec find_jar() :: String.t() | nil
  def find_jar do
    cond do
      env = System.get_env("TLA2TOOLS_JAR") -> if File.exists?(env), do: env
      File.exists?(Path.expand("~/.tla/tla2tools.jar")) -> Path.expand("~/.tla/tla2tools.jar")
      File.exists?("tla2tools.jar") -> Path.expand("tla2tools.jar")
      true -> nil
    end
  end

  @doc """
  Runs TLC on `spec_file` (in `dir`) with the config text `cfg`.

  ## Options

  - `:jar` — the path of `tla2tools.jar` (required).
  - `:deadlock` — when false, do not check for deadlock. Default: true.
  - `:dump` — when true, read all distinct states and all steps between
    them from a TLC graph dump (`-dump dot`).
  - `:timeout` — the time limit in seconds. Default: 120.
  - `:name` — the name of the config file. Default: `"check"`.
  """
  @spec run(Path.t(), String.t(), String.t(), keyword()) :: run()
  def run(dir, spec_file, cfg, opts) do
    jar = Keyword.fetch!(opts, :jar)
    name = Keyword.get(opts, :name, "check")
    timeout = Keyword.get(opts, :timeout, 120)
    cfg_file = "#{name}.cfg"
    dump_file = "#{name}_graph"

    File.write!(Path.join(dir, cfg_file), cfg)
    File.rm(Path.join(dir, dump_file <> ".dot"))

    # TLC writes its standard modules (TLC.tla, Integers.tla, ...) into
    # java.io.tmpdir. Two TLC processes that share that directory can read
    # a half-written file and fail to parse. Each run gets its own one.
    tmp = Path.join(dir, "tmp_#{name}")
    File.mkdir_p!(tmp)

    args =
      ["--kill-after=5", Integer.to_string(timeout), "java", "-XX:+UseParallelGC"] ++
        ["-Djava.io.tmpdir=#{tmp}", "-jar", jar] ++
        ["-config", cfg_file, "-workers", "1", "-cleanup", "-metadir", "states_#{name}"] ++
        if(Keyword.get(opts, :deadlock, true), do: [], else: ["-deadlock"]) ++
        if(Keyword.get(opts, :dump, false), do: ["-dump", "dot", dump_file], else: []) ++
        [spec_file]

    {output, exit_code} = System.cmd("timeout", args, cd: dir, stderr_to_stdout: true)
    File.rm_rf(Path.join(dir, "states_#{name}"))
    File.rm_rf(tmp)
    File.write!(Path.join(dir, "#{name}.out"), output)

    if exit_code in [124, 137] do
      %{empty_run(output) | status: :timeout}
    else
      parse_output(output, dir, dump_file, Keyword.get(opts, :dump, false))
    end
  end

  defp empty_run(output) do
    %{
      status: :ok,
      kind: nil,
      property: nil,
      message: nil,
      trace: [],
      distinct: nil,
      depth: nil,
      states: nil,
      edges: nil,
      constant: false,
      loop: nil,
      output: output
    }
  end

  defp parse_output(output, dir, dump_file, dump?) do
    lines = String.split(output, "\n")
    base = empty_run(output)
    initial = initial_violation(lines)

    constant = constant_false(lines)

    run =
      case TLCParser.parse(output) do
        # TLC does not search when an invariant is a constant FALSE. Each
        # state violates it, so it is a violation in the initial state.
        _ when is_binary(constant) ->
          %{base | status: :violated, kind: :invariant, property: constant, constant: true}

        {:ok, stats} ->
          %{base | status: :ok, distinct: stats.distinct_states, depth: stats.depth}

        {:error, _violation, _stats} when is_binary(initial) ->
          violated_initially(base, lines)

        {:error, %{kind: :error} = violation, _stats} ->
          %{base | status: :error, kind: :error, message: violation.message || output}

        {:error, violation, stats} ->
          %{
            base
            | status: :violated,
              kind: violation.kind,
              property: violation.property,
              trace: parse_trace(lines),
              loop: parse_loop(lines),
              distinct: stats.distinct_states,
              depth: stats.depth
          }
      end

    if dump? and run.status == :ok do
      {states, edges} = parse_dot(File.read!(Path.join(dir, dump_file <> ".dot")))
      %{run | states: states, edges: edges}
    else
      run
    end
  end

  defp constant_false(lines) do
    Enum.find_value(lines, fn line ->
      case Regex.run(~r/^Error: The invariant of (\w+) is equal to FALSE/, line) do
        [_, name] -> name
        nil -> nil
      end
    end)
  end

  # "Error: Invariant X is violated by the initial state:" is followed by
  # the variable lines, with no "State 1:" header.
  defp initial_violation(lines) do
    Enum.find_value(lines, fn line ->
      case Regex.run(~r/^Error: Invariant (.+) is violated by the initial state:/, line) do
        [_, name] -> name
        nil -> nil
      end
    end)
  end

  defp violated_initially(base, lines) do
    name = initial_violation(lines)

    vars =
      lines
      |> Enum.drop_while(&(not String.starts_with?(&1, "Error: Invariant")))
      |> tl()
      |> Enum.take_while(&(String.trim(&1) != ""))
      |> TLAValue.parse_assignments()

    %{
      base
      | status: :violated,
        kind: :invariant,
        property: name,
        trace: [%{action: nil, vars: vars}]
    }
  end

  @doc """
  Reads a counterexample from TLC output lines.
  """
  @spec parse_trace([String.t()]) :: [%{action: String.t() | nil, vars: map()}]
  def parse_trace(lines) do
    lines
    |> Enum.drop_while(&(not Regex.match?(~r/^State 1:/, &1)))
    |> Enum.reject(&Regex.match?(~r/^(State \d+: Stuttering|Back to state \d+:)/, &1))
    |> chunk_states()
    |> Enum.map(fn [header | body] ->
      action =
        case Regex.run(~r/^State \d+: <(\w+)/, header) do
          [_, "Initial"] -> nil
          [_, action] -> action
          nil -> nil
        end

      %{action: action, vars: TLAValue.parse_assignments(body)}
    end)
  end

  @doc """
  Reads the end of a liveness counterexample: `{:back_to, n}` when the
  behavior goes back to state `n`, `:stutter` when it stays in its last
  state forever, or `nil` for a finite trace.
  """
  @spec parse_loop([String.t()]) :: nil | :stutter | {:back_to, pos_integer()}
  def parse_loop(lines) do
    Enum.find_value(lines, fn line ->
      cond do
        match = Regex.run(~r/^Back to state (\d+):/, line) ->
          {:back_to, String.to_integer(Enum.at(match, 1))}

        Regex.match?(~r/^State \d+: Stuttering/, line) ->
          :stutter

        true ->
          nil
      end
    end)
  end

  # Splits lines into state blocks. A block starts at "State N:" and ends
  # at a blank line.
  defp chunk_states(lines) do
    {blocks, current} =
      Enum.reduce(lines, {[], nil}, fn line, {blocks, current} ->
        cond do
          Regex.match?(~r/^State \d+:/, line) ->
            {push(blocks, current), [line]}

          current != nil and String.trim(line) == "" ->
            {push(blocks, current), nil}

          current != nil ->
            {blocks, [line | current]}

          true ->
            {blocks, current}
        end
      end)

    blocks |> push(current) |> Enum.reverse()
  end

  defp push(blocks, nil), do: blocks
  defp push(blocks, current), do: [Enum.reverse(current) | blocks]

  @doc """
  Reads the states and the steps of a TLC graph dump (`-dump dot`).

  Gives `{states, edges}`. Each state is a map from variable name to
  value. Each edge is a `{from, to}` pair of states. A step from a state
  to itself is an edge too.
  """
  @spec parse_dot(String.t()) :: {[map()], [{map(), map()}]}
  def parse_dot(text) do
    lines = String.split(text, "\n")

    nodes =
      for line <- lines,
          [_, id, label] <- [Regex.run(~r/^(-?\d+) \[label="(.*)"(?:,[^\]]*)?\];?$/, line)],
          into: %{} do
        {id, label |> unescape() |> String.split("\n") |> TLAValue.parse_assignments()}
      end

    edges =
      for line <- lines,
          [_, from, to] <- [Regex.run(~r/^(-?\d+) -> (-?\d+)\b/, line)],
          uniq: true do
        {Map.fetch!(nodes, from), Map.fetch!(nodes, to)}
      end

    {Map.values(nodes), edges}
  end

  defp unescape(label) do
    label
    |> String.replace("\\n", "\n")
    |> String.replace("\\\"", "\"")
    |> String.replace("\\\\", "\\")
  end
end
