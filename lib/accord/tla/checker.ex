defmodule Accord.TLA.Checker do
  @moduledoc """
  A TLA+ model checker in Elixir. It reads a `.tla` module and a `.cfg`
  model file, and does an exhaustive check of the model with the rules
  of TLC. It does not need Java.

      Accord.TLA.Checker.check("JobQueue.tla")
      #=> {:ok, %{states_generated: 42, distinct_states: 17, depth: 6, warnings: []}}

  The result has the same shape as the result of
  `Accord.TLA.TLCParser.parse/1`, so the callers of TLC can use this
  checker without change. `run/2` gives the full result, with the values
  of the trace as TLA+ values.

  ## What it checks

  - `INIT`/`NEXT` or `SPECIFICATION` (with `WF_` and `SF_` fairness).
  - `INVARIANT`, `PROPERTY` (state predicates, action properties
    `[][A]_v`, and liveness: `~>`, `[]<>`, `<>`, `<>[]`, and fairness
    conditions as properties).
  - `CONSTANT` values, model values, and replacements (`<-`, `<-[M]`).
  - `CONSTRAINT`, `ACTION_CONSTRAINT`, `SYMMETRY`, `VIEW`, deadlock.
  - `ASSUME`.

  The standard modules (Naturals, Integers, Sequences, FiniteSets, Bags,
  TLC, TLCExt, and some others) are in Elixir. The other modules come
  from `.tla` files in the directory of the root module or in `:paths`.
  """

  alias Accord.TLA.Checker.{Config, Context, Parser, Search, Value}

  @type result ::
          {:ok, Accord.TLA.TLCParser.stats()}
          | {:error, Accord.TLA.TLCParser.violation(), Accord.TLA.TLCParser.stats()}

  @doc """
  Does a check of a model. The result has the shape of the result of
  `Accord.TLA.TLCParser.parse/1`.

  Options:

  - `:config` — the path of the `.cfg` file (default: the path of the
    module with the extension `.cfg`), or a `%Config{}`.
  - `:paths` — more directories to search for modules.
  - `:deadlock` — `false` to stop the deadlock check.
  - `:max_states` — stop after this number of distinct states.
  - `:invariant_exprs` — more invariants, as TLA+ expressions (text).
  - `:warn` — `false` for TLC's `-nowarning` (see `Accord.TLA.Checker.Eval`).
  """
  @spec check(Path.t(), keyword()) :: result()
  def check(path, opts \\ []) do
    path |> run(opts) |> to_tlc()
  end

  @doc """
  Does a check of a model and gives the full result.
  """
  def run(path, opts \\ []) do
    with {:ok, config} <- config(path, opts),
         {:ok, ctx} <- load(path, config, opts),
         {:ok, invariants} <- invariant_exprs(opts) do
      Search.run(ctx, Keyword.put(opts, :invariant_exprs, invariants))
    else
      {:error, kind, message} -> load_error(kind, message)
    end
  end

  defp config(path, opts) do
    case Keyword.get(opts, :config) do
      %Config{} = c ->
        {:ok, c}

      nil ->
        cfg = Path.rootname(path) <> ".cfg"
        # Without a .cfg file, the config can be a CONFIG section of the
        # module file.
        if File.exists?(cfg), do: read_config(cfg), else: read_config(path)

      cfg_path ->
        read_config(cfg_path)
    end
  end

  defp read_config(path) do
    case File.read(path) do
      {:ok, text} -> {:ok, text |> config_section() |> Config.parse()}
      {:error, reason} -> {:error, :config, "cannot read #{path}: #{:file.format_error(reason)}"}
    end
  rescue
    e in Config.Error -> {:error, :config, Exception.message(e)}
  end

  # A file with a `---- CONFIG Name ----` section (after a module) gives
  # the text of that section.
  defp config_section(text) do
    case Regex.run(~r/^-{4,}[ \t]*CONFIG[ \t]+\w+[ \t]*-{4,}[^\n]*\n(.*?)^={4,}/ms, text) do
      [_, section] -> section
      nil -> if text =~ ~r/^-{4,}[ \t]*MODULE/m, do: "", else: text
    end
  end

  defp load(path, config, opts) do
    {:ok, Context.load(path, config, paths: Keyword.get(opts, :paths, []))}
  rescue
    e in [Parser.Error, Accord.TLA.Checker.Lexer.Error] ->
      {:error, :parse, Exception.message(e)}

    e in Context.Error ->
      message = Exception.message(e)
      kind = if String.starts_with?(message, "cannot "), do: :parse, else: :config
      {:error, kind, message}

    e in Value.Error ->
      {:error, :config, Exception.message(e)}
  end

  # `:invariant_exprs`: invariants as TLA+ text (as TLC's `-inv`).
  defp invariant_exprs(opts) do
    {:ok,
     opts |> Keyword.get(:invariant_exprs, []) |> Enum.map(&{&1, Parser.parse_expression(&1)})}
  rescue
    e in [Parser.Error, Accord.TLA.Checker.Lexer.Error] -> {:error, :parse, Exception.message(e)}
  end

  defp load_error(kind, message) do
    %{
      status: :error,
      kind: kind,
      property: nil,
      message: message,
      trace: [],
      loop: nil,
      stats: %{generated: 0, distinct: 0, depth: 0, left: 0},
      warnings: [],
      variables: []
    }
  end

  @doc """
  Converts a full result to the shape of `Accord.TLA.TLCParser.parse/1`.
  """
  def to_tlc(result) do
    stats = %{
      states_generated: result.stats.generated,
      distinct_states: result.stats.distinct,
      depth: result.stats.depth,
      warnings: result.warnings
    }

    case result.status do
      :ok ->
        {:ok, stats}

      :incomplete ->
        {:ok, stats}

      _ ->
        kind =
          if result.kind in [:invariant, :deadlock, :temporal, :action_property],
            do: result.kind,
            else: tlc_kind(result.kind)

        violation = %{
          kind: kind,
          property: result.property,
          message: result.message,
          trace: tlc_trace(result)
        }

        {:error, violation, stats}
    end
  end

  defp tlc_kind(:assumption), do: :error
  defp tlc_kind(:postcondition), do: :error
  defp tlc_kind(:possible), do: :error
  defp tlc_kind(:init_property), do: :temporal
  defp tlc_kind(_), do: :error

  defp tlc_trace(result) do
    states =
      result.trace
      |> Enum.with_index(1)
      |> Enum.map(fn {%{state: state, action: action}, n} ->
        %{number: n, action: action, assignments: assignments(result.variables, state)}
      end)

    case result.loop do
      nil ->
        states

      :stuttering ->
        states ++ [%{number: length(states) + 1, action: :stuttering, assignments: %{}}]

      {:back_to, index, label} ->
        states ++ [%{number: index + 1, action: label, assignments: %{}}]
    end
  end

  defp assignments(variables, state) when is_tuple(state) do
    variables
    |> Enum.with_index()
    |> Map.new(fn {name, i} -> {name, Value.show(elem(state, i))} end)
  end

  defp assignments(variables, state) when is_map(state) do
    variables
    |> Enum.with_index()
    |> Enum.flat_map(fn {name, i} ->
      case Map.fetch(state, i) do
        {:ok, v} -> [{name, Value.show(v)}]
        :error -> []
      end
    end)
    |> Map.new()
  end

  @doc """
  Formats a full result as text in the style of TLC.
  """
  def format(result) do
    header =
      case result.status do
        s when s in [:ok, :incomplete] ->
          "Model checking completed. No error has been found."

        _ ->
          case result.kind do
            :invariant ->
              "Error: Invariant #{result.property} is violated."

            :init_property ->
              "Error: Property #{result.property} is violated by the initial state."

            :action_property ->
              "Error: Action property #{result.property} is violated."

            :temporal ->
              "Error: Temporal properties were violated."

            :deadlock ->
              "Error: Deadlock reached."

            :assumption ->
              "Error: #{result.message}"

            :postcondition ->
              "Error: The postcondition #{result.property} is violated."

            _ ->
              "Error: #{result.message}"
          end
      end

    trace =
      case result.trace do
        [] ->
          []

        _ ->
          [
            "Error: The behavior up to this point is:"
            | Enum.flat_map(tlc_trace(result), &format_state(&1, result))
          ]
      end

    stats = [
      "#{result.stats.generated} states generated, #{result.stats.distinct} distinct states found, #{result.stats.left} states left on queue.",
      "The depth of the complete state graph search is #{result.stats.depth}."
    ]

    Enum.join(result.warnings ++ [header | trace] ++ stats, "\n")
  end

  defp format_state(%{number: n, action: :stuttering}, _), do: ["State #{n}: Stuttering", ""]

  defp format_state(%{number: n, action: action, assignments: a}, result) do
    head =
      cond do
        a == %{} -> "Back to state #{n}: <#{action}>"
        action == nil -> "State #{n}: <Initial predicate>"
        true -> "State #{n}: <#{action}>"
      end

    vars = for name <- result.variables, Map.has_key?(a, name), do: "/\\ #{name} = #{a[name]}"
    [head | vars] ++ [""]
  end
end
