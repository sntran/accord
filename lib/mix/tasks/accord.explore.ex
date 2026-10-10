defmodule Mix.Tasks.Accord.Explore do
  @moduledoc """
  Checks protocols with the native explorer. Java and TLC are not
  necessary.

  The explorer (`Accord.Explore`) does a breadth-first search over the
  same finite model as the TLA+ spec. It checks `TypeInvariant`, the
  invariants, the action properties, deadlock, and liveness under the
  fairness of each liveness property.

  ## Usage

      mix accord.explore                     # all protocols
      mix accord.explore MyApp.Protocol      # one protocol
      mix accord.explore --no-deadlock       # do not check deadlock
      mix accord.explore --max-states 50000  # state limit

  Protocols with `tla: :off` are skipped, as in `mix accord.check`. The
  task fails when it finds a violation, or when a model is larger than
  the state limit.
  """

  use Mix.Task

  alias Accord.Explore
  alias Accord.Explore.Model

  @shortdoc "Check Accord protocols with the native explorer"

  @impl Mix.Task
  def run(args) do
    Mix.Task.run("compile", [])

    {opts, names, _} =
      OptionParser.parse(args, strict: [deadlock: :boolean, max_states: :integer])

    protocols =
      case names do
        [] -> discover_protocols()
        names -> Enum.map(names, &Module.concat([&1]))
      end

    results =
      Enum.map(protocols, fn mod ->
        result =
          try do
            Explore.run(mod,
              deadlock: Keyword.get(opts, :deadlock, true),
              max_states: Keyword.get(opts, :max_states, 200_000)
            )
          rescue
            e in Model.UnsupportedFailure -> {:unsupported, Exception.message(e)}
          end

        Mix.shell().info(format(mod, result))
        {mod, result}
      end)

    failed =
      for {mod, %Explore.Result{} = result} <- results, not Explore.Result.ok?(result), do: mod

    if failed != [] do
      Mix.raise("violations in: " <> Enum.map_join(failed, ", ", &inspect/1))
    end
  end

  defp format(mod, {:unsupported, message}), do: "- #{inspect(mod)}: not checked (#{message})"

  defp format(mod, %Explore.Result{} = result) do
    header =
      "#{mark(result)} #{inspect(mod)}: #{result.distinct} states, depth #{result.depth}" <>
        if(result.complete, do: "", else: " (stopped at the state limit)")

    violations =
      result.violations
      |> Enum.sort_by(fn {name, _} -> name end)
      |> Enum.map(fn {_name, v} -> format_violation(result.model, v) end)

    skipped = Enum.map(result.skipped, fn {name, why} -> "    - #{name}: #{why}" end)
    Enum.join([header | violations ++ skipped], "\n")
  end

  defp mark(result), do: if(Explore.Result.ok?(result), do: "✓", else: "✗")

  defp format_violation(model, violation) do
    title =
      case violation.kind do
        :deadlock -> "    ✗ deadlock"
        :error -> "    ✗ evaluation error: #{violation.message}"
        :action -> "    ✗ action property #{violation.name} is violated"
        :invariant -> "    ✗ invariant #{violation.name} is violated"
        :liveness -> "    ✗ liveness property #{violation.name} is violated"
      end

    steps =
      violation.trace
      |> Enum.with_index(1)
      |> Enum.map(fn {step, i} ->
        "      #{i}. #{format_label(step.label)} #{format_state(model, step.state)}"
      end)

    loop =
      case Map.get(violation, :loop) do
        nil ->
          []

        :stutter ->
          ["      … stays in state #{length(violation.trace)} forever"]

        %{to: to, label: label} ->
          ["      … #{format_label(label)} goes back to state #{to}, forever"]
      end

    Enum.join([title | steps] ++ loop, "\n")
  end

  defp format_label(nil), do: "initial"

  defp format_label(label) do
    session = if Map.get(label, :session, 1) > 1, do: "session #{label.session}: ", else: ""

    step =
      case label.kind do
        :call -> "#{inspect(label.message)} → #{inspect(label.reply)}"
        :timeout -> "state timeout"
        :terminating -> "terminal"
        _ -> inspect(label[:message])
      end

    "#{session}#{step}"
  end

  defp format_state(model, {sessions, shared}) do
    parts =
      sessions
      |> Tuple.to_list()
      |> Enum.with_index(1)
      |> Enum.map(fn {{name, tracks, _counters}, i} ->
        prefix = if model.sessions > 1, do: "s#{i}=", else: ""
        "#{prefix}#{name} #{inspect(tracks)}"
      end)

    shared_part = if shared == %{}, do: [], else: ["shared #{inspect(shared)}"]
    "[" <> Enum.join(parts ++ shared_part, ", ") <> "]"
  end

  defp discover_protocols do
    Mix.Project.compile_path()
    |> Path.join("*.beam")
    |> Path.wildcard()
    |> Enum.map(&(&1 |> Path.basename(".beam") |> String.to_atom()))
    |> Enum.filter(fn mod ->
      Code.ensure_loaded?(mod) and function_exported?(mod, :__tla_span__, 1) and
        mod.__tla_status__() == :ok
    end)
    |> Enum.sort()
  end
end
