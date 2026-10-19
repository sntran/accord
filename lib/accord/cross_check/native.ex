defmodule Accord.CrossCheck.Native do
  @moduledoc """
  Runs the native TLA+ checker (`Accord.TLA.Checker`) as the reference of
  the cross-check, in place of TLC.

  The checker writes its report in the style of TLC, and a graph dump in
  the format of `-dump dot`, so `Accord.CrossCheck.TLC.read_output/4`
  reads both references in the same way. The checker and the explorer
  are independent implementations, so the comparison stays meaningful
  without Java.
  """

  alias Accord.CrossCheck.TLC
  alias Accord.TLA.Checker
  alias Accord.TLA.Checker.Value

  @doc """
  Runs the checker on `spec_file` (in `dir`) with the config text `cfg`.
  The options and the result are those of `Accord.CrossCheck.TLC.run/4`
  (`:jar` is not used).
  """
  @spec run(Path.t(), String.t(), String.t(), keyword()) :: TLC.run()
  def run(dir, spec_file, cfg, opts) do
    name = Keyword.get(opts, :name, "check")
    dump? = Keyword.get(opts, :dump, false)
    cfg_path = Path.join(dir, "#{name}.cfg")
    dump_file = "#{name}_graph"
    File.write!(cfg_path, cfg)

    timeout = Keyword.get(opts, :timeout, 120) * 1000

    task =
      Task.async(fn ->
        Checker.run(Path.join(dir, spec_file),
          config: cfg_path,
          deadlock: Keyword.get(opts, :deadlock, true),
          graph: dump?
        )
      end)

    case Task.yield(task, timeout) || Task.shutdown(task, :brutal_kill) do
      {:ok, result} ->
        output = Checker.format(result)
        File.write!(Path.join(dir, "#{name}.out"), output)

        if dump? and Map.has_key?(result, :graph),
          do: write_dot(Path.join(dir, dump_file <> ".dot"), result)

        TLC.read_output(output, dir, dump_file, dump? and Map.has_key?(result, :graph))

      _ ->
        %{TLC.read_output("", dir, dump_file, false) | status: :timeout}
    end
  end

  # A graph dump in the format of TLC's `-dump dot`.
  defp write_dot(path, result) do
    nodes =
      result.graph.states
      |> Enum.with_index()
      |> Enum.map(fn {state, i} ->
        "#{i} [label=\"#{escape(label(result.variables, state))}\"];"
      end)

    edges = Enum.map(result.graph.edges, fn {from, to} -> "#{from} -> #{to};" end)
    File.write!(path, Enum.join(["strict digraph DiskGraph {"] ++ nodes ++ edges ++ ["}"], "\n"))
  end

  defp label(variables, state) do
    variables
    |> Enum.with_index()
    |> Enum.map_join("\n", fn {name, i} -> "/\\ #{name} = #{Value.show(elem(state, i))}" end)
  end

  defp escape(text) do
    text
    |> String.replace("\\", "\\\\")
    |> String.replace("\"", "\\\"")
    |> String.replace("\n", "\\n")
  end
end
