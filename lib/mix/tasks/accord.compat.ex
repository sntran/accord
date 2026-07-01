defmodule Mix.Tasks.Accord.Compat do
  @moduledoc """
  Checks protocol compatibility across versions.

  Answers the rolling-upgrade question: can clients speaking the old
  contract talk to a server monitored by the new one? (For client-first
  deployments, swap the arguments.)

  ## Usage

      # Snapshot the released contract into the repo:
      mix accord.compat --snapshot MyApp.Protocol priv/contracts/my_app.ir

      # Gate changes against the released snapshot (CI):
      mix accord.compat MyApp.Protocol --against priv/contracts/my_app.ir

      # Compare two compiled modules directly:
      mix accord.compat MyApp.ProtocolV1 MyApp.ProtocolV2

  In `--against` mode the snapshot is the OLD contract and the module is
  the NEW one. Exits non-zero on incompatibilities; guard/constraint
  changes are advisory warnings.
  """

  use Mix.Task

  alias Accord.Compat
  alias Accord.Compat.Snapshot

  @shortdoc "Check protocol compatibility across versions"

  @impl Mix.Task
  def run(args) do
    Mix.Task.run("compile", [])

    {opts, positional, _} =
      OptionParser.parse(args, strict: [snapshot: :boolean, against: :string])

    cond do
      Keyword.get(opts, :snapshot, false) ->
        run_snapshot(positional)

      path = Keyword.get(opts, :against) ->
        run_against(positional, path)

      true ->
        run_modules(positional)
    end
  end

  defp run_snapshot([module_name, path]) do
    mod = load_module!(module_name)
    :ok = Snapshot.save(mod, path)
    Mix.shell().info("Snapshot of #{inspect(mod)} written to #{path}")
  end

  defp run_snapshot(_),
    do: Mix.raise("usage: mix accord.compat --snapshot Module path/to/snapshot.ir")

  defp run_against([module_name], path) do
    mod = load_module!(module_name)

    case Snapshot.load(path) do
      {:ok, old_ir} ->
        report(Compat.check(old_ir, mod), "#{path} (snapshot)", inspect(mod))

      {:error, reason} ->
        Mix.raise("cannot load snapshot #{path}: #{inspect(reason)}")
    end
  end

  defp run_against(_, _),
    do: Mix.raise("usage: mix accord.compat Module --against path/to/snapshot.ir")

  defp run_modules([old_name, new_name]) do
    old_mod = load_module!(old_name)
    new_mod = load_module!(new_name)
    report(Compat.check(old_mod, new_mod), inspect(old_mod), inspect(new_mod))
  end

  defp run_modules(_) do
    Mix.raise("""
    usage:
      mix accord.compat --snapshot Module path.ir
      mix accord.compat Module --against path.ir
      mix accord.compat OldModule NewModule
    """)
  end

  defp load_module!(name) do
    # Safe: developer-provided CLI argument, not untrusted input.
    mod = Module.concat([String.to_atom(name)])

    unless Code.ensure_loaded?(mod) and function_exported?(mod, :__ir__, 0) do
      Mix.raise("#{inspect(mod)} is not a compiled Accord protocol")
    end

    mod
  end

  defp report(result, old_label, new_label) do
    Mix.shell().info("old clients: #{old_label}\nnew contract: #{new_label}\n")

    for warning <- result.warnings do
      Mix.shell().info(Pentiment.format(warning, %{}))
    end

    if result.compatible? do
      Mix.shell().info(
        "#{IO.ANSI.green()}✓ compatible#{IO.ANSI.reset()} — old clients can talk " <>
          "to the new contract" <> warning_note(result)
      )
    else
      for error <- result.errors do
        Mix.shell().info(Pentiment.format(error, %{}))
      end

      Mix.shell().info(
        "#{IO.ANSI.red()}✗ incompatible#{IO.ANSI.reset()} — " <>
          "#{length(result.errors)} breaking change(s)"
      )

      exit({:shutdown, 1})
    end
  end

  defp warning_note(%{warnings: []}), do: ""
  defp warning_note(%{warnings: ws}), do: " (#{length(ws)} advisory warning(s))"
end
