defmodule Accord.TLA.Checker.StandardModules do
  @moduledoc """
  The texts of the standard modules of SANY (`Naturals`, `Sequences`,
  `TLC`, ...), from `priv/tla/standard_modules` (copied from the
  tlaplus repository, MIT license).

  The model checker does not evaluate these definitions: it has native
  versions of the operators (see `Accord.TLA.Checker.Stdlib`). The
  semantic checks (see `Accord.TLA.Checker.Semantic`) use the texts for
  the names, the arities, and the levels of the operators, as SANY does.
  """

  @dir Path.join([__DIR__, "..", "..", "..", "..", "priv", "tla", "standard_modules"])
       |> Path.expand()

  @files @dir |> File.ls!() |> Enum.filter(&String.ends_with?(&1, ".tla")) |> Enum.sort()

  for file <- @files, do: @external_resource(Path.join(@dir, file))

  @sources Map.new(@files, fn file ->
             {Path.rootname(file), File.read!(Path.join(@dir, file))}
           end)

  @doc "The text of a standard module, or nil."
  @spec source(String.t()) :: String.t() | nil
  def source(name), do: Map.get(@sources, name)

  @doc "The names of the standard modules."
  @spec names() :: [String.t()]
  def names, do: Map.keys(@sources)
end
