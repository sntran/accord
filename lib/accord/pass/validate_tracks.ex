defmodule Accord.Pass.ValidateTracks do
  @moduledoc """
  Validates track declarations.

  Checks:
  - Track names are unique. A duplicate declaration would silently shadow
    the first, making the initial value and type depend on declaration
    order.
  """

  alias Accord.IR
  alias Pentiment.{Label, Report}

  import Accord.Pass.Helpers

  @spec run(IR.t()) :: {:ok, IR.t()} | {:error, [Report.t()]}
  def run(%IR{} = ir) do
    errors = check_duplicate_names(ir)

    case errors do
      [] -> {:ok, ir}
      errors -> {:error, errors}
    end
  end

  defp check_duplicate_names(%IR{tracks: tracks} = ir) do
    tracks
    |> Enum.group_by(& &1.name)
    |> Enum.filter(fn {_name, declarations} -> length(declarations) > 1 end)
    |> Enum.sort_by(fn {name, _} -> name end)
    |> Enum.map(fn {name, [first | duplicates]} ->
      labels =
        [Label.secondary(first.span, "first defined here")] ++
          Enum.map(duplicates, &Label.primary(&1.span, "duplicate declaration"))

      labels = Enum.reject(labels, &is_nil(&1.span))

      Report.error("duplicate track name :#{name}")
      |> Report.with_code("E040")
      |> Report.with_help(
        "each track must be declared once; remove or rename the duplicate declaration"
      )
      |> maybe_add_source(ir.source_file)
      |> Report.with_labels(labels)
    end)
  end
end
