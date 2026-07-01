defmodule Accord.Pass.ValidateRoles do
  @moduledoc """
  Validates role declarations.

  Accord protocols are two-party: the first declared role initiates
  calls and casts (default `:client`), the second replies and pushes
  events (default `:server`). Blame derives from message direction, and
  declared role names label it in diagnostics.

  Checks:
  - At most two roles are declared (E050). N-party protocols require
    projecting a global protocol onto per-participant views — a
    different tool; the monitor is architecturally a two-endpoint proxy.
  - Role names are unique (E051).
  """

  alias Accord.IR
  alias Pentiment.{Label, Report}

  import Accord.Pass.Helpers

  @spec run(IR.t()) :: {:ok, IR.t()} | {:error, [Report.t()]}
  def run(%IR{} = ir) do
    errors = check_role_count(ir) ++ check_duplicate_roles(ir)

    case errors do
      [] -> {:ok, ir}
      errors -> {:error, errors}
    end
  end

  defp check_role_count(%IR{roles: roles} = ir) when length(roles) > 2 do
    extra = Enum.drop(roles, 2)

    labels =
      for role <- extra, role.span != nil do
        Label.primary(role.span, "third role declared here")
      end

    [
      Report.error(
        "protocols are two-party: at most two roles may be declared, got #{length(roles)}"
      )
      |> Report.with_code("E050")
      |> Report.with_help(
        "the first role initiates calls/casts, the second replies and pushes events; " <>
          "N-party protocols require projection onto per-participant contracts"
      )
      |> maybe_add_source(ir.source_file)
      |> Report.with_labels(labels)
    ]
  end

  defp check_role_count(_ir), do: []

  defp check_duplicate_roles(%IR{roles: roles} = ir) do
    roles
    |> Enum.group_by(& &1.name)
    |> Enum.filter(fn {_name, declarations} -> length(declarations) > 1 end)
    |> Enum.sort_by(fn {name, _} -> name end)
    |> Enum.map(fn {name, [first | duplicates]} ->
      labels =
        [Label.secondary(first.span, "first defined here")] ++
          Enum.map(duplicates, &Label.primary(&1.span, "duplicate declaration"))

      labels = Enum.reject(labels, &is_nil(&1.span))

      Report.error("duplicate role name :#{name}")
      |> Report.with_code("E051")
      |> Report.with_help("each role must be declared once")
      |> maybe_add_source(ir.source_file)
      |> Report.with_labels(labels)
    end)
  end
end
