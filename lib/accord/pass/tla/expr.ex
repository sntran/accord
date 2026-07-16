defmodule Accord.Pass.TLA.Expr do
  @moduledoc """
  Shared expression compilation for TLA+ passes.

  Wraps `Accord.TLA.GuardCompiler`, converting unsupported forms and
  unresolved identifiers into pentiment reports carrying the caller's
  error code and span:

  - untranslatable guard/invariant expressions report the caller's code
    (E041 for guards and property expressions, E042 for update values,
    E045 for `where:` constraints);
  - identifiers that would not resolve in the generated spec — bare
    variables not bound to any declared argument, or field access on a
    track that does not exist — always report E043.

  Anything the model cannot faithfully express is a loud, span-carrying
  diagnostic. A formula that silently omitted a condition (or bound the
  wrong variable) would make TLC verify a different protocol than the
  monitor enforces.
  """

  alias Accord.IR
  alias Accord.TLA.GuardCompiler
  alias Pentiment.Report

  import Accord.Pass.Helpers, only: [maybe_add_source: 2, maybe_add_span_label: 3]

  @doc """
  Compiles an expression AST to TLA+, reporting failures with spans.

  ## Options

  - `:ir` — the protocol IR (for source attachment). Required.
  - `:code` — error code for untranslatable forms. Required.
  - `:context` — human label for the expression site ("guard", "update",
    "where: constraint", "invariant", ...). Required.
  - `:track_names` — MapSet of track name strings; field accesses must
    resolve to one of them. Required.
  - `:span` — span for report labels. Optional.
  - `:render_field` — forwarded to `GuardCompiler` (multi-session track
    access rendering). Optional.
  """
  @spec compile(Macro.t(), map(), keyword()) :: {:ok, String.t()} | {:error, [Report.t()]}
  def compile(ast, bindings, opts) do
    ir = Keyword.fetch!(opts, :ir)
    code = Keyword.fetch!(opts, :code)
    context = Keyword.fetch!(opts, :context)
    track_names = Keyword.fetch!(opts, :track_names)
    span = Keyword.get(opts, :span)
    compiler_opts = Keyword.take(opts, [:render_field])

    case GuardCompiler.compile(ast, bindings, compiler_opts) do
      {:ok, tla, idents} ->
        case identifier_errors(idents, bindings, track_names, ir, span, context) do
          [] -> {:ok, tla}
          errors -> {:error, errors}
        end

      {:error, unsupported} ->
        {:error, [unsupported_report(unsupported, code, ir, span, context)]}
    end
  end

  @doc """
  Report for an update writing to a track that does not exist.
  """
  @spec unknown_track_report(String.t(), MapSet.t(String.t()), IR.t(), term(), String.t()) ::
          Report.t()
  def unknown_track_report(name, track_names, ir, span, context) do
    Report.error("unknown track `#{name}` referenced in #{context}")
    |> Report.with_code("E043")
    |> Report.with_help(known_tracks_help(track_names))
    |> maybe_add_source(ir.source_file)
    |> maybe_add_span_label(span, "references `#{name}`")
  end

  # -- Private --

  defp unsupported_report(unsupported, code, ir, span, context) do
    details = Enum.map_join(unsupported, "\n  ", & &1.message)

    Report.error("cannot compile #{context} to TLA+:\n  #{details}")
    |> Report.with_code(code)
    |> Report.with_help(
      "supported forms: comparisons, arithmetic, and/or/not, track access " <>
        "(tracks.field), length/1, div/rem/abs, is_integer/is_boolean; " <>
        "restructure the expression, or compile with tla: :warn to skip verification"
    )
    |> maybe_add_source(ir.source_file)
    |> maybe_add_span_label(span, "in this #{context}")
  end

  defp identifier_errors(idents, bindings, track_names, ir, span, context) do
    enumerated = enumerated_atom_strings(ir)

    idents
    |> Enum.uniq()
    |> Enum.flat_map(fn
      {name, :bare} ->
        [bare_report(name, bindings, ir, span, context)]

      {name, :field} ->
        if MapSet.member?(track_names, name) do
          []
        else
          [unknown_track_report(name, track_names, ir, span, context)]
        end

      {name, :atom_literal} ->
        if MapSet.member?(enumerated, name) do
          []
        else
          [atom_literal_report(name, enumerated, ir, span, context)]
        end
    end)
  end

  # Atoms in a formula render as concrete TLA+ strings, so they must be
  # members of an explicit enumerated domain (`[:fast, :slow]`) whose values
  # render the same way. An atom outside such a domain would fall to the
  # builtin `{:model_values, N}` domain — abstract, symmetric identifiers
  # that TLC permutes and that a formula may not name (naming one breaks
  # symmetry reduction). Reported at compile time rather than as a TLC crash.
  defp atom_literal_report(name, enumerated, ir, span, context) do
    Report.error("atom :#{name} in #{context} is not a declared enumerated value")
    |> Report.with_code("E047")
    |> Report.with_help(enumerated_help(name, enumerated))
    |> maybe_add_source(ir.source_file)
    |> maybe_add_span_label(span, "names :#{name}")
  end

  defp enumerated_help(name, enumerated) do
    if MapSet.size(enumerated) == 0 do
      "declare the domain inline, e.g. `track :mode, :atom, domain: [:#{name}, ...]`, " <>
        "so comparing against :#{name} renders a concrete value the model can check"
    else
      known = enumerated |> Enum.sort() |> Enum.map_join(", ", &":#{&1}")

      "add :#{name} to an enumerated domain (declared values: #{known}); atoms outside " <>
        "one render as symmetric model values, which a formula may not name"
    end
  end

  # Atoms that may be named in a formula: the members of every explicit-list
  # domain declared inline — per-track (`domain: [...]`) or in the `model`
  # block (`domain :name, [...]`). Model-value domains (tuples) are excluded
  # on purpose; their values are symmetric and unnameable.
  defp enumerated_atom_strings(%IR{} = ir) do
    track_lists = for track <- ir.tracks, is_list(track.domain), do: track.domain
    block_lists = for {:domain, {_name, spec}} <- ir.model, is_list(spec), do: spec

    (track_lists ++ block_lists)
    |> List.flatten()
    |> Enum.filter(&(is_atom(&1) and &1 not in [true, false, nil]))
    |> Enum.map(&Atom.to_string/1)
    |> MapSet.new()
  end

  defp bare_report(name, bindings, ir, span, context) do
    known =
      bindings
      |> Map.keys()
      |> Enum.sort()
      |> Enum.map_join(", ", &inspect/1)

    help =
      if known == "" do
        "only tracks.field access can be referenced here"
      else
        "use a declared argument name (available: #{known}) or access a track via tracks.field"
      end

    Report.error("variable `#{name}` in #{context} is not bound to any declared argument")
    |> Report.with_code("E043")
    |> Report.with_help(help)
    |> maybe_add_source(ir.source_file)
    |> maybe_add_span_label(span, "references `#{name}`")
  end

  defp known_tracks_help(track_names) do
    case Enum.sort(track_names) do
      [] -> "this protocol declares no tracks"
      names -> "declared tracks: #{Enum.join(names, ", ")}"
    end
  end
end
