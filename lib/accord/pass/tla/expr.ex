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
    end)
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
