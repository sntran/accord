defmodule Accord.TLA.GuardCompiler do
  @moduledoc """
  Compiles Elixir guard/constraint ASTs to TLA+ expressions.

  Handles the composable subset: comparisons, arithmetic, boolean
  operators, track field access, and bound parameter references. Forms
  outside this subset produce an `{:error, unsupported}` result — never a
  silent `TRUE` — so the caller can report exactly which expression the
  model cannot express.

  ## Bindings

  The bindings map controls how variables render:

  - `%{name => tla_var}` — a bound parameter (message/reply existential).
  - `%{name => {:list_length, tla_var}}` — a list abstracted to its length;
    `length(name)` compiles to the variable itself.
  - `%{name => :current}` / `%{name => :primed}` — action-property bindings;
    field access on a `:primed` variable emits `field'`.

  ## Emitted identifiers

  Successful compilation also returns the identifiers that were emitted
  from *unresolved* sources — bare variables not present in the bindings
  and track-field accesses. The caller validates these against the names
  that actually exist in the spec (existentials, track variables); anything
  unknown would surface as a TLC "Unknown identifier" error at best, or
  silently alias another variable at worst.

  - `{name, :bare}` — a bare variable with no binding.
  - `{name, :field}` — a `var.field` access (the field name is emitted).
  """

  @type unsupported :: %{message: String.t(), ast: Macro.t()}
  @type identifier_kind :: :bare | :field | :atom_literal
  @type emitted_identifier :: {String.t(), identifier_kind()}

  @comparison_ops [:>, :>=, :<, :<=, :==, :!=]
  @arithmetic_ops [:+, :-, :*]

  @doc """
  Compiles a quoted Elixir expression to a TLA+ expression string.

  Returns `{:ok, tla_string, emitted_identifiers}` on success, or
  `{:error, unsupported}` listing every sub-expression that has no TLA+
  equivalent.

  ## Options

  - `:render_field` — `(field_name, primed?) -> String.t()`; controls how
    track-field accesses render. The default emits `field` / `field'`;
    multi-session emission renders per-session tracks as `field[s]` /
    `field'[s]`.
  """
  @spec compile(Macro.t(), map(), keyword()) ::
          {:ok, String.t(), [emitted_identifier()]} | {:error, [unsupported()]}
  def compile(ast, bindings \\ %{}, opts \\ []) do
    render_field = Keyword.get(opts, :render_field, &default_render_field/2)
    {tla, acc} = do_compile(ast, bindings, new_acc(render_field))

    case acc.unsupported do
      [] -> {:ok, tla, Enum.reverse(acc.idents)}
      unsupported -> {:error, Enum.reverse(unsupported)}
    end
  end

  defp default_render_field(field, false), do: field
  defp default_render_field(field, true), do: field <> "'"

  defp new_acc(render_field), do: %{unsupported: [], idents: [], render_field: render_field}

  defp add_ident(acc, name, kind), do: %{acc | idents: [{name, kind} | acc.idents]}

  defp add_unsupported(acc, ast) do
    entry = %{
      message: "expression not compilable to TLA+: #{Macro.to_string(ast)}",
      ast: ast
    }

    %{acc | unsupported: [entry | acc.unsupported]}
  end

  # -- Literals --

  defp do_compile(n, _bindings, acc) when is_integer(n) do
    {Integer.to_string(n), acc}
  end

  defp do_compile(true, _bindings, acc), do: {"TRUE", acc}
  defp do_compile(false, _bindings, acc), do: {"FALSE", acc}
  defp do_compile(nil, _bindings, acc), do: {"NULL", acc}

  # An atom literal renders as a TLA+ string, matching how explicit-list
  # domains and track defaults render atoms (`{"fast", "slow"}`,
  # `default: :slow` → `"slow"`). `inspect/1` would emit `:fast`, which is
  # not valid TLA+. The atom is recorded so the caller can require it to be
  # a member of a declared enumerated domain (see `Accord.Pass.TLA.Expr`) —
  # naming an atom from a symmetric model-value domain is unsound.
  defp do_compile(atom, _bindings, acc) when is_atom(atom) do
    {~s("#{atom}"), add_ident(acc, Atom.to_string(atom), :atom_literal)}
  end

  defp do_compile(s, _bindings, acc) when is_binary(s) do
    {~s("#{s}"), acc}
  end

  # -- Variable reference --
  # Context (third element) is nil for unquoted vars or a module name for quoted vars.

  defp do_compile({var, _meta, context} = ast, bindings, acc)
       when is_atom(var) and is_atom(context) do
    case Map.get(bindings, var) do
      nil ->
        {Atom.to_string(var), add_ident(acc, Atom.to_string(var), :bare)}

      {:list_length, tla_name} ->
        {tla_name, acc}

      marker when marker in [:current, :primed] ->
        # A bare reference to the whole tracks value (e.g. `old != new` in
        # an action property) has no faithful TLA+ rendering — the caller
        # must compare individual fields.
        {"TRUE", add_unsupported(acc, ast)}

      tla_name ->
        {tla_name, acc}
    end
  end

  # -- Dot access: tracks.field → field --

  defp do_compile({{:., _meta1, [Access, :get]}, _meta2, [_map, key]}, _bindings, acc) do
    key_str = Atom.to_string(key)
    {acc.render_field.(key_str, false), add_ident(acc, key_str, :field)}
  end

  defp do_compile({{:., _meta1, [{var, _meta2, _ctx}, field]}, _meta3, []}, bindings, acc)
       when is_atom(field) do
    field_str = Atom.to_string(field)
    acc = add_ident(acc, field_str, :field)

    case Map.get(bindings, var) do
      :primed -> {acc.render_field.(field_str, true), acc}
      _ -> {acc.render_field.(field_str, false), acc}
    end
  end

  # -- Comparison operators --

  defp do_compile({op, _meta, [left, right]}, bindings, acc) when op in @comparison_ops do
    {l, acc} = do_compile(left, bindings, acc)
    {r, acc} = do_compile(right, bindings, acc)

    tla_op =
      case op do
        :> -> ">"
        :>= -> ">="
        :< -> "<"
        :<= -> "=<"
        :== -> "="
        :!= -> "/="
      end

    {"#{l} #{tla_op} #{r}", acc}
  end

  # -- Arithmetic operators --

  defp do_compile({op, _meta, [left, right]}, bindings, acc) when op in @arithmetic_ops do
    {l, acc} = do_compile(left, bindings, acc)
    {r, acc} = do_compile(right, bindings, acc)
    tla_op = Atom.to_string(op)
    {"(#{l} #{tla_op} #{r})", acc}
  end

  # -- Unary minus and plus: `-x`, `-2` --

  defp do_compile({:-, _meta, [arg]}, bindings, acc) do
    {a, acc} = do_compile(arg, bindings, acc)
    {"-(#{a})", acc}
  end

  defp do_compile({:+, _meta, [arg]}, bindings, acc), do: do_compile(arg, bindings, acc)

  # -- Boolean operators --

  defp do_compile({:and, _meta, [left, right]}, bindings, acc) do
    {l, acc} = do_compile(left, bindings, acc)
    {r, acc} = do_compile(right, bindings, acc)
    {"(#{l} /\\ #{r})", acc}
  end

  defp do_compile({:or, _meta, [left, right]}, bindings, acc) do
    {l, acc} = do_compile(left, bindings, acc)
    {r, acc} = do_compile(right, bindings, acc)
    {"(#{l} \\/ #{r})", acc}
  end

  defp do_compile({:not, _meta, [expr]}, bindings, acc) do
    {e, acc} = do_compile(expr, bindings, acc)
    {"~#{e}", acc}
  end

  # -- Built-in functions --

  defp do_compile({:length, _meta, [arg]}, bindings, acc) do
    # When the argument is a list-length-abstracted variable, emit the
    # length variable directly instead of wrapping in Len().
    case arg do
      {var, _, ctx} when is_atom(var) and is_atom(ctx) ->
        case Map.get(bindings, var) do
          {:list_length, tla_name} -> {tla_name, acc}
          _ -> compile_len(arg, bindings, acc)
        end

      _ ->
        compile_len(arg, bindings, acc)
    end
  end

  defp do_compile({:is_integer, _meta, [arg]}, bindings, acc) do
    {a, acc} = do_compile(arg, bindings, acc)
    {"#{a} \\in Int", acc}
  end

  defp do_compile({:is_boolean, _meta, [arg]}, bindings, acc) do
    {a, acc} = do_compile(arg, bindings, acc)
    {"#{a} \\in BOOLEAN", acc}
  end

  defp do_compile({:abs, _meta, [arg]}, bindings, acc) do
    {a, acc} = do_compile(arg, bindings, acc)
    # TLA+ doesn't have a built-in abs, but TLC supports JavaModule.
    # Use IF-THEN-ELSE for portability.
    {"IF #{a} >= 0 THEN #{a} ELSE -(#{a})", acc}
  end

  # Elixir's `div/2` and `rem/2` round toward zero: `div(-1, 2) == 0` and
  # `rem(-1, 2) == -1`. TLA+ `\\div` and `%` round down: `-1 \\div 2 = -1`
  # and `-1 % 2 = 1`. Both are computed on the absolute values, and the
  # sign is set as Elixir sets it.
  defp do_compile({:div, _meta, [left, right]}, bindings, acc) do
    {l, acc} = do_compile(left, bindings, acc)
    {r, acc} = do_compile(right, bindings, acc)
    q = "(#{tla_abs(l)} \\div #{tla_abs(r)})"

    if r =~ ~r/^\d+$/,
      do: {"(IF #{l} >= 0 THEN #{q} ELSE -#{q})", acc},
      else: {"(IF (#{l} >= 0) = (#{r} >= 0) THEN #{q} ELSE -#{q})", acc}
  end

  defp do_compile({:rem, _meta, [left, right]}, bindings, acc) do
    {l, acc} = do_compile(left, bindings, acc)
    {r, acc} = do_compile(right, bindings, acc)
    m = "(#{tla_abs(l)} % #{tla_abs(r)})"
    {"(IF #{l} >= 0 THEN #{m} ELSE -#{m})", acc}
  end

  # -- fn expressions (extract body) --
  # Guards/invariants stored as `fn args -> body end`. We compile the body.

  defp do_compile({:fn, _meta, [{:->, _meta2, [_args, body]}]}, bindings, acc) do
    do_compile(body, bindings, acc)
  end

  # -- Block (compile last expression) --

  defp do_compile({:__block__, _meta, exprs}, bindings, acc) do
    do_compile(List.last(exprs), bindings, acc)
  end

  # -- Unsupported form --

  defp do_compile(ast, _bindings, acc) do
    {"TRUE", add_unsupported(acc, ast)}
  end

  defp tla_abs(expr) do
    if expr =~ ~r/^\d+$/,
      do: expr,
      else: "(IF #{expr} >= 0 THEN #{expr} ELSE -(#{expr}))"
  end

  defp compile_len(arg, bindings, acc) do
    {a, acc} = do_compile(arg, bindings, acc)
    {"Len(#{a})", acc}
  end
end
