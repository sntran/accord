defmodule Accord.TLA.Checker.Parser do
  @moduledoc """
  Parses TLA+ tokens into a syntax tree.

  The parser is a recursive-descent parser with precedence climbing for
  the infix operators. It uses the precedence table of the TLA+ book
  (Lamport, *Specifying Systems*, table 6). A valid module has no
  precedence conflicts, so the parser uses the low end of each
  precedence range.

  ## Junction lists

  A bulleted list of `/\\` or `\\/` items depends on the columns:

      Init == /\\ x = 0
              /\\ y \\in {1, 2}

  The first bullet sets the column of the list. An item ends at the first
  token at that column or to the left of it. A bullet of the same kind at
  that column starts the next item; any other token ends the list. Inside
  parentheses, brackets, and braces, the columns do not matter: the
  closing delimiter ends the item.

  ## Syntax tree

  Expressions are tuples. The first element is the kind:

  - `{:num, n}`, `{:str, s}`, `{:dec, text}`
  - `{:name, name, pos}` — an identifier
  - `{:app, name, args, pos}` — an operator application, also for the
    built-in infix and prefix operators (`"+"`, `"\\\\in"`, `"-."` for
    unary minus)
  - `{:inst, path, name, args, pos}` — `M!Op(args)`; `path` is a list of
    `{instance_name, args}`
  - `{:and, items}`, `{:or, items}`, `{:not, e}`, `{:implies, a, b}`,
    `{:equiv, a, b}`
  - `{:prime, e}`, `{:unchanged, e}`, `{:enabled, e}`
  - `{:always, e}`, `{:eventually, e}`, `{:leadsto, a, b}`,
    `{:box_action, a, sub}`, `{:diamond_action, a, sub}`,
    `{:wf, sub, a}`, `{:sf, sub, a}`
  - `{:if, c, t, e}`, `{:case, arms, other}`, `{:let, defs, body}`
  - `{:forall, binds, body}`, `{:exists, binds, body}`,
    `{:choose, bind, body}`; a bind is `{target, set | nil}`, where the
    target is a name or `{:tuple, names}`
  - `{:set, elems}`, `{:set_map, e, binds}`, `{:set_filter, bind, pred}`
  - `{:tuple, elems}`, `{:func, binds, body}`, `{:apply, f, args}`,
    `{:dot, e, field}`, `{:record, fields}`, `{:record_set, fields}`,
    `{:fun_set, domain, range}`, `{:times, sets}`,
    `{:except, f, updates}` (an update is `{path, value}`; a path step is
    `{:index, args}` or `{:field, name}`), `{:at}`
  - `{:lambda, params, body}`, `{:label, name, e}`, `{:op_arg, name}`

  A definition is a map with `:kind` `:op`, `:fun`, or `:instance`.
  """

  alias Accord.TLA.Checker.Lexer

  defmodule Error do
    @moduledoc "A parse error, with its position."
    defexception [:message, :line, :column, :file]

    @impl true
    def message(%{message: m, line: l, column: c, file: f}) do
      where = if f, do: "#{f}:", else: ""
      "#{where}#{l}:#{c}: #{m}"
    end
  end

  defmodule Module do
    @moduledoc """
    A parsed TLA+ module.

    `units` keeps the definitions, instances, and declarations in order.
    """
    defstruct [
      :name,
      :file,
      extends: [],
      constants: [],
      variables: [],
      units: [],
      assumes: [],
      submodules: [],
      recursive: [],
      # For a module inside another module: the name of the outer module.
      outer: nil
    ]
  end

  @infix %{
    "=>" => {1, :right},
    "<=>" => {2, :none},
    "~>" => {2, :none},
    "-+->" => {2, :none},
    "/\\" => {3, :and},
    "\\/" => {3, :or},
    "=" => {5, :none},
    "/=" => {5, :none},
    "<" => {5, :none},
    ">" => {5, :none},
    "<=" => {5, :none},
    ">=" => {5, :none},
    "\\in" => {5, :none},
    "\\notin" => {5, :none},
    "\\subseteq" => {5, :none},
    "\\subset" => {5, :none},
    "\\supseteq" => {5, :none},
    "\\supset" => {5, :none},
    "\\prec" => {5, :none},
    "\\succ" => {5, :none},
    "\\preceq" => {5, :none},
    "\\succeq" => {5, :none},
    "\\sqsubset" => {5, :none},
    "\\sqsupset" => {5, :none},
    "\\sqsubseteq" => {5, :none},
    "\\sqsupseteq" => {5, :none},
    "\\ll" => {5, :none},
    "\\gg" => {5, :none},
    "\\sim" => {5, :none},
    "\\simeq" => {5, :none},
    "\\asymp" => {5, :none},
    "\\approx" => {5, :none},
    "\\cong" => {5, :none},
    "\\doteq" => {5, :none},
    "\\propto" => {5, :none},
    "|-" => {5, :none},
    "-|" => {5, :none},
    "|=" => {5, :none},
    "=|" => {5, :none},
    ":=" => {5, :none},
    "::=" => {5, :none},
    "\\cdot" => {5, :left},
    "@@" => {6, :left},
    ":>" => {7, :none},
    "<:" => {7, :none},
    "\\cup" => {8, :left},
    "\\cap" => {8, :left},
    "\\" => {8, :none},
    ".." => {9, :none},
    "..." => {9, :none},
    "!!" => {9, :none},
    "??" => {9, :left},
    "$" => {9, :left},
    "$$" => {9, :left},
    "\\uplus" => {9, :left},
    "\\sqcap" => {9, :left},
    "\\sqcup" => {9, :left},
    "\\wr" => {9, :none},
    "+" => {10, :left},
    "++" => {10, :left},
    "(+)" => {10, :left},
    "%" => {10, :none},
    "%%" => {10, :left},
    "|" => {10, :left},
    "||" => {10, :left},
    "\\X" => {10, :times},
    "-" => {11, :left},
    "--" => {11, :left},
    "(-)" => {11, :left},
    "*" => {13, :left},
    "**" => {13, :left},
    "/" => {13, :none},
    "//" => {13, :none},
    "\\div" => {13, :none},
    "\\o" => {13, :left},
    "&" => {13, :left},
    "&&" => {13, :left},
    "(.)" => {13, :left},
    "(/)" => {13, :none},
    "(\\X)" => {13, :left},
    "\\star" => {13, :left},
    "\\bullet" => {13, :left},
    "\\bigcirc" => {13, :left},
    "^" => {14, :none},
    "^^" => {14, :none}
  }

  @postfix ["'", "^+", "^*", "^#"]

  @unit_keywords ~w(THEOREM LEMMA PROPOSITION COROLLARY AXIOM ASSUME ASSUMPTION CONSTANT
    CONSTANTS VARIABLE VARIABLES EXTENDS INSTANCE LOCAL RECURSIVE USE HIDE)

  @eof {:eof, nil, 0, 0}

  defstruct toks: {}, pos: 0, n: 0, limits: [], file: nil

  @doc "The infix operator table: name to `{precedence, associativity}`."
  @spec infix_ops() :: map()
  def infix_ops, do: @infix

  # -- Entry points --

  @doc """
  Parses the source of a module file. Gives the outermost module.
  Raises `Accord.TLA.Checker.Parser.Error`.
  """
  @spec parse_module(String.t(), keyword()) :: %Module{}
  def parse_module(source, opts \\ []) do
    file = Keyword.get(opts, :file)

    tokens =
      try do
        Lexer.tokenize(source)
      rescue
        e in Lexer.Error ->
          raise Error, message: e.message, line: e.line, column: e.column, file: file
      end

    p = %__MODULE__{toks: List.to_tuple(tokens), n: length(tokens), file: file}
    {mod, p} = module(p)
    # More top-level modules in the file: they are available as
    # submodules of the first one.
    {extra, _p} = more_modules(p, [])
    %{mod | file: file, submodules: mod.submodules ++ extra}
  end

  defp more_modules(p, acc) do
    case raw(p) do
      {:module_start, _, _, _} ->
        {m, p} = module(p)
        more_modules(p, [m | acc])

      _ ->
        {Enum.reverse(acc), p}
    end
  end

  @doc """
  Parses one expression (for tests, and for values in config files).
  """
  @spec parse_expression(String.t()) :: tuple()
  def parse_expression(source) do
    tokens = Lexer.tokenize("---- MODULE E ----\n" <> source <> "\n====")
    tokens = tokens |> Enum.drop(1) |> Enum.drop(-1)
    p = %__MODULE__{toks: List.to_tuple(tokens), n: length(tokens)}
    {e, p} = expr(p, 0)

    case peek(p) do
      @eof -> e
      t -> error(p, t, "unexpected #{describe(t)} after the expression")
    end
  end

  # -- Token access --

  defp raw(%{pos: pos, n: n}) when pos >= n, do: @eof
  defp raw(%{toks: toks, pos: pos}), do: elem(toks, pos)

  defp raw_at(%{n: n}, i) when i >= n, do: @eof
  defp raw_at(%{toks: toks}, i), do: elem(toks, i)

  # The next token, or :offside when it is at or to the left of the
  # column of the innermost junction list.
  defp peek(p) do
    t = raw(p)

    case p.limits do
      [c | _] when is_integer(c) ->
        {_, _, line, col} = t
        if t != @eof and col <= c, do: {:offside, nil, line, col}, else: t

      _ ->
        t
    end
  end

  defp advance(p), do: %{p | pos: p.pos + 1}

  defp push_limit(p, limit), do: %{p | limits: [limit | p.limits]}
  defp pop_limit(%{limits: [_ | rest]} = p), do: %{p | limits: rest}

  defp expect(p, type, value) do
    case peek(p) do
      {^type, ^value, _, _} -> advance(p)
      t -> error(p, t, "expected #{inspect(value)}, found #{describe(t)}")
    end
  end

  defp expect_op(p, value), do: expect(p, :op, value)

  defp expect_id(p) do
    case peek(p) do
      {:id, name, _, _} -> {name, advance(p)}
      t -> error(p, t, "expected a name, found #{describe(t)}")
    end
  end

  defp at?(p, type, value) do
    case peek(p) do
      {^type, ^value, _, _} -> true
      _ -> false
    end
  end

  defp op?(p, value), do: at?(p, :op, value)

  defp pos({_, _, line, col}), do: {line, col}

  defp describe({:eof, _, _, _}), do: "the end of the module"
  defp describe({:offside, _, _, _}), do: "a token to the left of the junction list"
  defp describe({:module_end, _, _, _}), do: "the end of the module"
  defp describe({type, value, _, _}), do: "#{type} #{inspect(value)}"

  defp error(p, {_, _, line, col}, message),
    do: raise(Error, message: message, line: line, column: col, file: p.file)

  # -- Modules --

  defp module(p) do
    {name, p} =
      case raw(p) do
        {:module_start, name, _, _} -> {name, advance(p)}
        t -> error(p, t, "expected a module header")
      end

    units(p, %Module{name: name}, false)
  end

  defp units(p, mod, local?) do
    case raw(p) do
      {:module_end, _, _, _} ->
        {finish(mod), advance(p)}

      {:eof, _, _, _} ->
        {finish(mod), p}

      {:separator, _, _, _} ->
        units(advance(p), mod, false)

      {:module_start, _, _, _} ->
        {sub, p} = module(p)
        units(p, %{mod | submodules: [%{sub | outer: mod.name} | mod.submodules]}, false)

      {:kw, "EXTENDS", _, _} ->
        {names, p} = name_list(advance(p))
        units(p, %{mod | extends: mod.extends ++ names}, false)

      {:kw, kw, _, _} when kw in ["CONSTANT", "CONSTANTS"] ->
        {decls, p} = constant_decls(advance(p))
        units(p, %{mod | constants: mod.constants ++ decls}, false)

      {:kw, kw, _, _} when kw in ["VARIABLE", "VARIABLES"] ->
        {names, p} = name_list(advance(p))
        units(p, %{mod | variables: mod.variables ++ names}, false)

      {:kw, kw, _, _} = t when kw in ["ASSUME", "ASSUMPTION", "AXIOM"] ->
        case assumption(advance(p)) do
          {:skip, p} ->
            units(p, mod, false)

          {name, e, p} ->
            mod = %{mod | assumes: mod.assumes ++ [{e, pos(t)}]}
            mod = if name, do: %{mod | units: [named_unit(name, e, t) | mod.units]}, else: mod
            units(p, mod, false)
        end

      {:kw, kw, _, _} = t when kw in ["THEOREM", "LEMMA", "PROPOSITION", "COROLLARY"] ->
        case named_theorem(p) do
          {name, e, p2} -> units(p2, %{mod | units: [named_unit(name, e, t) | mod.units]}, false)
          nil -> units(skip_unit(p), mod, false)
        end

      {:kw, kw, _, _} when kw in ["USE", "HIDE"] ->
        units(skip_unit(p), mod, false)

      {:kw, "PROOF", _, _} ->
        units(skip_unit(p), mod, false)

      {:kw, "LOCAL", _, _} ->
        units(advance(p), mod, true)

      {:kw, "RECURSIVE", _, _} ->
        {decls, p} = constant_decls(advance(p))
        units(p, %{mod | recursive: mod.recursive ++ decls}, false)

      {:kw, "INSTANCE", _, _} ->
        {inst, p} = instance(advance(p), nil, [], local?)
        units(p, %{mod | units: [inst | mod.units]}, false)

      _ ->
        if proof_start?(p) do
          units(skip_unit(p), mod, false)
        else
          {def, p} = definition(p, local?)
          units(p, %{mod | units: [def | mod.units]}, false)
        end
    end
  end

  defp finish(mod) do
    %{mod | units: Enum.reverse(mod.units), submodules: Enum.reverse(mod.submodules)}
  end

  # A proof step at the top level: `<1>1.`, `<2> QED`.
  defp proof_start?(p) do
    case {raw(p), raw_at(p, p.pos + 1), raw_at(p, p.pos + 2)} do
      {{:op, "<", _, _}, {:num, _, _, _}, {:op, ">", _, _}} -> true
      {{:op, "<", _, _}, {:op, "*", _, _}, {:op, ">", _, _}} -> true
      {{:op, "<", _, _}, {:op, "+", _, _}, {:op, ">", _, _}} -> true
      {{:kw, kw, _, _}, _, _} when kw in ["BY", "OBVIOUS", "OMITTED", "QED"] -> true
      _ -> false
    end
  end

  defp name_list(p) do
    {name, p} = expect_id(p)

    if op?(p, ","),
      do: (fn {names, p} -> {[name | names], p} end).(name_list(advance(p))),
      else: {[name], p}
  end

  # `N, Proc, F(_, _), _ + _`.
  defp constant_decls(p) do
    {decl, p} =
      case peek(p) do
        {:id, name, _, _} ->
          p = advance(p)

          if op?(p, "(") do
            {arity, p} = underscores(advance(p), 0)
            {{name, arity}, p}
          else
            {{name, 0}, p}
          end

        {:op, "_", _, _} ->
          # Infix or postfix constant operator: `_ + _`, `_ ^+`.
          case {raw_at(p, p.pos + 1), raw_at(p, p.pos + 2)} do
            {{:op, op, _, _}, {:op, "_", _, _}} -> {{op, 2}, %{p | pos: p.pos + 3}}
            {{:op, op, _, _}, _} -> {{op, 1}, %{p | pos: p.pos + 2}}
          end

        {:op, op, _, _} ->
          {{op, 1}, p |> advance() |> expect_op("_")}

        t ->
          error(p, t, "expected a constant declaration, found #{describe(t)}")
      end

    if op?(p, ",") do
      {rest, p} = constant_decls(advance(p))
      {[decl | rest], p}
    else
      {[decl], p}
    end
  end

  defp underscores(p, n) do
    p = expect_op(p, "_")

    cond do
      op?(p, ",") -> underscores(advance(p), n + 1)
      op?(p, ")") -> {n + 1, advance(p)}
      true -> error(p, peek(p), "expected `,` or `)` in an operator declaration")
    end
  end

  defp assumption(p) do
    # `ASSUME Name == expr`, `ASSUME expr`, or the ASSUME of a theorem
    # (`ASSUME NEW x PROVE ...`), which is skipped. A name defines an
    # operator with the expression as its body.
    {name, p} =
      case {raw(p), raw_at(p, p.pos + 1)} do
        {{:id, name, _, _}, {:op, "==", _, _}} -> {name, %{p | pos: p.pos + 2}}
        _ -> {nil, p}
      end

    case raw(p) do
      {:kw, kw, _, _} when kw in ["NEW", "CONSTANT", "VARIABLE", "STATE", "ACTION", "TEMPORAL"] ->
        {:skip, skip_unit(p)}

      _ ->
        {e, p} = expr(p, 0)

        if at?(p, :kw, "PROVE") or op?(p, ","), do: {:skip, skip_unit(p)}, else: {name, e, p}
    end
  end

  # `THEOREM Name == expr` defines an operator. A theorem without a name,
  # or with the form `ASSUME ... PROVE ...`, gives nil.
  defp named_theorem(p) do
    with {:id, name, _, _} <- raw_at(p, p.pos + 1),
         {:op, "==", _, _} <- raw_at(p, p.pos + 2),
         p2 = %{p | pos: p.pos + 3},
         false <- match?({:kw, k, _, _} when k in ["ASSUME", "NEW"], raw(p2)) do
      # The statement ends where the proof starts; the unit ends where
      # `skip_unit/1` stops.
      stop = skip_unit(p).pos
      e_end = Enum.find(p2.pos..(stop - 1)//1, stop, &proof_token?(p, &1))

      try do
        {e, p3} = expr(%{p2 | n: e_end}, 0)
        if p3.pos == e_end, do: {name, e, %{p3 | n: p.n, pos: stop}}, else: nil
      rescue
        Error -> nil
      end
    else
      _ -> nil
    end
  end

  defp proof_token?(p, i) do
    {_, _, line, _} = raw_at(p, i)
    {_, _, prev_line, _} = raw_at(p, i - 1)

    prev_line < line and
      case {raw_at(p, i), raw_at(p, i + 1), raw_at(p, i + 2)} do
        {{:op, "<", _, _}, {kind, _, _, _}, {:op, ">", _, _}} when kind in [:num, :op] -> true
        {{:kw, kw, _, _}, _, _} -> kw in ["PROOF", "BY", "OBVIOUS", "OMITTED"]
        _ -> false
      end
  end

  defp named_unit(name, e, t),
    do: %{kind: :op, name: name, params: [], body: e, local: false, pos: pos(t)}

  # Skips a theorem, a proof, or a USE/HIDE: to the next token that is
  # first on its line and starts a module unit.
  #
  # Inside the skipped text, definitions between LET and IN, and after a
  # proof DEFINE (to the next step), belong to the theorem or proof.
  defp skip_unit(p), do: %{p | pos: next_unit(p, p.pos + 1, 0, false)}

  defp next_unit(p, i, lets, define?) do
    t = raw_at(p, i)

    cond do
      t == @eof ->
        i

      match?({:kw, "LET", _, _}, t) ->
        next_unit(p, i + 1, lets + 1, define?)

      match?({:kw, "IN", _, _}, t) ->
        next_unit(p, i + 1, max(lets - 1, 0), define?)

      match?({:kw, "DEFINE", _, _}, t) ->
        next_unit(p, i + 1, lets, true)

      step_label?(p, i) ->
        next_unit(p, i + 1, lets, false)

      lets == 0 and not define? and unit_start?(p, i, t) ->
        i

      match?({type, _, _, _} when type in [:module_end, :module_start, :separator], t) ->
        i

      true ->
        next_unit(p, i + 1, lets, define?)
    end
  end

  defp step_label?(p, i) do
    match?(
      {{:op, "<", _, _}, {type, _, _, _}, {:op, ">", _, _}} when type in [:num, :op],
      {raw_at(p, i), raw_at(p, i + 1), raw_at(p, i + 2)}
    )
  end

  defp unit_start?(p, i, {type, value, line, _col}) do
    {_, _, prev_line, _} = raw_at(p, i - 1)
    first_on_line = prev_line < line

    case type do
      :module_end ->
        true

      :module_start ->
        true

      :separator ->
        true

      :kw when first_on_line and value in ["ASSUME", "ASSUMPTION"] ->
        # `LEMMA Name ==` and `THEOREM` can start with ASSUME on the next line.
        not match?({:kw, kw, _, _} when kw in ["NEW", "CONSTANT", "VARIABLE"], raw_at(p, i + 1)) and
          not theorem_head?(p, i - 1)

      :kw when first_on_line ->
        value in @unit_keywords

      :id when first_on_line ->
        definition_start?(p, i)

      _ ->
        false
    end
  end

  defp theorem_head?(p, i) do
    case raw_at(p, i) do
      {:kw, kw, _, _} when kw in ["THEOREM", "LEMMA", "PROPOSITION", "COROLLARY"] -> true
      {:op, "==", _, _} -> theorem_head?(p, i - 2)
      {:id, _, _, _} -> theorem_head?(p, i - 1)
      _ -> false
    end
  end

  # `Name ==`, `Name(...) ==`, `Name[...] ==`, `a op b ==`, `a op ==`.
  defp definition_start?(p, i) do
    case raw_at(p, i + 1) do
      {:op, "==", _, _} ->
        true

      {:op, "(", _, _} ->
        after_group(p, i + 1, "(", ")")

      {:op, "[", _, _} ->
        after_group(p, i + 1, "[", "]")

      {:op, _, _, _} ->
        match?({:op, "==", _, _}, raw_at(p, i + 3)) or match?({:op, "==", _, _}, raw_at(p, i + 2))

      _ ->
        false
    end
  end

  defp after_group(p, i, open, close), do: group_end(p, i + 1, open, close, 1)

  defp group_end(p, i, open, close, depth) do
    case raw_at(p, i) do
      @eof -> false
      {:op, ^close, _, _} when depth == 1 -> match?({:op, "==", _, _}, raw_at(p, i + 1))
      {:op, ^close, _, _} -> group_end(p, i + 1, open, close, depth - 1)
      {:op, ^open, _, _} -> group_end(p, i + 1, open, close, depth + 1)
      {:module_end, _, _, _} -> false
      _ -> group_end(p, i + 1, open, close, depth)
    end
  end

  # -- Definitions --

  defp definition(p, local?) do
    t = peek(p)
    pos = pos(t)

    case {t, raw_at(p, p.pos + 1), raw_at(p, p.pos + 2), raw_at(p, p.pos + 3)} do
      {{:id, name, _, _}, {:op, "==", _, _}, _, _} ->
        p = %{p | pos: p.pos + 2}

        if at?(p, :kw, "INSTANCE") do
          instance(advance(p), name, [], local?)
        else
          {body, p} = expr(p, 0)
          {%{kind: :op, name: name, params: [], body: body, local: local?, pos: pos}, p}
        end

      {{:id, name, _, _}, {:op, "(", _, _}, _, _} ->
        {params, p} = params(%{p | pos: p.pos + 2}, [])
        p = expect_op(p, "==")

        if at?(p, :kw, "INSTANCE") do
          instance(advance(p), name, params, local?)
        else
          {body, p} = expr(p, 0)
          {%{kind: :op, name: name, params: params, body: body, local: local?, pos: pos}, p}
        end

      {{:id, name, _, _}, {:op, "[", _, _}, _, _} ->
        {binds, p} = binders(%{p | pos: p.pos + 2}, true)
        p = p |> expect_op("]") |> expect_op("==")
        {body, p} = expr(p, 0)
        {%{kind: :fun, name: name, binds: binds, body: body, local: local?, pos: pos}, p}

      {{:id, a, _, _}, {:op, op, _, _}, {:id, b, _, _}, {:op, "==", _, _}} ->
        p = %{p | pos: p.pos + 4}
        {body, p} = expr(p, 0)
        {%{kind: :op, name: op, params: [{a, 0}, {b, 0}], body: body, local: local?, pos: pos}, p}

      {{:id, a, _, _}, {:op, op, _, _}, {:op, "==", _, _}, _} when op in @postfix ->
        p = %{p | pos: p.pos + 3}
        {body, p} = expr(p, 0)
        {%{kind: :op, name: op, params: [{a, 0}], body: body, local: local?, pos: pos}, p}

      {{:op, "-", _, _}, {:op, ".", _, _}, {:id, a, _, _}, {:op, "==", _, _}} ->
        p = %{p | pos: p.pos + 4}
        {body, p} = expr(p, 0)
        {%{kind: :op, name: "-.", params: [{a, 0}], body: body, local: local?, pos: pos}, p}

      {{:op, op, _, _}, {:id, a, _, _}, {:op, "==", _, _}, _} ->
        name = if op == "-", do: "-.", else: op
        p = %{p | pos: p.pos + 3}
        {body, p} = expr(p, 0)
        {%{kind: :op, name: name, params: [{a, 0}], body: body, local: local?, pos: pos}, p}

      _ ->
        error(p, t, "expected a definition, found #{describe(t)}")
    end
  end

  # Operator parameters: `x`, `F(_, _)`, `_ + _`, `-. _`.
  defp params(p, acc) do
    {param, p} =
      case {peek(p), raw_at(p, p.pos + 1), raw_at(p, p.pos + 2)} do
        {{:id, name, _, _}, {:op, "(", _, _}, _} ->
          {arity, p} = underscores(%{p | pos: p.pos + 2}, 0)
          {{name, arity}, p}

        {{:id, name, _, _}, _, _} ->
          {{name, 0}, advance(p)}

        {{:op, "_", _, _}, {:op, op, _, _}, {:op, "_", _, _}} ->
          {{op, 2}, %{p | pos: p.pos + 3}}

        {{:op, op, _, _}, {:op, "_", _, _}, _} ->
          {{op, 1}, %{p | pos: p.pos + 2}}

        {t, _, _} ->
          error(p, t, "expected a parameter, found #{describe(t)}")
      end

    acc = [param | acc]

    cond do
      op?(p, ",") -> params(advance(p), acc)
      op?(p, ")") -> {Enum.reverse(acc), advance(p)}
      true -> error(p, peek(p), "expected `,` or `)` after a parameter")
    end
  end

  # `INSTANCE M WITH a <- e, b <- f`.
  defp instance(p, name, params, local?) do
    t = peek(p)
    {module, p} = expect_id(p)

    {subs, p} =
      if at?(p, :kw, "WITH"), do: substitutions(advance(p), []), else: {[], p}

    {%{
       kind: :instance,
       name: name,
       params: params,
       module: module,
       subs: subs,
       local: local?,
       pos: pos(t)
     }, p}
  end

  defp substitutions(p, acc) do
    {target, p} =
      case peek(p) do
        {:id, n, _, _} -> {n, advance(p)}
        {:op, op, _, _} -> {op, advance(p)}
        t -> error(p, t, "expected a name to substitute")
      end

    p = expect_op(p, "<-")

    {value, p} =
      case {peek(p), raw_at(p, p.pos + 1)} do
        {{:op, op, _, _}, next}
        when op != "(" and op != "{" and op != "[" and op != "<<" and
               op != "-" and op != "~" ->
          case next do
            {:op, sep, _, _} when sep in [",", ")"] -> {{:op_arg, op}, advance(p)}
            {:module_end, _, _, _} -> {{:op_arg, op}, advance(p)}
            {:kw, _, _, _} -> {{:op_arg, op}, advance(p)}
            _ -> expr(p, 0)
          end

        _ ->
          expr(p, 0)
      end

    acc = [{target, value} | acc]
    if op?(p, ","), do: substitutions(advance(p), acc), else: {Enum.reverse(acc), p}
  end

  # LET definitions, to IN.
  defp let_defs(p, acc) do
    case peek(p) do
      {:kw, "IN", _, _} ->
        {Enum.reverse(acc), advance(p)}

      {:kw, "RECURSIVE", _, _} ->
        {_decls, p} = constant_decls(advance(p))
        let_defs(p, acc)

      _ ->
        {def, p} = definition(p, false)
        let_defs(p, [def | acc])
    end
  end

  # -- Expressions --

  defp expr(p, min) do
    {left, p} = unary(p)
    infix_loop(p, left, min)
  end

  defp infix_loop(p, left, min) do
    # `-. a == ...` starts the definition of unary minus.
    next =
      case {peek(p), raw_at(p, p.pos + 1)} do
        {{:op, "-", _, _}, {:op, ".", _, _}} -> :stop
        {t, _} -> t
      end

    case next do
      {:op, op, _, _} = t ->
        case Map.fetch(@infix, op) do
          {:ok, {prec, assoc}} when prec >= min ->
            p = advance(p)

            case assoc do
              :times ->
                {right, p} = expr(p, prec + 1)
                {sets, p} = more_times(p, [right, left], prec)
                infix_loop(p, {:times, Enum.reverse(sets)}, min)

              :right ->
                {right, p} = expr(p, prec)
                infix_loop(p, binary(op, left, right, t), min)

              _ ->
                {right, p} = expr(p, prec + 1)
                infix_loop(p, binary(op, left, right, t), min)
            end

          _ ->
            {left, p}
        end

      _ ->
        {left, p}
    end
  end

  defp more_times(p, acc, prec) do
    if op?(p, "\\X") do
      {right, p} = expr(advance(p), prec + 1)
      more_times(p, [right | acc], prec)
    else
      {acc, p}
    end
  end

  defp binary("/\\", {:and, items}, right, _t), do: {:and, items ++ [right]}
  defp binary("/\\", left, right, _t), do: {:and, [left, right]}
  defp binary("\\/", {:or, items}, right, _t), do: {:or, items ++ [right]}
  defp binary("\\/", left, right, _t), do: {:or, [left, right]}
  defp binary("=>", left, right, _t), do: {:implies, left, right}
  defp binary("<=>", left, right, _t), do: {:equiv, left, right}
  defp binary("~>", left, right, _t), do: {:leadsto, left, right}
  defp binary(op, left, right, t), do: {:app, op, [left, right], pos(t)}

  # Prefix operators and primaries, then postfix operators.
  defp unary(p) do
    t = peek(p)

    case t do
      {:op, "~", _, _} ->
        {e, p} = expr(advance(p), 5)
        postfix(p, {:not, e})

      {:op, "-", _, _} ->
        {e, p} = expr(advance(p), 13)
        {{:app, "-.", [e], pos(t)}, p}

      {:op, "[]", _, _} ->
        {e, p} = expr(advance(p), 5)
        {{:always, e}, p}

      {:op, "<>", _, _} ->
        {e, p} = expr(advance(p), 5)
        {{:eventually, e}, p}

      {:kw, "ENABLED", _, _} ->
        {e, p} = expr(advance(p), 5)
        {{:enabled, e}, p}

      {:kw, "UNCHANGED", _, _} ->
        {e, p} = expr(advance(p), 5)
        {{:unchanged, e}, p}

      {:kw, "SUBSET", _, _} ->
        {e, p} = expr(advance(p), 9)
        {{:app, "SUBSET", [e], pos(t)}, p}

      {:kw, "UNION", _, _} ->
        {e, p} = expr(advance(p), 9)
        {{:app, "UNION", [e], pos(t)}, p}

      {:kw, "DOMAIN", _, _} ->
        {e, p} = expr(advance(p), 10)
        {{:app, "DOMAIN", [e], pos(t)}, p}

      {:op, bullet, _, col} when bullet in ["/\\", "\\/"] ->
        junction(p, bullet, col, [])

      _ ->
        {e, p} = primary(p)
        postfix(p, e)
    end
  end

  defp junction(p, bullet, col, acc) do
    p = p |> advance() |> push_limit(col)
    {item, p} = expr(p, 0)
    p = pop_limit(p)
    acc = [item | acc]

    case peek(p) do
      {:op, ^bullet, _, ^col} ->
        junction(p, bullet, col, acc)

      _ ->
        kind = if bullet == "/\\", do: :and, else: :or
        {{kind, Enum.reverse(acc)}, p}
    end
  end

  defp postfix(p, e) do
    case peek(p) do
      {:op, "'", _, _} ->
        postfix(advance(p), {:prime, e})

      {:op, op, _, _} = t when op in ["^+", "^*", "^#"] ->
        postfix(advance(p), {:app, op, [e], pos(t)})

      {:op, "[", _, _} ->
        p = p |> advance() |> push_limit(:none)
        {args, p} = expr_list(p, "]")
        p = pop_limit(p)
        postfix(p, {:apply, e, args})

      {:op, ".", _, _} ->
        case raw_at(p, p.pos + 1) do
          {:id, field, _, _} -> postfix(%{p | pos: p.pos + 2}, {:dot, e, field})
          {:kw, field, _, _} -> postfix(%{p | pos: p.pos + 2}, {:dot, e, field})
          {:num, n, _, _} -> postfix(%{p | pos: p.pos + 2}, {:dot, e, Integer.to_string(n)})
          _ -> {e, p}
        end

      _ ->
        {e, p}
    end
  end

  # Expressions separated by commas, to the closing token.
  defp expr_list(p, close) do
    {e, p} = expr(p, 0)

    cond do
      op?(p, ",") ->
        {rest, p} = expr_list(advance(p), close)
        {[e | rest], p}

      op?(p, close) ->
        {[e], advance(p)}

      true ->
        error(p, peek(p), "expected `,` or `#{close}`, found #{describe(peek(p))}")
    end
  end

  defp primary(p) do
    t = peek(p)

    case t do
      {:num, n, _, _} ->
        {{:num, n}, advance(p)}

      {:dec, d, _, _} ->
        {{:dec, d}, advance(p)}

      {:str, s, _, _} ->
        {{:str, s}, advance(p)}

      {:id, name, _, _} ->
        name_expr(advance(p), name, t)

      {:op, "(", _, _} ->
        p = p |> advance() |> push_limit(:none)
        {e, p} = expr(p, 0)
        p = p |> expect_op(")") |> pop_limit()
        {e, p}

      {:op, "{", _, _} ->
        braces(advance(p))

      {:op, "[", _, _} ->
        brackets(advance(p))

      {:op, "<<", _, _} ->
        angles(advance(p))

      {:op, "@", _, _} ->
        {{:at}, advance(p)}

      {:op, q, _, _} when q in ["\\A", "\\E"] ->
        {binds, p} = binders(advance(p), false)
        p = expect_op(p, ":")
        {body, p} = expr(p, 0)
        {{if(q == "\\A", do: :forall, else: :exists), binds, body}, p}

      {:op, q, _, _} when q in ["\\AA", "\\EE"] ->
        {names, p} = name_list(advance(p))
        p = expect_op(p, ":")
        {body, p} = expr(p, 0)
        {{if(q == "\\AA", do: :temporal_forall, else: :temporal_exists), names, body}, p}

      {:kw, "CHOOSE", _, _} ->
        {[bind], p} = binders(advance(p), false, true)
        p = expect_op(p, ":")
        {body, p} = expr(p, 0)
        {{:choose, bind, body}, p}

      {:kw, "IF", _, _} ->
        {c, p} = expr(advance(p), 0)
        p = expect(p, :kw, "THEN")
        {a, p} = expr(p, 0)
        p = expect(p, :kw, "ELSE")
        {b, p} = expr(p, 0)
        {{:if, c, a, b}, p}

      {:kw, "CASE", _, _} ->
        case_arms(advance(p), [])

      {:kw, "LET", _, _} ->
        {defs, p} = let_defs(advance(p), [])
        {body, p} = expr(p, 0)
        {{:let, defs, body}, p}

      {:kw, "LAMBDA", _, _} ->
        lambda(advance(p))

      {:kw, fair, _, _} when fair in ["WF_", "SF_"] ->
        {sub, p} = subscript(advance(p))
        p = p |> expect_op("(") |> push_limit(:none)
        {a, p} = expr(p, 0)
        p = p |> expect_op(")") |> pop_limit()
        {{if(fair == "WF_", do: :wf, else: :sf), sub, a}, p}

      _ ->
        error(p, t, "unexpected #{describe(t)}")
    end
  end

  # A name, an operator application, an instance path, or a label.
  defp name_expr(p, name, t) do
    {args, p} =
      if op?(p, "(") do
        p = p |> advance() |> push_limit(:none)
        {args, p} = args(p)
        {args, pop_limit(p)}
      else
        {nil, p}
      end

    cond do
      op?(p, "!") ->
        instance_path(advance(p), [{name, args || []}], t)

      op?(p, "::") ->
        {e, p} = expr(advance(p), 0)
        {{:label, name, e}, p}

      args == nil ->
        {{:name, name, pos(t)}, p}

      true ->
        {{:app, name, args, pos(t)}, p}
    end
  end

  # `M!N!Op(args)`.
  defp instance_path(p, path, t) do
    {name, p} =
      case peek(p) do
        {:id, n, _, _} -> {n, advance(p)}
        {:num, n, _, _} -> {n, advance(p)}
        {:op, op, _, _} -> {op, advance(p)}
        tok -> error(p, tok, "expected a name after `!`")
      end

    {args, p} =
      if op?(p, "(") do
        p = p |> advance() |> push_limit(:none)
        {args, p} = args(p)
        {args, pop_limit(p)}
      else
        {[], p}
      end

    cond do
      op?(p, "!") ->
        instance_path(advance(p), path ++ [{name, args}], t)

      # `Thm!:` is the statement of `Thm`.
      name == ":" ->
        case Enum.split(path, -1) do
          {[], [{n, []}]} -> {{:name, n, pos(t)}, p}
          {[], [{n, a}]} -> {{:app, n, a, pos(t)}, p}
          {outer, [{n, a}]} -> {{:inst, outer, n, a, pos(t)}, p}
        end

      true ->
        {{:inst, path, name, args, pos(t)}, p}
    end
  end

  # Operator arguments: expressions, LAMBDA, or a bare operator symbol.
  defp args(p) do
    {arg, p} =
      case {peek(p), raw_at(p, p.pos + 1)} do
        {{:kw, "LAMBDA", _, _}, _} ->
          lambda(advance(p))

        {{:op, op, _, _}, {:op, sep, _, _}}
        when sep in [",", ")"] and op not in ["(", "{", "[", "<<", "@"] ->
          {{:op_arg, op}, advance(p)}

        _ ->
          expr(p, 0)
      end

    cond do
      op?(p, ",") ->
        {rest, p} = args(advance(p))
        {[arg | rest], p}

      op?(p, ")") ->
        {[arg], advance(p)}

      true ->
        error(p, peek(p), "expected `,` or `)` in the arguments")
    end
  end

  defp lambda(p) do
    {names, p} = name_list(p)
    p = expect_op(p, ":")
    {body, p} = expr(p, 0)
    {{:lambda, names, body}, p}
  end

  defp case_arms(p, acc) do
    case peek(p) do
      {:kw, "OTHER", _, _} ->
        p = p |> advance() |> expect_op("->")
        {e, p} = expr(p, 0)
        {{:case, Enum.reverse(acc), e}, p}

      _ ->
        {c, p} = expr(p, 0)
        p = expect_op(p, "->")
        {e, p} = expr(p, 0)
        acc = [{c, e} | acc]

        if op?(p, "[]"),
          do: case_arms(advance(p), acc),
          else: {{:case, Enum.reverse(acc), nil}, p}
    end
  end

  # The subscript of `[A]_v`, `WF_v(A)`: a name, a tuple, or parentheses.
  defp subscript(p) do
    case peek(p) do
      {:id, name, _, _} = t ->
        p = advance(p)

        if op?(p, "!"),
          do: instance_path(advance(p), [{name, []}], t),
          else: {{:name, name, pos(t)}, p}

      {:op, "<<", _, _} ->
        angles(advance(p))

      {:op, "(", _, _} ->
        p = p |> advance() |> push_limit(:none)
        {e, p} = expr(p, 0)
        {e, p |> expect_op(")") |> pop_limit()}

      t ->
        error(p, t, "expected a subscript, found #{describe(t)}")
    end
  end

  # Bound variables: `x \in S, y, z \in T`, `<<a, b>> \in S`, or `x, y`
  # (unbounded). With `bounded`, every name needs a set.
  defp binders(p, bounded, single \\ false) do
    {targets, p} = bind_targets(p, [])

    {set, p} =
      if op?(p, "\\in") do
        p = advance(p)
        expr(p, 0)
      else
        if bounded, do: error(p, peek(p), "expected `\\in`"), else: {nil, p}
      end

    binds = Enum.map(targets, &{&1, set})

    if not single and op?(p, ",") and binder_follows?(p) do
      {rest, p} = binders(advance(p), bounded)
      {binds ++ rest, p}
    else
      {binds, p}
    end
  end

  defp binder_follows?(p) do
    case raw_at(p, p.pos + 1) do
      {:id, _, _, _} -> true
      {:op, "<<", _, _} -> true
      _ -> false
    end
  end

  defp bind_targets(p, acc) do
    {target, p} =
      case peek(p) do
        {:id, name, _, _} ->
          {name, advance(p)}

        {:op, "<<", _, _} ->
          {names, p} = name_list(advance(p))
          {{:tuple, names}, expect_op(p, ">>")}

        t ->
          error(p, t, "expected a bound variable, found #{describe(t)}")
      end

    acc = [target | acc]

    # `x, y \in S`: a comma followed by another target, with no `\in`
    # between them.
    if op?(p, ",") and not op?(p, "\\in") and binder_follows?(p) and
         next_is_bare_target?(p) do
      bind_targets(advance(p), acc)
    else
      {Enum.reverse(acc), p}
    end
  end

  # After `x,`: is the next item a target in the same group (`x, y \in S`
  # or `x, y :`), not a new binder of its own?
  defp next_is_bare_target?(p) do
    case raw_at(p, p.pos + 1) do
      {:id, _, _, _} ->
        case raw_at(p, p.pos + 2) do
          {:op, sep, _, _} when sep in [",", "\\in", ":"] -> true
          _ -> false
        end

      {:op, "<<", _, _} ->
        true

      _ ->
        false
    end
  end

  defp braces(p) do
    p = push_limit(p, :none)

    if op?(p, "}") do
      {{:set, []}, p |> advance() |> pop_limit()}
    else
      {first, p} = expr(p, 0)

      cond do
        op?(p, "}") ->
          {{:set, [first]}, p |> advance() |> pop_limit()}

        op?(p, ",") ->
          {rest, p} = expr_list(advance(p), "}")
          {{:set, [first | rest]}, pop_limit(p)}

        op?(p, ":") ->
          p = advance(p)

          case filter_bind(first) do
            {:ok, bind} ->
              {pred, p} = expr(p, 0)
              p = p |> expect_op("}") |> pop_limit()
              {{:set_filter, bind, pred}, p}

            :error ->
              {binds, p} = binders(p, true)
              p = p |> expect_op("}") |> pop_limit()
              {{:set_map, first, binds}, p}
          end

        true ->
          error(p, peek(p), "expected `}`, `,`, or `:` in a set")
      end
    end
  end

  defp filter_bind({:app, "\\in", [{:name, x, _}, set], _}), do: {:ok, {x, set}}

  defp filter_bind({:app, "\\in", [{:tuple, elems}, set], _}) do
    if Enum.all?(elems, &match?({:name, _, _}, &1)),
      do: {:ok, {{:tuple, Enum.map(elems, fn {:name, n, _} -> n end)}, set}},
      else: :error
  end

  defp filter_bind(_), do: :error

  defp brackets(p) do
    p = push_limit(p, :none)

    case {peek(p), raw_at(p, p.pos + 1)} do
      {{:id, _, _, _}, {:op, "|->", _, _}} ->
        {fields, p} = fields(p, "|->", [])
        {{:record, fields}, pop_limit(p)}

      {{:id, _, _, _}, {:op, ":", _, _}} ->
        {fields, p} = fields(p, ":", [])
        {{:record_set, fields}, pop_limit(p)}

      _ ->
        {first, p} = expr(p, 0)

        cond do
          at?(p, :kw, "EXCEPT") ->
            {updates, p} = excepts(advance(p), [])
            p = p |> expect_op("]") |> pop_limit()
            {{:except, first, updates}, p}

          op?(p, "->") ->
            {range, p} = expr(advance(p), 0)
            p = p |> expect_op("]") |> pop_limit()
            {{:fun_set, first, range}, p}

          op?(p, "]_") ->
            p = p |> advance() |> pop_limit()
            {sub, p} = subscript(p)
            {{:box_action, first, sub}, p}

          op?(p, "|->") or op?(p, ",") ->
            {items, p} = more_items(p, [first])
            p = expect_op(p, "|->")
            {body, p} = expr(p, 0)
            p = p |> expect_op("]") |> pop_limit()
            {{:func, items_to_binds(p, items), body}, p}

          true ->
            error(p, peek(p), "unexpected #{describe(peek(p))} in brackets")
        end
    end
  end

  defp more_items(p, acc) do
    if op?(p, ",") do
      {e, p} = expr(advance(p), 0)
      more_items(p, [e | acc])
    else
      {Enum.reverse(acc), p}
    end
  end

  # `[x, y \in S, <<a, b>> \in T |-> e]`: items without `\in` take the
  # set of the next item.
  defp items_to_binds(p, items) do
    items
    |> Enum.reverse()
    |> Enum.reduce({[], nil}, fn item, {acc, set} ->
      case item do
        {:app, "\\in", [target, s], _} -> {[{target_of(p, target), s} | acc], s}
        {:name, n, _} when set != nil -> {[{n, set} | acc], set}
        _ -> raise Error, message: "bad bound variable in a function", file: p.file
      end
    end)
    |> elem(0)
  end

  defp target_of(_p, {:name, n, _}), do: n

  defp target_of(p, {:tuple, elems}) do
    {:tuple,
     Enum.map(elems, fn
       {:name, n, _} -> n
       _ -> raise Error, message: "bad tuple of bound variables", file: p.file
     end)}
  end

  defp target_of(p, _), do: raise(Error, message: "bad bound variable", file: p.file)

  defp fields(p, sep, acc) do
    {name, p} = expect_id(p)
    p = expect_op(p, sep)
    {e, p} = expr(p, 0)
    acc = [{name, e} | acc]

    cond do
      op?(p, ",") -> fields(advance(p), sep, acc)
      op?(p, "]") -> {Enum.reverse(acc), advance(p)}
      true -> error(p, peek(p), "expected `,` or `]` in a record")
    end
  end

  defp excepts(p, acc) do
    p = expect_op(p, "!")
    {path, p} = except_path(p, [])
    p = expect_op(p, "=")
    {value, p} = expr(p, 0)
    acc = [{path, value} | acc]
    if op?(p, ","), do: excepts(advance(p), acc), else: {Enum.reverse(acc), p}
  end

  defp except_path(p, acc) do
    cond do
      op?(p, "[") ->
        {args, p} = expr_list(advance(p), "]")
        except_path(p, [{:index, args} | acc])

      op?(p, ".") ->
        {field, p} =
          case raw_at(p, p.pos + 1) do
            {:id, f, _, _} -> {f, %{p | pos: p.pos + 2}}
            {:kw, f, _, _} -> {f, %{p | pos: p.pos + 2}}
            t -> error(p, t, "expected a field name")
          end

        except_path(p, [{:field, field} | acc])

      acc == [] ->
        error(p, peek(p), "expected `[` or `.` after `!`")

      true ->
        {Enum.reverse(acc), p}
    end
  end

  defp angles(p) do
    p = push_limit(p, :none)

    cond do
      op?(p, ">>") ->
        {{:tuple, []}, p |> advance() |> pop_limit()}

      true ->
        {items, p} = angle_items(p, [])

        case peek(p) do
          {:op, ">>", _, _} ->
            {{:tuple, items}, p |> advance() |> pop_limit()}

          {:op, ">>_", _, _} ->
            p = p |> advance() |> pop_limit()
            {sub, p} = subscript(p)

            case items do
              [a] -> {{:diamond_action, a, sub}, p}
              _ -> error(p, peek(p), "`<<A>>_v` needs one action")
            end

          t ->
            error(p, t, "expected `>>`, found #{describe(t)}")
        end
    end
  end

  defp angle_items(p, acc) do
    {e, p} = expr(p, 0)
    acc = [e | acc]
    if op?(p, ","), do: angle_items(advance(p), acc), else: {Enum.reverse(acc), p}
  end
end
