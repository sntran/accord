defmodule Accord.TLA.Checker.Semantic do
  @moduledoc """
  The semantic checks of SANY, the parser of TLC, on parsed modules.

  TLC refuses a specification with an error of SANY (the exit status
  ERROR_SPEC_PARSE). The parser of the checker reads the syntax; this
  module checks the meaning, with the rules and the error codes of SANY:

  - names: an unknown name (4200), a name defined two times (4201), a
    built-in name defined again (4202), an instance name without `!`
    (4203);
  - arguments: the number of arguments of an operator (4204), of a
    function (4260), operator arguments (4270-4275), `@` outside EXCEPT
    (4261), a record with a field two times (4262);
  - modules: a module that does not exist (4220), a module that uses
    itself (4222), a module name used two times (4223), EXTENDS of two
    different kinds of the same name (4224);
  - INSTANCE substitutions (4240-4243);
  - RECURSIVE declarations (4290-4294);
  - labels (4330-4337) and proofs (4350-4357);
  - levels (4205, 4206, 4244-4247, 4272, 4273, 4310-4315), in
    `Accord.TLA.Checker.Semantic.Level`.

  The checks build a semantic graph as SANY does: each name refers to a
  symbol (a map with an `:id`), and each expression is a node (a map with
  `:t`). The level checks use this graph.
  """

  alias Accord.TLA.Checker.{Parser, StandardModules}
  alias Accord.TLA.Checker.Semantic.{Level, Lint}

  defmodule Err do
    @moduledoc """
    A semantic error or warning: the SANY code, a message, a position,
    the module, and the level (`:error` or `:warning`).
    """
    defstruct [:code, :message, :pos, :module, level: :error]
  end

  # The built-in operators of SANY (BuiltInOperators.java): name =>
  # {arity, level, max levels of the arguments, weights}. Arity -1: any
  # number of arguments (one max level and one weight for all).
  @builtins %{
    "STRING" => {0, 0, [], []},
    "FALSE" => {0, 0, [], []},
    "TRUE" => {0, 0, [], []},
    "BOOLEAN" => {0, 0, [], []},
    "=" => {2, 0, [2, 2], [1, 1]},
    "/=" => {2, 0, [2, 2], [1, 1]},
    "'" => {1, 2, [1], [0]},
    "\\lnot" => {1, 0, [3], [1]},
    "\\land" => {2, 0, [3, 3], [1, 1]},
    "\\lor" => {2, 0, [3, 3], [1, 1]},
    "\\equiv" => {2, 0, [3, 3], [1, 1]},
    "=>" => {2, 0, [3, 3], [1, 1]},
    "SUBSET" => {1, 0, [2], [1]},
    "UNION" => {1, 0, [2], [1]},
    "DOMAIN" => {1, 0, [2], [1]},
    "\\subseteq" => {2, 0, [2, 2], [1, 1]},
    "\\in" => {2, 0, [2, 2], [1, 1]},
    "\\notin" => {2, 0, [2, 2], [1, 1]},
    "\\" => {2, 0, [2, 2], [1, 1]},
    "\\cap" => {2, 0, [2, 2], [1, 1]},
    "\\cup" => {2, 0, [2, 2], [1, 1]},
    "~>" => {2, 3, [3, 3], [0, 0]},
    "[]" => {1, 3, [3], [0]},
    "<>" => {1, 3, [3], [0]},
    "ENABLED" => {1, 1, [2], [0]},
    "UNCHANGED" => {1, 2, [1], [0]},
    "\\cdot" => {2, 2, [2, 2], [0, 0]},
    "-+->" => {2, 3, [3, 3], [0, 0]},
    "$AngleAct" => {2, 2, [2, 1], [0, 0]},
    "$BoundedChoose" => {-1, 0, [2], [1]},
    "$BoundedExists" => {-1, 0, [3], [1]},
    "$BoundedForall" => {-1, 0, [3], [1]},
    "$CartesianProd" => {-1, 0, [2], [1]},
    "$Case" => {-1, 0, [3], [1]},
    "$ConjList" => {-1, 0, [3], [1]},
    "$DisjList" => {-1, 0, [3], [1]},
    "$Except" => {-1, 0, [2], [1]},
    "$FcnApply" => {2, 0, [2, 2], [1, 1]},
    "$FcnConstructor" => {-1, 0, [3], [1]},
    "$IfThenElse" => {3, 0, [3, 3, 3], [1, 1, 1]},
    "$NonRecursiveFcnSpec" => {1, 0, [3], [1]},
    "$Pair" => {2, 0, [3, 3], [1, 1]},
    "$RcdConstructor" => {-1, 0, [3], [1]},
    "$RcdSelect" => {2, 0, [2, 0], [1, 1]},
    "$RecursiveFcnSpec" => {1, 0, [3], [1]},
    "$Seq" => {-1, 0, [2], [1]},
    "$SetEnumerate" => {-1, 0, [2], [1]},
    "$SetOfAll" => {-1, 0, [2], [1]},
    "$SetOfFcns" => {-1, 0, [2], [1]},
    "$SetOfRcds" => {-1, 0, [2], [1]},
    "$SF" => {2, 3, [1, 2], [0, 0]},
    "$SquareAct" => {2, 2, [2, 1], [0, 0]},
    "$SubsetOf" => {1, 0, [2], [1]},
    "$TemporalExists" => {1, 3, [3], [0]},
    "$TemporalForall" => {1, 3, [3], [0]},
    "$Tuple" => {-1, 0, [2], [1]},
    "$UnboundedChoose" => {1, 0, [2], [1]},
    "$UnboundedExists" => {1, 0, [3], [1]},
    "$UnboundedForall" => {1, 0, [3], [1]},
    "$WF" => {2, 3, [1, 2], [0, 0]},
    "$Nop" => {1, 0, [3], [1]},
    "$Qed" => {0, 0, [], []},
    "$Pfcase" => {1, 0, [3], [1]},
    "$Have" => {1, 0, [3], [1]},
    "$Take" => {1, 0, [3], [1]},
    "$Pick" => {1, 0, [3], [1]},
    "$Witness" => {-1, 0, [2], [1]},
    "$Suffices" => {1, 0, [3], [1]}
  }

  # Built-in operators that the parser keeps as `{:app, op, args}`.
  @infix_builtins %{
    "=" => "=",
    "/=" => "/=",
    "\\in" => "\\in",
    "\\notin" => "\\notin",
    "\\subseteq" => "\\subseteq",
    "\\cup" => "\\cup",
    "\\cap" => "\\cap",
    "\\" => "\\",
    "SUBSET" => "SUBSET",
    "UNION" => "UNION",
    "DOMAIN" => "DOMAIN",
    "\\cdot" => "\\cdot",
    "-+->" => "-+->"
  }

  # The names that a definition cannot have (BUILT_IN_SYMBOL_REDEFINED).
  @builtin_names ~w(TRUE FALSE BOOLEAN STRING)

  @doc "The built-in operator symbol `name`."
  def builtin(name) do
    {arity, level, max, weights} = Map.fetch!(@builtins, name)

    %{
      id: {:builtin, name},
      kind: :builtin,
      name: name,
      arity: arity,
      level: level,
      max: max,
      weights: weights
    }
  end

  # -- Entry point --

  @doc """
  Checks the module `mod` (parsed) and the modules it uses. `opts`:
  `:paths` (the directories of the modules), `:modules` (parsed modules
  by name). Gives the list of errors (`%Err{}`), empty when the module is
  correct.
  """
  def check(mod, opts \\ []) do
    keys = [
      :sem_errors,
      :sem_infos,
      :sem_loading,
      :sem_subs,
      :sem_paths,
      :sem_parsed,
      :sem_defs,
      :sem_insts,
      :sem_module,
      :sem_order,
      :sem_records,
      :sem_files
    ]

    old = Enum.map(keys, &{&1, Process.get(&1)})

    try do
      Process.put(:sem_errors, [])
      Process.put(:sem_infos, %{})
      Process.put(:sem_loading, [])
      Process.put(:sem_subs, %{})
      Process.put(:sem_defs, %{})
      Process.put(:sem_insts, [])
      Process.put(:sem_order, [])
      Process.put(:sem_records, [])
      Process.put(:sem_files, if(mod.file, do: [{mod.name, mod.file}], else: []))
      Process.put(:sem_module, mod.name)
      Process.put(:sem_paths, Keyword.get(opts, :paths, []))
      Process.put(:sem_parsed, Keyword.get(opts, :modules, %{}))

      if mod.file && Path.rootname(Path.basename(mod.file)) != mod.name do
        err(
          4221,
          {1, 1},
          "File name `#{Path.basename(mod.file)}' does not match the name `#{mod.name}' of the top level module it contains."
        )
      end

      # The other modules of the file (after the root module) are
      # available by name, as modules of other files.
      inner = for {:module, n, _} <- mod.order, do: n

      Enum.each(mod.submodules, fn sub ->
        unless sub.name in inner,
          do:
            Process.put(
              :sem_subs,
              Map.put(Process.get(:sem_subs), sub.name, {sub, :outer_unknown})
            )
      end)

      info = analyze(mod, %{})

      # As SANY: the level checks and the lint checks only for a module
      # without errors.
      order = Enum.reverse(Process.get(:sem_order))

      unless errors?(Process.get(:sem_errors)) do
        Level.check(info, order, Enum.reverse(Process.get(:sem_insts)))
      end

      unless errors?(Process.get(:sem_errors)) do
        # Not the standard modules, not the inner modules.
        inner? = fn n -> match?({_, ctx} when is_map(ctx), Map.get(Process.get(:sem_subs), n)) end
        user = Enum.reject(order, &(StandardModules.source(&1.name) != nil or inner?.(&1.name)))
        Lint.check(user, Process.get(:sem_records, []), order)
      end

      # The PlusCal checksums of the files (SANY's `Validator`).
      Enum.each(Process.get(:sem_files, []), fn {name, file} -> Lint.pluscal(name, file) end)

      Process.get(:sem_errors) |> Enum.reverse()
    catch
      {:sem_abort, _} -> Process.get(:sem_errors) |> Enum.reverse()
    after
      Enum.each(old, fn {k, v} -> if v == nil, do: Process.delete(k), else: Process.put(k, v) end)
    end
  end

  @doc false
  def err(code, pos, message, level \\ :error) do
    mod = Process.get(:sem_module)
    e = %Err{code: code, message: message, pos: pos, module: mod, level: level}
    Process.put(:sem_errors, [e | Process.get(:sem_errors, [])])
    :error
  end

  @doc false
  def warn(code, pos, message), do: err(code, pos, message, :warning)

  @doc "True if the list has an error (not only warnings)."
  def errors?(errs), do: Enum.any?(errs, &(&1.level == :error))

  # -- Symbols --

  @doc false
  def new_sym(kind, name, arity, extra \\ %{}) do
    Map.merge(
      %{id: make_ref(), kind: kind, name: name, arity: arity, mod: Process.get(:sem_module)},
      extra
    )
  end

  # A definition symbol, its body set later (see `def_body/1`).
  defp put_def(sym), do: Process.put(:sem_defs, Map.put(Process.get(:sem_defs), sym.id, sym))

  @doc "The latest version of a definition symbol (with its body)."
  def def_of(%{id: id} = sym), do: Map.get(Process.get(:sem_defs), id, sym)

  # -- Modules --

  # The info of a module by name: analyzes it the first time.
  defp module_info(name, pos, outer_sub \\ nil) do
    infos = Process.get(:sem_infos)

    cond do
      Map.has_key?(infos, name) ->
        Map.fetch!(infos, name)

      name in Process.get(:sem_loading) ->
        err(
          4222,
          pos,
          "Circular dependency among .tla files; dependency cycle is: #{Enum.join(Enum.reverse([name | Process.get(:sem_loading)]), " -> ")}"
        )

        throw({:sem_abort, :cycle})

      true ->
        case fetch_module(name, outer_sub) do
          nil ->
            err(4220, pos, "Cannot find source file for module #{name}.")
            throw({:sem_abort, :missing})

          {mod, outer_ctx} ->
            analyze(mod, outer_ctx)
        end
    end
  end

  defp fetch_module(name, _outer) do
    subs = Process.get(:sem_subs)
    parsed = Process.get(:sem_parsed)

    cond do
      Map.has_key?(subs, name) ->
        Map.fetch!(subs, name)

      src = StandardModules.source(name) ->
        {Parser.parse_module(src, file: "#{name}.tla"), %{}}

      Map.has_key?(parsed, name) ->
        {Map.fetch!(parsed, name), %{}}

      path = Enum.find_value(Process.get(:sem_paths), &existing(Path.join(&1, name <> ".tla"))) ->
        mod = Parser.parse_module(File.read!(path), file: path)
        Process.put(:sem_files, Process.get(:sem_files, []) ++ [{mod.name, path}])

        if mod.name != name do
          err(
            4221,
            {1, 1},
            "File name `#{name}.tla' does not match the name `#{mod.name}' of the top level module it contains."
          )
        end

        # The other modules of the file are available by name.
        Enum.each(mod.submodules, fn sub ->
          unless Map.has_key?(Process.get(:sem_subs), sub.name),
            do:
              Process.put(
                :sem_subs,
                Map.put(Process.get(:sem_subs), sub.name, {sub, :outer_unknown})
              )
        end)

        {mod, %{}}

      true ->
        nil
    end
  rescue
    e in Parser.Error ->
      err(
        4220,
        {e.line || 1, e.column || 1},
        "Parse error in module #{name}: #{Exception.message(e)}"
      )

      throw({:sem_abort, :parse})
  end

  defp existing(path), do: if(File.exists?(path), do: path)

  # Analyzes a module: gives its info (`ctx`, the names it exports, its
  # declarations, its definitions).
  defp analyze(mod, outer_ctx) do
    outer_ctx = if outer_ctx == :outer_unknown, do: %{}, else: outer_ctx
    saved = Process.get(:sem_module)
    Process.put(:sem_module, mod.name)
    Process.put(:sem_loading, [mod.name | Process.get(:sem_loading)])

    # The inner modules: registered with the context at their place (see
    # `items/2`); until then, a reference finds them with the outer
    # context so far.
    st = %{
      mod: mod,
      ctx: outer_ctx,
      exports: %{},
      decls: [],
      defs: [],
      locals: MapSet.new(),
      recursive: %{},
      rec_open: [],
      theorems: [],
      assumes: [],
      instances: [],
      extended: []
    }

    st = Enum.reduce(mod.extends, st, &extend(&2, &1))
    st = items(st, mod)

    # RECURSIVE declarations without definitions.
    Enum.each(st.recursive, fn {name, sym} ->
      unless def_of(sym)[:defined],
        do: err(4291, sym[:pos] || {1, 1}, "Recursive operator #{name} declared but not defined.")
    end)

    info = %{
      name: mod.name,
      ctx: st.ctx,
      exports: st.exports,
      decls: st.decls,
      defs: Enum.reverse(st.defs),
      theorems: Enum.reverse(st.theorems),
      assumes: Enum.reverse(st.assumes),
      instances: Enum.reverse(st.instances),
      recursive: st.defs |> Enum.reverse() |> Enum.filter(& &1[:recursive]),
      extends: mod.extends
    }

    Process.put(:sem_infos, Map.put(Process.get(:sem_infos), mod.name, info))
    Process.put(:sem_order, [info | Process.get(:sem_order, [])])
    Process.put(:sem_loading, tl(Process.get(:sem_loading)))
    Process.put(:sem_module, saved)
    info
  end

  # EXTENDS M: the names that M exports, and its declarations.
  defp extend(st, name) do
    if name in st.extended do
      st
    else
      if Map.has_key?(Process.get(:sem_subs), name) and
           Map.has_key?(Process.get(:sem_infos), name) == false and
           StandardModules.source(name) != nil and false,
         do: :ok

      info = module_info(name, {1, 1})

      ctx =
        Enum.reduce(info.exports, st.ctx, fn {n, sym}, ctx ->
          case Map.fetch(ctx, n) do
            :error ->
              Map.put(ctx, n, sym)

            {:ok, %{id: id}} when id == sym.id ->
              ctx

            {:ok, other} ->
              cond do
                other.kind != sym.kind and not (def_kind?(other) and def_kind?(sym)) ->
                  err(
                    4224,
                    {1, 1},
                    "Incompatible declarations of #{n} in modules that #{st.mod.name} extends."
                  )

                # The first definition stays.
                origin(other) != origin(sym) ->
                  warn(
                    4800,
                    sym[:pos],
                    "Warning: the definition of '#{n}' conflicts with its definition at #{show_pos(other[:pos])}."
                  )

                true ->
                  :ok
              end

              ctx
          end
        end)

      exports = Map.merge(info.exports, st.exports)

      decls =
        st.decls ++ Enum.reject(info.decls, fn d -> Enum.any?(st.decls, &(&1.id == d.id)) end)

      %{st | ctx: ctx, exports: exports, decls: decls, extended: [name | st.extended]}
    end
  end

  defp def_kind?(sym), do: sym.kind in [:def, :fun, :theorem, :instance_def, :builtin]

  # The module where a symbol is first defined (an INSTANCE copies the
  # definitions of a module; SANY's `sameOriginallyDefinedInModule`).
  defp origin(%{kind: :instance_def, base_sym: base}), do: origin(base)
  defp origin(sym), do: sym[:mod]

  # The kinds of SANY: a definition of an operator, a theorem, a
  # declaration.
  defp sany_kind(%{kind: k}) when k in [:def, :fun, :instance_def, :builtin], do: :op
  defp sany_kind(%{kind: k}), do: k

  # The items of a module in order.
  defp items(st, mod) do
    queues = %{
      units: Enum.reject(mod.units, &Map.has_key?(&1, :from)),
      named: Enum.filter(mod.units, &Map.has_key?(&1, :from)),
      constants: mod.constants,
      theorems: mod.theorems,
      assumes: mod.assumes,
      uses: mod.uses,
      subs: mod.submodules
    }

    {st, _} =
      Enum.reduce(mod.order, {st, queues}, fn {kind, name, pos}, {st, q} ->
        item(kind, name, pos, st, q)
      end)

    st
  end

  defp item(:constant, name, pos, st, q) do
    [{^name, arity} | rest] = q.constants
    st = close_recursive(st, pos, "a CONSTANT declaration")
    sym = new_sym(:constant, name, arity, %{pos: pos})
    {declare(st, name, sym, pos, false) |> add_decl(sym), %{q | constants: rest}}
  end

  defp item(:variable, name, pos, st, q) do
    st = close_recursive(st, pos, "a VARIABLE declaration")
    sym = new_sym(:variable, name, 0, %{pos: pos})
    {declare(st, name, sym, pos, false) |> add_decl(sym), q}
  end

  defp item(:recursive, name, pos, st, q) do
    {^name, arity} = Enum.find(st.mod.recursive, fn {n, _} -> n == name end)
    sym = new_sym(:def, name, arity, %{pos: pos, recursive: true, defined: false, params: nil})
    put_def(sym)
    st = declare(st, name, sym, pos, false)
    {%{st | recursive: Map.put(st.recursive, name, sym), rec_open: [name | st.rec_open]}, q}
  end

  defp item(:instance, _name, pos, st, q) do
    [unit | rest] = q.units
    {unit_def(st, unit, pos), %{q | units: rest}}
  end

  defp item(:def, _name, pos, st, q) do
    [unit | rest] = q.units
    {unit_def(st, unit, pos), %{q | units: rest}}
  end

  defp item(:theorem, _name, pos, st, q) do
    [thm | rest] = q.theorems
    st = close_recursive(st, pos, "a theorem")
    {_named, q} = take_named(q, thm.name, :theorem)
    named = if thm.name, do: %{name: thm.name, pos: thm.pos}
    {theorem(st, thm, named), %{q | theorems: rest}}
  end

  defp item(:assume, name, pos, st, q) do
    [{e, apos} | rest] = q.assumes
    st = close_recursive(st, pos, "an assumption")
    {_named, q} = take_named(q, name, :assume)
    {assumption(st, name, e, apos), %{q | assumes: rest}}
  end

  defp item(:use, _name, pos, st, q) do
    [use | rest] = q.uses
    st = close_recursive(st, pos, "a USE or HIDE")
    uses(use, %{env(st) | proof: true})
    {st, %{q | uses: rest}}
  end

  defp item(:proof, _name, pos, st, q), do: {close_recursive(st, pos, "a proof"), q}

  defp item(:module, name, pos, st, q) do
    st = close_recursive(st, pos, "a module")
    sub = Enum.find(q.subs, &(&1.name == name))

    if name in st.extended or
         (Map.has_key?(Process.get(:sem_infos), name) and name != st.mod.name and
            StandardModules.source(name) != nil) do
      err(4223, pos, "Multiple definitions of module name #{name}.")
    end

    # SANY checks an inner module where it is; it sees the names of the
    # outer module defined before it.
    Process.put(:sem_subs, Map.put(Process.get(:sem_subs), name, {sub, st.ctx}))
    Process.put(:sem_infos, Map.delete(Process.get(:sem_infos), name))
    module_info(name, pos)
    {st, q}
  end

  defp take_named(q, nil, _from), do: {nil, q}

  defp take_named(q, name, from) do
    case Enum.split_while(q.named, &(&1.name != name or &1.from != from)) do
      {before, [u | after_]} -> {u, %{q | named: before ++ after_}}
      _ -> {nil, q}
    end
  end

  defp add_decl(st, sym), do: %{st | decls: st.decls ++ [sym]}

  # A RECURSIVE section: between a RECURSIVE declaration and the
  # definition, no declarations, modules, theorems, proofs, assumptions,
  # USE, or HIDE (SANY's checkIfInRecursiveSection).
  defp close_recursive(st, pos, what) do
    open =
      st.recursive
      |> Enum.reject(fn {_, sym} -> def_of(sym)[:defined] end)
      |> Enum.map(&elem(&1, 0))

    if open != [] do
      err(
        4294,
        pos,
        "#{what} may not appear within a recursive definition section (#{hd(open)})."
      )
    end

    st
  end

  # Declares a name in the module: an error when the name exists.
  defp declare(st, name, sym, pos, local?) do
    cond do
      name in @builtin_names ->
        err(4202, pos, "Symbol #{name} is a built-in operator, and cannot be redefined.")
        st

      Map.has_key?(st.ctx, name) and not recursive_placeholder?(st.ctx[name], sym) ->
        err(
          4201,
          pos,
          "Multiply-defined symbol '#{name}': this definition or declaration conflicts with the one at #{show_pos(st.ctx[name][:pos])}."
        )

        %{st | ctx: Map.put(st.ctx, name, sym)}

      true ->
        exports = if local?, do: st.exports, else: Map.put(st.exports, name, sym)
        %{st | ctx: Map.put(st.ctx, name, sym), exports: exports}
    end
  end

  defp recursive_placeholder?(%{recursive: true, defined: false, id: id}, %{id: id}), do: true
  defp recursive_placeholder?(_, _), do: false

  @doc false
  def show_pos({l, c}), do: "line #{l}, col #{c}"
  def show_pos(_), do: "an earlier place"

  # The environment of an expression of the module.
  defp env(st) do
    %{
      ctx: st.ctx,
      locals: %{},
      bound: [],
      at: false,
      label_ok: true,
      labels: nil,
      proof: false,
      fact: false,
      mod: st.mod.name,
      rec: st.recursive,
      self: nil,
      let_depth: 0
    }
  end

  # -- Definitions --

  defp unit_def(st, %{kind: :op} = d, pos) do
    st = check_rec_section(st, d, pos)
    {params, penv} = params(d.params, %{env(st) | labels: :top}, d.pos || pos)
    existing = recursive_sym(st, d)

    sym =
      (existing ||
         new_sym(:def, d.name, length(d.params), %{pos: d.pos || pos}))
      |> Map.merge(%{params: params, local: d.local, defined: true, arity: length(d.params)})

    if existing && existing.arity != length(d.params) do
      err(
        4292,
        d.pos || pos,
        "Arity of RECURSIVE declaration of #{d.name} does not match its definition."
      )
    end

    put_def(sym)
    body = with_labels(fn -> res(d.body, penv) end)
    sym = Map.put(sym, :body, body)
    put_def(sym)

    st =
      if existing,
        do: %{st | exports: if(d.local, do: st.exports, else: Map.put(st.exports, d.name, sym))},
        else: declare(st, d.name, sym, d.pos || pos, d.local)

    st = if existing, do: %{st | ctx: Map.put(st.ctx, d.name, sym)}, else: st

    %{
      st
      | defs: [sym | st.defs],
        locals: if(d.local, do: MapSet.put(st.locals, d.name), else: st.locals)
    }
  end

  defp unit_def(st, %{kind: :fun} = d, pos) do
    st = check_rec_section(st, d, pos)
    existing = recursive_sym(st, d)

    if existing && existing.arity != 0 do
      err(
        4292,
        d.pos || pos,
        "Arity of RECURSIVE declaration of #{d.name} does not match its definition."
      )
    end

    sym =
      (existing || new_sym(:fun, d.name, 0, %{pos: d.pos || pos}))
      |> Map.merge(%{
        kind: :fun,
        params: [],
        local: d.local,
        defined: true,
        arity: 0,
        nbinds: length(d.binds)
      })

    put_def(sym)
    # The function is defined in its own body (a recursive function).
    env = %{env(st) | locals: %{d.name => sym}, labels: :top}
    body = with_labels(fn -> bounded("$FcnConstructor", d.binds, [d.body], env, d.pos || pos) end)
    sym = Map.put(sym, :body, body)
    put_def(sym)

    st =
      if existing,
        do: %{
          st
          | ctx: Map.put(st.ctx, d.name, sym),
            exports: if(d.local, do: st.exports, else: Map.put(st.exports, d.name, sym))
        },
        else: declare(st, d.name, sym, d.pos || pos, d.local)

    %{st | defs: [sym | st.defs]}
  end

  defp unit_def(st, %{kind: :instance} = d, pos) do
    {params, penv} = params(d.params || [], env(st), d.pos || pos)
    inst = instance(d, penv, d.pos || pos)

    case d.name do
      nil ->
        # The definitions of the module, with the substitution, in this
        # module; also the named instances of the module (`I!Op`).
        named =
          inst.info.exports
          |> Enum.filter(fn {_, sym} -> sym.kind == :instance end)
          |> Map.new(fn {n, sym} -> {n, Map.put(sym, :base, sym.id)} end)

        Enum.reduce(Map.merge(named, inst.defs), %{st | instances: [inst | st.instances]}, fn {n,
                                                                                               sym},
                                                                                              st ->
          case Map.fetch(st.ctx, n) do
            {:ok, %{id: id}} when id == sym.base ->
              st

            {:ok, other} ->
              # SANY (SymbolTable.addSymbol): an error for symbols of two
              # kinds or arities, else a warning for two origins.
              cond do
                sany_kind(other) != sany_kind(sym) or (other.arity || 0) != (sym.arity || 0) ->
                  err(
                    4201,
                    pos,
                    "Multiply-defined symbol '#{n}': this definition or declaration conflicts with the one at #{show_pos(other[:pos])}."
                  )

                origin(other) != origin(sym) ->
                  warn(
                    4801,
                    pos,
                    "Multiple declarations or definitions for symbol #{n}. This duplicates the one at #{show_pos(other[:pos])}."
                  )

                true ->
                  :ok
              end

              st

            :error ->
              exports = if d.local, do: st.exports, else: Map.put(st.exports, n, sym)
              %{st | ctx: Map.put(st.ctx, n, sym), exports: exports}
          end
        end)

      name ->
        sym =
          new_sym(:instance, name, length(params), %{
            pos: d.pos || pos,
            params: params,
            inst: inst,
            local: d.local
          })

        put_def(sym)
        st = declare(st, name, sym, d.pos || pos, d.local)
        %{st | instances: [inst | st.instances]}
    end
  end

  defp recursive_sym(st, d) do
    case Map.fetch(st.recursive, d.name) do
      {:ok, sym} -> if def_of(sym)[:defined], do: nil, else: sym
      :error -> nil
    end
  end

  # A definition of a RECURSIVE section: the section stays open until
  # all its operators have definitions.
  defp check_rec_section(st, d, _pos) do
    open = Enum.reject(st.rec_open, &(&1 == d.name or def_of(st.recursive[&1])[:defined]))
    %{st | rec_open: if(open == [] and d.name in st.rec_open, do: [], else: st.rec_open)}
  end

  # The parameters of a definition: symbols, and the environment with them.
  defp params(params, env, pos) do
    {syms, env} =
      Enum.map_reduce(params, env, fn {name, arity}, env ->
        sym = new_sym(:param, name, arity, %{pos: pos})
        {sym, bind(env, name, sym, pos)}
      end)

    {syms, env}
  end

  # A new local name (a parameter, a bound name, a LET definition): an
  # error when the name exists.
  defp bind(env, name, sym, pos) do
    cond do
      name in @builtin_names ->
        err(4202, pos, "Symbol #{name} is a built-in operator, and cannot be redefined.")

      Map.has_key?(env.locals, name) or Map.has_key?(env.ctx, name) ->
        err(4201, pos, "Multiply-defined symbol '#{name}'.")

      true ->
        :ok
    end

    %{env | locals: Map.put(env.locals, name, sym)}
  end

  # -- INSTANCE --

  # `INSTANCE M WITH a <- e`: checks the substitutions; gives the
  # instance: the module, the substitutions, and the definitions with
  # the substitution.
  defp instance(d, env, pos) do
    inst = instance_node(d, env, pos)
    Process.put(:sem_insts, [inst | Process.get(:sem_insts, [])])
    inst
  end

  defp instance_node(d, env, pos) do
    info = module_info(d.module, pos)

    if d.module == env.mod, do: err(4222, pos, "Module #{d.module} instantiates itself.")

    decls = info.decls
    by_name = Map.new(decls, &{&1.name, &1})

    explicit =
      Enum.reduce(d.subs, %{}, fn {name, e}, acc ->
        cond do
          Map.has_key?(acc, name) ->
            err(
              4241,
              pos,
              "Multiple substitutions for symbol #{name} in instantiation of #{d.module}."
            )

            acc

          not Map.has_key?(by_name, name) ->
            if Map.has_key?(info.ctx, name),
              do:
                err(
                  4242,
                  pos,
                  "Illegal substitution for #{name}: it is not a CONSTANT or VARIABLE of module #{d.module}."
                ),
              else:
                err(
                  4242,
                  pos,
                  "Substitution for #{name}, which is not a symbol of module #{d.module}."
                )

            acc

          true ->
            Map.put(acc, name, e)
        end
      end)

    substs =
      Enum.flat_map(decls, fn decl ->
        case Map.fetch(explicit, decl.name) do
          {:ok, e} ->
            [{decl, subst_expr(decl, e, env, pos)}]

          :error ->
            case lookup(env, decl.name) do
              nil ->
                err(
                  4240,
                  pos,
                  "Instantiation of module #{d.module} requires a substitution for #{decl.name}, which is not defined here."
                )

                []

              sym ->
                [{decl, implicit_subst(decl, sym, pos)}]
            end
        end
      end)

    inst = %{
      id: make_ref(),
      module: d.module,
      info: info,
      substs: substs,
      pos: pos,
      in: env.mod,
      params: Enum.map(d[:params] || [], fn {n, _} -> env.locals[n] end) |> Enum.reject(&is_nil/1)
    }

    # The definitions of the instance: the exported definitions of M.
    defs =
      info.exports
      |> Enum.filter(fn {_, sym} -> sym.kind in [:def, :fun, :theorem, :instance_def] end)
      |> Map.new(fn {n, sym} -> {n, instance_def(inst, sym)} end)

    Map.put(inst, :defs, defs)
  end

  defp subst_expr(decl, e, env, pos) do
    if decl.arity > 0 do
      node = res_oparg(e, decl.arity, env, pos)

      case node do
        # A subexpression name (`COp!@!++`) takes the parameters of its
        # path; its arity is not checked here.
        %{t: :oparg, selector: true} ->
          :ok

        %{t: :oparg, op: op} ->
          if op.arity != decl.arity,
            do:
              err(
                4243,
                pos,
                "Substitution for operator #{decl.name} of arity #{decl.arity} with an operator of arity #{op.arity}."
              )

        _ ->
          :ok
      end

      node
    else
      case e do
        {:lambda, _, _} ->
          err(4275, pos, "LAMBDA given where an expression is required for #{decl.name}.")
          error_node()

        {:op_arg, _} ->
          err(4243, pos, "Substitution for #{decl.name} of arity 0 with an operator.")
          error_node()

        _ ->
          res(e, env)
      end
    end
  end

  defp implicit_subst(decl, sym, pos) do
    cond do
      decl.arity > 0 ->
        if (sym[:arity] || 0) != decl.arity,
          do:
            err(
              4243,
              pos,
              "Substitution for operator #{decl.name} of arity #{decl.arity} with an operator of arity #{sym[:arity]}."
            )

        %{t: :oparg, op: sym, id: make_ref(), pos: pos}

      (sym[:arity] || 0) != 0 ->
        err(4204, pos, "The operator #{decl.name} requires #{sym.arity} arguments.")
        error_node()

      sym.kind == :instance ->
        err(4203, pos, "Operator name #{decl.name} is incomplete.")
        error_node()

      true ->
        %{t: :appl, op: sym, args: [], id: make_ref(), pos: pos}
    end
  end

  # A definition of M in an instance: the parameters of the instance,
  # then the parameters of the definition; the body has the
  # substitution.
  defp instance_def(inst, sym) do
    key = {:sem_inst_def, inst.id, sym.id}

    case Process.get(key) do
      nil ->
        base = def_of(sym)

        # `I(x)!Op(y)` is an operator of the parameters of I and of Op.
        d =
          new_sym(:instance_def, sym.name, length(inst.params) + base.arity, %{
            op_arity: base.arity,
            base: sym.id,
            base_sym: base,
            inst: inst,
            params: base[:params] || [],
            pos: base[:pos],
            mod: base[:mod],
            defined: true,
            nbinds: base[:nbinds]
          })

        Process.put(key, d)
        d

      d ->
        d
    end
  end

  # -- Theorems, assumptions, USE --

  defp theorem(st, %{unparsed: _}, named), do: declare_named(st, named, :theorem)

  defp theorem(st, thm, named) do
    env = %{env(st) | labels: if(thm.name, do: :top, else: :forbidden)}
    {body, benv} = with_labels(fn -> statement(thm.body, env) end)
    st = declare_named(st, named, :theorem, body, thm)
    pf = if thm.proof, do: proof(thm.proof, %{benv | proof: true, ctx: st.ctx}, body, thm.pos)
    %{st | theorems: [%{body: body, proof: pf, pos: thm.pos, name: thm.name} | st.theorems]}
  end

  defp assumption(st, name, e, pos) do
    env = %{env(st) | labels: if(name, do: :top, else: :forbidden)}
    body = with_labels(fn -> res(e, env) end)
    named = if name, do: %{name: name, pos: pos}
    st = declare_named(st, named, :assume, body, nil)
    %{st | assumes: [%{body: body, pos: pos} | st.assumes]}
  end

  defp declare_named(st, named, kind, body \\ nil, thm \\ nil)
  defp declare_named(st, nil, _kind, _body, _thm), do: st

  defp declare_named(st, named, kind, body, thm) do
    sym =
      new_sym(:theorem, named.name, 0, %{
        pos: named.pos,
        body: body,
        defined: true,
        params: [],
        from: kind,
        assume_prove: match?(%{t: :assume_prove}, body),
        thm: thm
      })

    put_def(sym)
    declare(st, named.name, sym, named.pos, false) |> Map.update!(:defs, &[sym | &1])
  end

  # The statement of a theorem: an expression or ASSUME/PROVE. Gives the
  # node and the environment with the NEW symbols.
  defp statement({:assume_prove, _, _} = ap, env), do: assume_prove(ap, env)
  defp statement(e, env), do: {res(e, env), env}

  defp assume_prove({:assume_prove, items, goal}, env) do
    {nodes, env2} =
      Enum.map_reduce(items, env, fn item, env ->
        case item do
          {:new, kind, name, arity, set, pos} ->
            range = if set, do: res(set, env)
            sym = new_sym(:new, name, arity, %{pos: pos, new_kind: kind, range: range})
            env = bind(env, name, sym, pos)
            # In a nested ASSUME/PROVE, no labels in the scope of a NEW.
            env =
              if env.labels in [:nested_ap, :nested_ap_new],
                do: %{env | labels: :nested_ap_new},
                else: env

            {%{t: :new, sym: sym, range: range, id: make_ref(), pos: pos}, env}

          {:assume_prove, _, _} = ap ->
            labels =
              if env.labels in [:forbidden, :nested_ap_new], do: env.labels, else: :nested_ap

            {node, _} = assume_prove(ap, %{env | labels: labels})
            {node, env}

          {:label, _name, _, {:assume_prove, _, _} = ap} ->
            {node, _} = assume_prove(ap, env)
            {node, env}

          e ->
            {res(e, env), env}
        end
      end)

    goal_node = res(goal, env2)
    {%{t: :assume_prove, items: nodes, goal: goal_node, id: make_ref()}, env2}
  end

  defp uses(%{unparsed: _}, _env), do: :ok

  defp uses(use, env) do
    Enum.each(use.facts, &fact(&1, env, use))
    Enum.each(use.defs, &def_name(&1, env, use.pos))
  end

  # A fact of USE, HIDE, or BY: an expression, a step, `MODULE M`.
  defp fact({:module, _name}, _env, _use), do: :ok
  defp fact({:op_name, _}, _env, _use), do: :ok
  defp fact({:step_ref, _, _}, _env, _use), do: :ok

  # In a HIDE, a fact is the name of a theorem, an assumption, or a step
  # (SANY's UseOrHideNode.factCheck); a USE can have expressions.
  defp fact(e, env, use) do
    node = res(e, %{env | proof: true, fact: true})

    if use.kind == :hide do
      step? = match?({:name, _, _}, e) and match?(%{kind: :step}, lookup(env, elem(e, 1)))

      case node do
        %{t: :appl, op: %{kind: :theorem}} ->
          :ok

        %{t: :appl} when not step? ->
          err(
            4357,
            elem_pos(e),
            "The only expression allowed as a fact in a HIDE is the name of a theorem, assumption, or step."
          )

        _ ->
          :ok
      end
    end
  end

  defp elem_pos({:name, _, pos}), do: pos
  defp elem_pos({:app, _, _, pos}), do: pos
  defp elem_pos(_), do: nil

  # A name of DEF: a definition.
  defp def_name({:op_name, _}, _env, _pos), do: :ok
  defp def_name({:module, _}, _env, _pos), do: :ok

  defp def_name({:name, n, pos}, env, _pos) do
    if lookup(env, n) == nil, do: err(4200, pos, "Unknown operator: `#{n}'.")
  end

  defp def_name({:inst, path, name, _args, pos}, env, _) do
    try do
      inst_ref(path, name, [], pos, env, :def)
    catch
      {:sem_skip, _} -> :ok
    end
  end

  defp def_name(_, _env, _pos), do: :ok

  # -- Proofs (see `Accord.TLA.Checker.Semantic.Proof` for the rules) --

  # A proof: nil for a leaf proof, else the node of its steps (for the
  # level checks, see `Accord.TLA.Checker.Semantic.Level`).
  defp proof(nil, _env, _goal, _pos), do: nil
  defp proof(:obvious, _env, _goal, _pos), do: nil
  defp proof(:omitted, _env, _goal, _pos), do: nil

  defp proof(%{kind: :by} = by, env, _goal, _pos),
    do:
      (
        uses(by, env)
        nil
      )

  defp proof({:steps, steps}, env, goal, _pos) do
    {nodes, _} = Enum.map_reduce(steps, env, fn step, env -> step(step, env, goal) end)
    %{t: :proof, steps: nodes, id: make_ref()}
  end

  defp step(step, env, goal) do
    if step[:implicit] && step.label,
      do:
        err(
          4350,
          step.pos,
          "A step with the level <+> or <*> cannot have a name (#{step.label})."
        )

    # In a proof, `@` is the right side of the step before.
    env = %{env | at: :proof}

    {node, env2, penv} =
      case {step.kind, step.body} do
        {:qed, _} ->
          {nil, env}

        {:define, defs} ->
          {nil, let_defs(defs, env)}

        {:use, use} ->
          uses(use, env)
          {nil, env}

        {:instance, inst} ->
          case inst.name do
            nil ->
              instance(inst, env, step.pos)
              {nil, env}

            name ->
              i = instance(inst, env, step.pos)
              sym = new_sym(:instance, name, 0, %{pos: step.pos, params: [], inst: i})
              {nil, bind(env, name, sym, step.pos)}
          end

        {:take, binds} ->
          ranges = Enum.map(binds, fn {_, s} -> if s, do: res(s, env) end)
          {_syms, env} = bind_names(binds, env, step.pos)
          {%{t: :take, ranges: Enum.reject(ranges, &is_nil/1), id: make_ref()}, env}

        {:pick, {binds, body}} ->
          ranges = Enum.map(binds, fn {_, s} -> if s, do: res(s, env) end)
          {syms, env2} = bind_names(binds, env, step.pos)
          b = res(body, env2)
          {%{t: :pick, syms: syms, ranges: ranges, body: b, id: make_ref()}, env2}

        {:witness, es} ->
          {%{t: :witness, args: Enum.map(es, &res(&1, env)), id: make_ref()}, env}

        {:have, e} ->
          {%{t: :have, arg: res(e, env), id: make_ref()}, env}

        {:case, e} ->
          {%{t: :pfcase, arg: res(e, env), id: make_ref()}, env}

        # SUFFICES ASSUME NEW x ... PROVE: x is in the next steps, not
        # in the proof of the step.
        {:suffices, b} ->
          {node, senv} = with_labels(fn -> statement(b, %{env | labels: :top}) end)
          {node, senv, env}

        # ASSUME NEW x ... PROVE: x is in the proof of the step only.
        {:assert, b} ->
          {node, aenv} = with_labels(fn -> statement(b, %{env | labels: :top}) end)
          if match?(%{t: :assume_prove}, node), do: {node, env, aenv}, else: {node, aenv, aenv}
      end
      |> case do
        {node, env2} -> {node, env2, env}
        t -> t
      end

    sub = if step.proof, do: proof(step.proof, penv, node || goal, step.pos)
    snode = %{t: :step, kind: step.kind, node: node, proof: sub, pos: step.pos, id: make_ref()}

    # A named step can be used as a fact; its NEW symbols stay inside.
    # The body of a HAVE, CASE, or PICK step is not an expression.
    if step.label do
      name = "<#{step.level}>#{step.label}"
      body = if step.kind in [:assert, :suffices], do: node
      sym = new_sym(:step, name, 0, %{pos: step.pos, step_kind: step.kind, body: body})
      {snode, %{env2 | locals: Map.put(env2.locals, name, sym)}}
    else
      {snode, env2}
    end
  end

  defp bind_names(binds, env, pos) do
    Enum.flat_map_reduce(binds, env, fn {target, _set}, env ->
      names =
        case target do
          {:tuple, ns} -> Enum.map(ns, &name_of/1)
          n -> [name_of(n)]
        end

      Enum.map_reduce(names, env, fn n, env ->
        sym = new_sym(:param, n, 0, %{pos: pos, bound: true})
        {sym, bind(env, n, sym, pos)}
      end)
    end)
  end

  defp name_of({:name, n, _}), do: n
  defp name_of(n) when is_binary(n), do: n

  # -- Labels --

  # Labels of one definition: the names must differ (a label inside a
  # label is in another scope).
  defp with_labels(fun) do
    old = Process.get(:sem_label_scope)
    Process.put(:sem_label_scope, MapSet.new())

    try do
      fun.()
    after
      if old == nil,
        do: Process.delete(:sem_label_scope),
        else: Process.put(:sem_label_scope, old)
    end
  end

  # -- Expressions --

  @doc false
  def error_node, do: %{t: :error, id: make_ref()}

  defp value_node, do: %{t: :value, id: make_ref()}

  @doc false
  def lookup(env, name) do
    case Map.fetch(env.locals, name) do
      {:ok, sym} ->
        sym

      :error ->
        case Map.fetch(env.ctx, name) do
          {:ok, sym} -> sym
          :error -> if Map.has_key?(@builtins, name) and name in @builtin_names, do: builtin(name)
        end
    end
  end

  # The node of an expression.
  @doc false
  def res(e, env) do
    case e do
      {:num, _} ->
        value_node()

      {:dec, _} ->
        value_node()

      {:str, _} ->
        value_node()

      {:value, _} ->
        value_node()

      {:at} ->
        at_node(env)

      {:name, n, pos} ->
        res_name(n, [], pos, env)

      {:app, n, args, pos} ->
        res_app(n, args, pos, env)

      {:and, items} ->
        appl("$ConjList", items, env)

      {:or, items} ->
        appl("$DisjList", items, env)

      {:not, x} ->
        appl("\\lnot", [x], env)

      {:implies, a, b} ->
        appl("=>", [a, b], env)

      {:equiv, a, b} ->
        appl("\\equiv", [a, b], env)

      {:prime, x} ->
        appl("'", [x], env)

      {:unchanged, x} ->
        appl("UNCHANGED", [x], env)

      {:enabled, x} ->
        appl("ENABLED", [x], env)

      {:always, x} ->
        appl("[]", [x], env)

      {:eventually, x} ->
        appl("<>", [x], env)

      {:leadsto, a, b} ->
        appl("~>", [a, b], env)

      {:box_action, a, sub} ->
        appl("$SquareAct", [a, sub], env)

      {:diamond_action, a, sub} ->
        appl("$AngleAct", [a, sub], env)

      {:wf, sub, a} ->
        appl("$WF", [sub, a], env)

      {:sf, sub, a} ->
        appl("$SF", [sub, a], env)

      {:if, c, t, f} ->
        appl("$IfThenElse", [c, t, f], env)

      {:case, arms, other} ->
        case_node(arms, other, env)

      {:forall, binds, body} ->
        quant(:forall, binds, body, env)

      {:exists, binds, body} ->
        quant(:exists, binds, body, env)

      {:choose, bind, body} ->
        quant(:choose, [bind], body, env)

      {:set, elems} ->
        appl("$SetEnumerate", elems, env)

      {:set_map, body, binds} ->
        bounded("$SetOfAll", binds, [body], env, nil)

      {:set_filter, bind, pred} ->
        bounded("$SubsetOf", [bind], [pred], env, nil)

      {:tuple, elems} ->
        appl("$Tuple", elems, env)

      {:func, binds, body} ->
        bounded("$FcnConstructor", binds, [body], env, nil)

      {:apply, f, args} ->
        fcn_apply(f, args, env)

      {:dot, r, _field} ->
        appl_nodes("$RcdSelect", [res(r, env), value_node()])

      {:record, fields} ->
        record("$RcdConstructor", fields, env)

      {:record_set, fields} ->
        record("$SetOfRcds", fields, env)

      {:fun_set, d, r} ->
        appl("$SetOfFcns", [d, r], env)

      {:times, sets} ->
        appl("$CartesianProd", sets, env)

      {:except, f, updates} ->
        except(f, updates, env)

      {:let, defs, body} ->
        let(defs, body, env)

      {:label, name, params, body} ->
        label(name, params, body, env)

      {:temporal_forall, names, body} ->
        temporal_quant("$TemporalForall", names, body, env)

      {:temporal_exists, names, body} ->
        temporal_quant("$TemporalExists", names, body, env)

      {:lambda, _, _} ->
        err(4275, nil, "LAMBDA given where an expression is required.")
        error_node()

      {:op_arg, op} ->
        err(4270, nil, "Operator #{op} given where an expression is required.")
        error_node()

      {:inst, path, name, args, pos} ->
        inst_expr(path, name, args, pos, env)

      {:step_ref, level, label} ->
        step_ref("<#{level}>#{label}", env)

      {:assume_prove, _, _} = ap ->
        elem(assume_prove(ap, env), 0)

      _ ->
        error_node()
    end
  end

  defp at_node(env) do
    if env.at,
      do: %{t: :at, id: make_ref(), except: env.at},
      else:
        (
          err(4261, nil, "@ used where its meaning is not defined.")
          error_node()
        )
  end

  # A built-in operator applied to expressions.
  defp appl(name, args, env), do: appl_nodes(name, Enum.map(args, &res(&1, env)))

  defp appl_nodes(name, nodes), do: %{t: :appl, op: builtin(name), args: nodes, id: make_ref()}

  defp case_node(arms, other, env) do
    pairs =
      Enum.map(arms, fn {c, v} -> appl("$Pair", [c, v], env) end) ++
        if(other, do: [appl_nodes("$Pair", [nil, res(other, env)])], else: [])

    appl_nodes("$Case", pairs)
  end

  defp record(name, fields, env) do
    fields
    |> Enum.map(&elem(&1, 0))
    |> Enum.frequencies()
    |> Enum.each(fn {f, n} ->
      if n > 1, do: err(4262, nil, "Non-unique fields in constructor: #{f}.")
    end)

    node =
      appl_nodes(
        name,
        Enum.map(fields, fn {_, v} -> appl_nodes("$Pair", [value_node(), res(v, env)]) end)
      )

    # The records and the sets of records, for the lint check (W4802).
    if name in ["$RcdConstructor", "$SetOfRcds"] do
      pairs =
        Enum.zip(Enum.map(fields, &elem(&1, 0)), Enum.map(node.args, fn %{args: [_, v]} -> v end))

      rec = %{module: env.mod, fields: pairs, id: node.id}
      Process.put(:sem_records, [rec | Process.get(:sem_records, [])])
    end

    node
  end

  defp except(f, updates, env) do
    fnode = res(f, env)

    pairs =
      Enum.map(updates, fn {path, v} ->
        keys =
          Enum.flat_map(path, fn
            {:index, args} -> Enum.map(args, &res(&1, env))
            {:field, _} -> [value_node()]
          end)

        # Labels are not allowed in EXCEPT; `@` is the value of the
        # function at the path.
        vnode = res(v, %{env | at: {:except, fnode}, labels: :except})
        appl_nodes("$Pair", [appl_nodes("$Seq", keys), vnode])
      end)

    appl_nodes("$Except", [fnode | pairs])
  end

  # `f[a, b]`: for a function definition, the number of arguments.
  defp fcn_apply(f, args, env) do
    fnode = res(f, env)

    case {f, fnode} do
      {{:name, n, pos}, %{t: :appl, op: %{kind: kind} = op}} when kind in [:fun, :instance_def] ->
        nb = op[:nbinds]

        if (nb && length(args) > 1) and length(args) != nb do
          err(
            4260,
            pos,
            "Function #{n} is defined with #{nb} arguments but is applied to #{length(args)} arguments."
          )
        end

      _ ->
        :ok
    end

    key =
      case args do
        [a] -> res(a, env)
        many -> appl("$Tuple", many, env)
      end

    appl_nodes("$FcnApply", [fnode, key])
  end

  # A name or an application.
  defp res_name(n, args, pos, env) do
    case lookup(env, n) do
      nil ->
        err(4200, pos, "Unknown operator: `#{n}'.")
        Enum.each(args, &res_arg(&1, 0, env, pos))
        error_node()

      %{kind: :instance} = sym ->
        if args != [] and length(args) != sym.arity,
          do: err(4204, pos, "The operator #{n} requires #{sym.arity} arguments."),
          else: err(4203, pos, "Operator name #{n} is incomplete.")

        error_node()

      %{kind: :step} = sym ->
        step_value(sym, pos)

      %{kind: :theorem} = sym ->
        if def_of(sym)[:assume_prove] && !env[:fact] do
          err(4355, pos, "ASSUME/PROVE used where an expression is required.")
          error_node()
        else
          apply_sym(sym, n, args, pos, env)
        end

      sym ->
        apply_sym(sym, n, args, pos, env)
    end
  end

  defp res_app(n, args, pos, env) do
    case Map.fetch(@infix_builtins, n) do
      {:ok, b} ->
        if lookup(env, n) == nil, do: appl(b, args, env), else: res_name(n, args, pos, env)

      :error ->
        res_name(n, args, pos, env)
    end
  end

  # An application of a symbol: the number of arguments, and operator
  # arguments where the parameters are operators.
  defp apply_sym(sym, n, args, pos, env) do
    arity = sym.arity || 0

    if arity >= 0 and arity != length(args) do
      err(4204, pos, "The operator #{n} requires #{arity} arguments.")
    end

    arities = param_arities(sym, length(args))

    nodes =
      args
      |> Enum.zip(arities)
      |> Enum.map(fn {a, k} -> res_arg(a, k, env, pos) end)

    # An operator argument cannot take operators (OpDefNode.match).
    if sym.kind in [:def, :fun, :instance_def] and arity == length(args) do
      nodes
      |> Enum.zip(arities)
      |> Enum.with_index()
      |> Enum.each(fn {{node, k}, i} ->
        with true <- k > 0,
             %{t: :oparg, op: %{kind: ok} = op} when ok in [:def, :fun, :instance_def] <- node,
             true <- Enum.any?(List.wrap(def_of(op)[:params]), &((&1.arity || 0) > 0)) do
          err(
            4271,
            pos,
            "Argument number #{i + 1} to operator '#{n}' should be a #{k}-parameter operator."
          )
        end
      end)
    end

    %{t: :appl, op: sym, args: nodes, id: make_ref(), pos: pos}
  end

  @doc false
  def param_arities(sym, n) do
    case def_of(sym) do
      %{params: params} when is_list(params) and params != [] ->
        Enum.map(params, & &1.arity) ++ List.duplicate(0, max(n - length(params), 0))

      _ ->
        List.duplicate(0, n)
    end
  end

  # An argument: an expression for a parameter of arity 0, an operator
  # for the others.
  defp res_arg(a, 0, env, pos) do
    case a do
      {:lambda, _, _} ->
        err(4275, pos, "LAMBDA given where an expression is required.")
        error_node()

      {:op_arg, op} ->
        err(4270, pos, "Operator #{op} given where an expression is required.")
        error_node()

      _ ->
        res(a, env)
    end
  end

  defp res_arg(a, k, env, pos), do: res_oparg(a, k, env, pos)

  # An operator argument of arity `k`.
  defp res_oparg(a, k, env, pos) do
    case a do
      {:name, m, p} ->
        case lookup(env, m) do
          nil ->
            err(4200, p, "Unknown operator: `#{m}'.")
            error_node()

          sym ->
            if (sym.arity || 0) != k,
              do:
                err(
                  4271,
                  p,
                  "Argument #{m} of arity #{sym.arity || 0} given for a parameter of arity #{k}."
                )

            %{t: :oparg, op: sym, id: make_ref(), pos: p}
        end

      {:op_arg, op} ->
        sym = lookup(env, op) || builtin_op(op)

        if sym == nil do
          err(4200, pos, "Unknown operator: `#{op}'.")
          error_node()
        else
          if sym.arity >= 0 and sym.arity != k,
            do:
              err(
                4271,
                pos,
                "Argument #{op} of arity #{sym.arity} given for a parameter of arity #{k}."
              )

          %{t: :oparg, op: sym, id: make_ref(), pos: pos}
        end

      {:lambda, names, body} ->
        if length(names) != k,
          do:
            err(
              4274,
              pos,
              "LAMBDA of #{length(names)} parameters given for a parameter of arity #{k}."
            )

        {params, lenv} = params(Enum.map(names, &{&1, 0}), env, pos)

        lam =
          new_sym(:def, "LAMBDA", length(names), %{
            params: params,
            pos: pos,
            defined: true,
            lambda: true
          })

        put_def(lam)
        lam = Map.put(lam, :body, res(body, lenv))
        put_def(lam)
        %{t: :oparg, op: lam, id: make_ref(), pos: pos}

      {:inst, path, name, [], p} ->
        case inst_ref(path, name, [], p, env, {:op, k}) do
          %{t: :oparg} = node -> node
          %{t: :appl, op: op} -> %{t: :oparg, op: op, id: make_ref(), pos: p}
          other -> other
        end

      _ ->
        err(4270, pos, "Higher-order operator required but expression given.")
        res(a, env)
        error_node()
    end
  end

  # The built-in operator of an operator argument (`'`, `[]`, `SUBSET`).
  defp builtin_op(op) do
    name =
      case op do
        "~" -> "\\lnot"
        "/\\" -> "\\land"
        "\\/" -> "\\lor"
        "<=>" -> "\\equiv"
        other -> other
      end

    if Map.has_key?(@builtins, name), do: builtin(name)
  end

  # A step name used as an expression: its statement.
  defp step_ref(name, env) do
    case Map.get(env.locals, name) do
      nil -> value_node()
      sym -> step_value(sym, nil)
    end
  end

  defp step_value(sym, pos) do
    if sym[:step_kind] in [
         :have,
         :take,
         :pick,
         :witness,
         :qed,
         :case,
         :suffices,
         :define,
         :use,
         :instance
       ] do
      err(4351, pos, "Non-expression step #{sym.name} used as an expression.")
      error_node()
    else
      sym[:body] || value_node()
    end
  end

  # Quantifiers, CHOOSE: bounded or not.
  defp quant(kind, binds, body, env) do
    bounded? = Enum.all?(binds, fn {_, s} -> s != nil end)

    name =
      case {kind, bounded?} do
        {:forall, true} -> "$BoundedForall"
        {:forall, false} -> "$UnboundedForall"
        {:exists, true} -> "$BoundedExists"
        {:exists, false} -> "$UnboundedExists"
        {:choose, true} -> "$BoundedChoose"
        {:choose, false} -> "$UnboundedChoose"
      end

    if bounded?,
      do: bounded(name, binds, [body], env, nil),
      else: unbounded(name, binds, body, env)
  end

  # A construct with bound names `x \\in S`: the ranges in the outer
  # context, then the names (as SANY's processQuantBoundArgs).
  defp bounded(name, binds, bodies, env, pos) do
    groups = group_binds(binds)
    ranges = Enum.map(groups, fn {_, set} -> res(set, env) end)

    {syms, benv} =
      Enum.map_reduce(groups, env, fn {targets, _}, env ->
        Enum.flat_map_reduce(targets, env, fn target, env ->
          names =
            case target do
              {:tuple, ns} -> Enum.map(ns, &name_of/1)
              n -> [name_of(n)]
            end

          Enum.map_reduce(names, env, fn n, env ->
            sym = new_sym(:param, n, 0, %{pos: pos, bound: true})
            {sym, bind(env, n, sym, pos)}
          end)
        end)
      end)

    benv = %{benv | bound: benv.bound ++ List.flatten(syms)}
    nodes = Enum.map(bodies, &res(&1, benv))
    %{t: :appl, op: builtin(name), args: nodes, bounds: Enum.zip(syms, ranges), id: make_ref()}
  end

  defp unbounded(name, binds, body, env) do
    names =
      Enum.flat_map(binds, fn
        {{:tuple, ns}, _} -> Enum.map(ns, &name_of/1)
        {n, _} -> [name_of(n)]
      end)

    {syms, benv} =
      Enum.map_reduce(names, env, fn n, env ->
        sym = new_sym(:param, n, 0, %{bound: true})
        {sym, bind(env, n, sym, nil)}
      end)

    benv = %{benv | bound: benv.bound ++ syms}
    %{t: :appl, op: builtin(name), args: [res(body, benv)], unbounded: syms, id: make_ref()}
  end

  defp temporal_quant(name, names, body, env) do
    {syms, benv} =
      Enum.map_reduce(names, env, fn n, env ->
        sym = new_sym(:param, n, 0, %{bound: true, temporal: true})
        {sym, bind(env, n, sym, nil)}
      end)

    benv = %{benv | bound: benv.bound ++ syms}
    %{t: :appl, op: builtin(name), args: [res(body, benv)], unbounded: syms, id: make_ref()}
  end

  # The groups of bound names with one range: `x, y \\in S` (the parser
  # repeats the range for each name).
  defp group_binds(binds) do
    binds
    |> Enum.chunk_while(
      nil,
      fn {t, s}, acc ->
        case acc do
          nil -> {:cont, {[t], s}}
          {ts, ^s} -> {:cont, {ts ++ [t], s}}
          {ts, s0} -> {:cont, {ts, s0}, {[t], s}}
        end
      end,
      fn
        nil -> {:cont, nil}
        acc -> {:cont, acc, nil}
      end
    )
  end

  # LET: the definitions in order, then the body.
  defp let(defs, body, env) do
    lenv = let_defs(defs, env)
    lenv = %{lenv | let_depth: env.let_depth}

    syms =
      Enum.flat_map(defs, fn d ->
        case Map.get(lenv.locals, d.name) do
          nil -> []
          s -> [s]
        end
      end)

    %{t: :let, defs: syms, body: res(body, lenv), id: make_ref()}
  end

  defp let_defs(defs, env) do
    env =
      Enum.reduce(defs, env, fn d, env ->
        case d.kind do
          :recursive ->
            Enum.reduce(d.decls, env, fn {name, arity}, env ->
              sym =
                new_sym(:def, name, arity, %{
                  pos: d.pos,
                  recursive: true,
                  defined: false,
                  params: nil,
                  let_level: env[:let_depth] || 0
                })

              put_def(sym)
              bind(env, name, sym, d.pos)
            end)

          :op ->
            {params, penv} = params(d.params, %{env | bound: [], labels: :top}, d.pos)
            placeholder = rec_placeholder(env, d.name)

            if placeholder && placeholder.arity != length(d.params),
              do:
                err(
                  4292,
                  d.pos,
                  "Arity of RECURSIVE declaration of #{d.name} does not match its definition."
                )

            sym =
              (placeholder || new_sym(:def, d.name, length(d.params), %{pos: d.pos, let: true}))
              |> Map.merge(%{params: params, defined: true, arity: length(d.params)})

            put_def(sym)

            body =
              with_labels(fn -> res(d.body, %{penv | let_depth: (env[:let_depth] || 0) + 1}) end)

            sym = Map.put(sym, :body, body)
            put_def(sym)

            if placeholder,
              do: %{env | locals: Map.put(env.locals, d.name, sym)},
              else: bind(env, d.name, sym, d.pos)

          :fun ->
            placeholder = rec_placeholder(env, d.name)

            if placeholder && placeholder.arity != 0,
              do:
                err(
                  4292,
                  d.pos,
                  "Arity of RECURSIVE declaration of #{d.name} does not match its definition."
                )

            sym =
              (placeholder || new_sym(:fun, d.name, 0, %{pos: d.pos, let: true}))
              |> Map.merge(%{
                kind: :fun,
                params: [],
                defined: true,
                nbinds: length(d.binds),
                arity: 0
              })

            put_def(sym)
            fenv = %{env | locals: Map.put(env.locals, d.name, sym), bound: [], labels: :top}

            body =
              with_labels(fn -> bounded("$FcnConstructor", d.binds, [d.body], fenv, d.pos) end)

            sym = Map.put(sym, :body, body)
            put_def(sym)

            if placeholder,
              do: %{env | locals: Map.put(env.locals, d.name, sym)},
              else: bind(env, d.name, sym, d.pos)

          :instance ->
            {params, penv} = params(d.params || [], env, d.pos)
            inst = instance(d, penv, d.pos)

            case d.name do
              nil ->
                env

              name ->
                sym =
                  new_sym(:instance, name, length(params), %{
                    params: params,
                    inst: inst,
                    pos: d.pos
                  })

                put_def(sym)
                bind(env, name, sym, d.pos)
            end
        end
      end)

    # The RECURSIVE declarations of this LET need definitions in it.
    Enum.each(defs, fn
      %{kind: :recursive, decls: decls, pos: pos} ->
        Enum.each(decls, fn {name, _} ->
          case Map.get(env.locals, name) do
            %{recursive: true} = s ->
              unless def_of(s)[:defined],
                do: err(4291, pos, "Recursive operator #{name} declared but not defined.")

            _ ->
              :ok
          end
        end)

      _ ->
        :ok
    end)

    env
  end

  # A RECURSIVE declaration of this LET (not of an outer one) for `name`.
  defp rec_placeholder(env, name) do
    case Map.get(env.locals, name) do
      %{recursive: true, defined: false} = s ->
        if (s[:let_level] || 0) == (env[:let_depth] || 0) do
          s
        else
          err(
            4293,
            s.pos,
            "Recursive operator #{name} is defined in an inner LET, not in the LET of its declaration."
          )

          nil
        end

      _ ->
        nil
    end
  end

  # A label: its parameters are the bound names of its scope.
  defp label(name, params, body, env) do
    case env.labels do
      :forbidden ->
        err(4333, nil, "Label #{name} is not in a definition or a proof step.")

      :except ->
        err(4335, nil, "Label #{name} is not allowed in EXCEPT.")

      :nested_ap_new ->
        err(4334, nil, "Label #{name} is not allowed in a nested ASSUME/PROVE with NEW.")

      _ ->
        :ok
    end

    scope = Process.get(:sem_label_scope) || MapSet.new()

    if MapSet.member?(scope, name),
      do: err(4336, nil, "Label #{name} is defined two times."),
      else: Process.put(:sem_label_scope, MapSet.put(scope, name))

    dups = params |> Enum.frequencies() |> Enum.filter(fn {_, n} -> n > 1 end)

    if dups != [],
      do: err(4330, nil, "Label #{name} has the parameter #{elem(hd(dups), 0)} two times.")

    bound_names = Enum.map(env.bound, & &1.name)

    missing = bound_names -- params
    if missing != [], do: err(4331, nil, "Label #{name} must have the parameter #{hd(missing)}.")

    extra = params -- bound_names

    if extra != [],
      do:
        err(
          4332,
          nil,
          "Label #{name} has the parameter #{hd(extra)}, which is not a bound name of its scope."
        )

    psyms =
      Enum.map(params, fn p -> Enum.find(env.bound, &(&1.name == p)) end)
      |> Enum.reject(&is_nil/1)

    inner = with_labels(fn -> res(body, %{env | bound: []}) end)
    %{t: :label, name: name, params: psyms, body: inner, id: make_ref()}
  end

  # -- Instances and subexpression names --

  defp inst_expr(path, name, args, pos, env) do
    inst_ref(path, name, args, pos, env, :expr)
  catch
    {:sem_skip, _} -> error_node()
  end

  # `I!Op(args)`, `I(x)!J!Op`, or a subexpression name (`Op!2`): the
  # node of the name. `want`: `:expr`, `{:op, arity}`, or `:def`.
  defp inst_ref(path, name, args, pos, env, want) do
    [{first, fargs} | rest] = path

    case is_binary(first) && lookup(env, first) do
      %{kind: :instance} = sym ->
        if length(fargs) != sym.arity and not (fargs == [] and want != :expr) do
          err(4204, pos, "The instance #{first} requires #{sym.arity} arguments.")
        end

        inst_args = Enum.map(fargs, &res(&1, env))

        inst_path(
          def_of(sym)[:inst],
          rest,
          name,
          args,
          pos,
          env,
          {want, fargs != [], inst_args},
          first
        )

      nil when is_binary(first) ->
        if String.starts_with?(first, "<") do
          value_node()
        else
          # SANY names the whole compound name when it has only names.
          segs = path ++ [{name, args}]

          full =
            if Enum.all?(segs, &is_binary(elem(&1, 0))),
              do: Enum.map_join(segs, "!", &elem(&1, 0)),
              else: first

          err(4200, pos, "Unknown operator: `#{full}'.")
          error_node()
        end

      _ ->
        # A subexpression of a definition: resolved with the evaluator's
        # rules (see `Accord.TLA.Checker.Eval.resolve_selector/3`);
        # here the arguments are checked: `Op(Foo, 9)!lab` gives the
        # operator Foo for a parameter of Op of arity 1.
        arities =
          case is_binary(first) && lookup(env, first) do
            %{} = sym -> param_arities(sym, length(fargs))
            _ -> List.duplicate(0, length(fargs))
          end

        fnodes = fargs |> Enum.zip(arities) |> Enum.map(fn {a, k} -> res_arg(a, k, env, pos) end)
        selector_node(path, name, args, pos, env, want, fnodes)
    end
  end

  defp inst_path(nil, _rest, _name, _args, _pos, _env, _want, _first), do: error_node()

  # `want` has a flag: true if the path gives the arguments of the
  # instances. `I(a)!Op(b)` gives them; the operator argument `I!Op` takes
  # them as the first parameters.
  defp inst_path(inst, [], name, args, pos, env, {want, given, inst_args}, first)
       when is_binary(name) do
    case Map.fetch(inst.defs, name) do
      {:ok, sym} ->
        sym =
          if (want == :expr or given) and sym[:op_arity],
            do: %{sym | arity: sym.op_arity},
            else: sym

        case want do
          # The node has the arguments of the instances, then the
          # arguments of the operator (as SANY).
          :expr ->
            node = apply_sym(sym, "#{first}!#{name}", args, pos, env)
            if match?(%{t: :appl}, node), do: %{node | args: inst_args ++ node.args}, else: node

          {:op, k} ->
            if sym.arity != k,
              do:
                err(
                  4271,
                  pos,
                  "Argument #{first}!#{name} of arity #{sym.arity} given for a parameter of arity #{k}."
                )

            %{t: :oparg, op: sym, id: make_ref(), pos: pos}

          :def ->
            sym
        end

      :error ->
        case Map.fetch(inst.info.exports, name) do
          {:ok, %{kind: :instance} = isym} when want == :def ->
            isym

          _ ->
            err(4200, pos, "Unknown operator: `#{first}!#{name}'.")
            error_node()
        end
    end
  end

  defp inst_path(
         inst,
         [{seg, segargs} | rest],
         name,
         args,
         pos,
         env,
         {want, given, inst_args},
         first
       )
       when is_binary(seg) do
    case Map.fetch(inst.info.exports, seg) do
      {:ok, %{kind: :instance} = isym} ->
        seg_nodes = Enum.map(segargs, &res(&1, env))

        inst_path(
          def_of(isym)[:inst],
          rest,
          name,
          args,
          pos,
          env,
          {want, given or segargs != [], inst_args ++ seg_nodes},
          "#{first}!#{seg}"
        )

      # `L!Op(Foo, 9)!lab`: a subexpression of a definition of the
      # instance.
      {:ok, sym} ->
        segargs
        |> Enum.zip(param_arities(sym, length(segargs)))
        |> Enum.each(fn {a, k} -> res_arg(a, k, env, pos) end)

        value_node()

      :error ->
        err(4200, pos, "Unknown operator: `#{first}!#{seg}'.")
        error_node()
    end
  end

  defp inst_path(_inst, _rest, _name, _args, _pos, _env, _want, _first), do: value_node()

  # A subexpression name: the checks of SANY on labels and arguments.
  # As an expression, the node is the selected subexpression, applied to
  # the arguments of the path (SANY makes an operator of the parameters
  # of the definition and of the bound names on the path).
  defp selector_node(path, name, args, pos, env, want, fnodes) do
    segs = path ++ [{name, args}]
    [{first, _} | rest] = segs

    case lookup(env, first) do
      %{kind: kind} = sym when kind in [:def, :theorem, :fun] ->
        d = def_of(sym)
        check_selector_labels(d, rest, pos)

        case want do
          {:op, _} ->
            Enum.each(rest, fn {_, a} -> Enum.each(a, &res(&1, env)) end)
            %{t: :oparg, op: sym, id: make_ref(), pos: pos, selector: true}

          _ ->
            {cur, params, sargs} = select(d[:body], rest, List.wrap(d[:params]), fnodes, env)

            cond do
              cur == nil ->
                value_node()

              params == [] ->
                cur

              true ->
                op =
                  new_sym(:def, "#{first}!...", length(params), %{
                    params: params,
                    body: cur,
                    defined: true,
                    selection: true
                  })

                put_def(op)
                %{t: :appl, op: op, args: sargs, id: make_ref(), pos: pos}
            end
        end

      _ ->
        Enum.each(rest, fn {_, a} -> Enum.each(a, &res(&1, env)) end)
        value_node()
    end
  end

  # Follows the selectors in the nodes: gives the node, the parameters
  # in scope (of the definition, of the labels, of the bound names), and
  # their arguments. A selector that the nodes do not have gives nil.
  defp select(cur, [], params, args, _env), do: {cur, params, args}
  defp select(nil, _segs, _params, _args, _env), do: {nil, [], []}

  defp select(cur, [{:colon, _} | rest], params, args, env) do
    select(skip_labels(cur), rest, params, args, env)
  end

  defp select(cur, [{name, largs} | rest], params, args, env) when is_binary(name) do
    lnodes = Enum.map(largs, &res(&1, env))

    case find_label(cur, name) do
      %{params: ps, body: body} ->
        select(body, rest, params ++ ps, args ++ lnodes, env)

      nil ->
        case let_def(cur, name) do
          %{} = d ->
            d = def_of(d)
            select(d[:body], rest, params ++ List.wrap(d[:params]), args ++ lnodes, env)

          nil ->
            {nil, [], []}
        end
    end
  end

  defp select(cur, [{sel, sargs} | rest], params, args, env) do
    snodes = Enum.map(sargs, &res(&1, env))

    case skip_labels(cur) do
      %{t: :let, body: body} ->
        if sel_num(sel, 1) == 1, do: select(body, rest, params, args, env), else: {nil, [], []}

      %{t: :appl, bounds: bounds, args: [body | _]} ->
        case sel do
          :null ->
            syms = Enum.flat_map(bounds, fn {ss, _} -> List.wrap(ss) end)
            select(body, rest, params ++ syms, args ++ snodes, env)

          _ ->
            select(sel_pick(sel, Enum.map(bounds, &elem(&1, 1))), rest, params, args, env)
        end

      %{t: :appl, unbounded: syms, args: [body]} when sel == :null ->
        select(body, rest, params ++ syms, args ++ snodes, env)

      %{t: :appl, op: %{name: "$Case"}, args: pairs} ->
        case {sel_pick(sel, pairs), rest} do
          {%{args: [c, v]}, [{j, _} | rest2]} ->
            case sel_num(j, 2) do
              1 -> select(c, rest2, params, args, env)
              2 -> select(v, rest2, params, args, env)
              _ -> {nil, [], []}
            end

          _ ->
            {nil, [], []}
        end

      %{t: :appl, op: %{name: rn}, args: pairs} when rn in ["$RcdConstructor", "$SetOfRcds"] ->
        case sel_pick(sel, pairs) do
          %{args: [_, v]} -> select(v, rest, params, args, env)
          _ -> {nil, [], []}
        end

      %{t: :appl, args: list} ->
        select(sel_pick(sel, list), rest, params, args, env)

      _ ->
        {nil, [], []}
    end
  end

  defp skip_labels(%{t: :label, body: body}), do: skip_labels(body)
  defp skip_labels(n), do: n

  defp let_def(%{t: :label, body: body}, name), do: let_def(body, name)
  defp let_def(%{t: :let, defs: defs}, name), do: Enum.find(defs, &(&1.name == name))
  defp let_def(_, _name), do: nil

  defp sel_pick(sel, list) do
    case sel_num(sel, length(list)) do
      -1 -> nil
      n -> Enum.at(list, n - 1)
    end
  end

  # SANY's ArgNum: the operand of a selector (from 1), or -1.
  defp sel_num(n, arity) when is_integer(n), do: if(n >= 1 and n <= arity, do: n, else: -1)
  defp sel_num(:ll, arity), do: if(arity > 0, do: 1, else: -1)
  defp sel_num(:gg, 2), do: 2
  defp sel_num(_, _), do: -1

  # `Op!lab(a, b)`: the label exists and has as many parameters.
  defp check_selector_labels(d, [{lab, largs} | _], pos) when is_binary(lab) do
    case find_label(d[:body], lab) do
      nil ->
        :ok

      %{params: params} ->
        if largs != [] and length(largs) != length(params),
          do: err(4337, pos, "Label `#{lab}' used with wrong number of arguments.")
    end
  end

  defp check_selector_labels(_d, _segs, _pos), do: :ok

  defp find_label(%{t: :label, name: name} = l, name), do: l
  defp find_label(%{t: :label}, _name), do: nil
  defp find_label(%{t: :appl, args: args}, name), do: Enum.find_value(args, &find_label(&1, name))
  defp find_label(%{t: :let, body: body}, name), do: find_label(body, name)
  defp find_label(_, _name), do: nil
end
