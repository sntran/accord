defmodule Accord.TLA.Checker.Context do
  @moduledoc """
  Loads a root module and the modules it uses, and builds the name scopes.

  Each module has its own scope. A definition is evaluated in the scope of
  the module that defines it, so a `LOCAL` definition of a module is
  visible to the definitions of that module but not to the modules that
  extend it.

  A scope maps a name to an entry:

  - `{:def, definition, scope_id}` — a user definition
  - `{:native, module, name}` — an operator of a standard module
  - `{:const, name}` — a constant of the root module (its value comes
    from the config)
  - `{:var, index}` — a variable of the root module
  - `{:subst, expr, outer_scope_id, frame}` — a constant or a variable of
    an instantiated module, replaced by an expression of the module that
    instantiates it
  - `{:instance, scope_id, params, frame}` — a named instance `M == INSTANCE ...`
  - `{:alias, scope_id, name}` — a definition replaced in the config
    (`Op <- Other`)
  - `{:value, value}` — a definition replaced by a value in the config

  `EXTENDS` shares the constants and variables: the root module and every
  module that it extends use the same constants and variables. Each
  `INSTANCE` has its own substitutions.

  Standard modules (`Naturals`, `Integers`, `Sequences`, `FiniteSets`,
  `Bags`, `TLC`, ...) are native: `Accord.TLA.Checker.Stdlib` gives their
  operators. Other modules are files: `Name.tla` in the directory of the
  root module, or in a directory of the `:paths` option.
  """

  alias Accord.TLA.Checker.{Community, Config, Parser, Stdlib, Value}

  defmodule Error do
    @moduledoc "An error while loading modules."
    defexception [:message]
  end

  defmodule Scope do
    @moduledoc "The names that a module can see."
    # `exports`: for an instance, the entries that `I!Op` gives when they
    # differ from `ops`. A config replacement changes the names that the
    # module uses, but not `I!Op` (as in TLC, where an instance has its
    # own copies of the definitions).
    defstruct [:id, :module, ops: %{}, public: %{}, exports: %{}]
  end

  defstruct id: nil,
            scopes: %{},
            root: nil,
            root_module: nil,
            variables: {},
            var_index: %{},
            constants: %{},
            config: nil,
            modules: %{},
            assumes: [],
            paths: [],
            root_scopes: MapSet.new(),
            let_instances: %{}

  @type t :: %__MODULE__{}

  @doc """
  Loads the module in `path` with the config in `config`.

  Options: `:paths` — more directories to search for modules.
  """
  def load(path, %Config{} = config, opts \\ []) do
    dir = Path.dirname(path)
    paths = [dir | Keyword.get(opts, :paths, [])] |> Enum.uniq()
    root_mod = parse_file(path)

    state = %{
      modules: %{root_mod.name => root_mod},
      paths: paths,
      scopes: %{},
      next_id: 0,
      cache: %{},
      variables: [],
      assumes: [],
      root_scopes: MapSet.new(),
      let_instances: %{}
    }

    # The variables of the root module: its own and those of the modules
    # it extends, in order.
    {vars, state} = root_variables(root_mod, state, MapSet.new())
    var_index = vars |> Enum.with_index() |> Map.new()
    state = %{state | variables: vars}

    {root_id, state} = build_scope(root_mod.name, {:root, var_index}, state)

    ctx = %__MODULE__{
      id: make_ref(),
      scopes: state.scopes,
      root: root_id,
      root_module: root_mod.name,
      variables: List.to_tuple(vars),
      var_index: var_index,
      config: config,
      modules: state.modules,
      assumes: state.assumes,
      paths: paths,
      root_scopes: state.root_scopes,
      let_instances: state.let_instances
    }

    ctx
    |> apply_constants(config)
  end

  defp parse_file(path) do
    Parser.parse_module(File.read!(path), file: path)
  rescue
    e in File.Error -> raise Error, message: "cannot read #{path}: #{Exception.message(e)}"
  end

  # Finds a module by name: a submodule already seen, a file on the path,
  # or a standard module.
  defp fetch_module(name, state) do
    cond do
      Map.has_key?(state.modules, name) ->
        {Map.fetch!(state.modules, name), state}

      Stdlib.native?(name) ->
        {:native, state}

      path = Enum.find_value(state.paths, &existing(Path.join(&1, name <> ".tla"))) ->
        mod = parse_file(path)
        modules = Map.put(state.modules, name, mod)
        modules = Enum.reduce(mod.submodules, modules, &Map.put_new(&2, &1.name, &1))
        {mod, %{state | modules: modules}}

      true ->
        raise Error,
          message: "cannot find module #{name} (searched #{Enum.join(state.paths, ", ")})"
    end
  end

  defp existing(path), do: if(File.exists?(path), do: path)

  defp root_variables(mod, state, seen) do
    state = register_submodules(mod, state)

    Enum.reduce(mod.extends, {[], state}, fn name, {vars, state} ->
      if MapSet.member?(seen, name) do
        {vars, state}
      else
        case fetch_module(name, state) do
          {:native, state} ->
            {vars, state}

          {ext, state} ->
            {ext_vars, state} = root_variables(ext, state, MapSet.put(seen, name))
            {vars ++ (ext_vars -- vars), state}
        end
      end
    end)
    |> then(fn {vars, state} -> {vars ++ (mod.variables -- vars), state} end)
  end

  defp register_submodules(mod, state) do
    modules = Enum.reduce(mod.submodules, state.modules, &Map.put_new(&2, &1.name, &1))
    %{state | modules: modules}
  end

  # Builds the scope of a module for a substitution context. `subst` is
  # `{:root, var_index}` for the root module and the modules it extends,
  # or `{:inst, id, entries}` for an instance (entries: name -> entry).
  defp build_scope(name, subst, state) do
    key = {name, subst_key(subst)}

    case Map.fetch(state.cache, key) do
      {:ok, id} ->
        {id, state}

      :error ->
        {id, state} = new_id(state)
        state = %{state | cache: Map.put(state.cache, key, id)}

        state =
          if match?({:root, _}, subst),
            do: %{state | root_scopes: MapSet.put(state.root_scopes, id)},
            else: state

        case fetch_module(name, state) do
          {:native, state} ->
            ops = Stdlib.ops(name)
            scope = %Scope{id: id, module: name, ops: ops, public: ops}
            {id, put_scope(state, scope)}

          {mod, state} ->
            state = register_submodules(mod, state)
            {scope, state} = module_scope(mod, id, subst, state)
            {id, put_scope(state, scope)}
        end
    end
  end

  defp subst_key({:root, _}), do: :root
  defp subst_key({:inst, id, _, _}), do: id

  defp new_id(state), do: {state.next_id, %{state | next_id: state.next_id + 1}}

  defp put_scope(state, scope), do: %{state | scopes: Map.put(state.scopes, scope.id, scope)}

  defp module_scope(mod, id, subst, state) do
    # 0. A module inside another module sees the names of the outer one.
    inherited =
      case subst do
        {:inst, _, _, outer_ops} when mod.outer != nil -> outer_ops
        _ -> %{}
      end

    # 1. EXTENDS: the public names of each extended module.
    {ops, state} =
      Enum.reduce(mod.extends, {inherited, state}, fn ext, {ops, state} ->
        {ext_id, state} = build_scope(ext, subst, state)
        {Map.merge(ops, Map.fetch!(state.scopes, ext_id).public), state}
      end)

    public = ops

    # 2. Constants and variables.
    decls =
      Enum.map(mod.constants, fn {c, _arity} -> {c, decl_entry(c, :const, subst)} end) ++
        Enum.map(mod.variables, fn v -> {v, decl_entry(v, :var, subst)} end)

    ops = Map.merge(ops, Map.new(decls))
    public = Map.merge(public, Map.new(decls))

    # The assumptions of the root module and its extensions.
    state =
      case subst do
        {:root, _} ->
          %{
            state
            | assumes: state.assumes ++ Enum.map(mod.assumes, fn {e, pos} -> {e, id, pos} end)
          }

        _ ->
          state
      end

    # 3. Definitions and instances, in order.
    {ops, public, state} =
      Enum.reduce(mod.units, {ops, public, state}, fn unit, {ops, public, state} ->
        unit_entries(unit, id, ops, public, state)
      end)

    {ops, public} = native_overrides(mod.name, ops, public)
    {%Scope{id: id, module: mod.name, ops: ops, public: public}, state}
  end

  # The operators of a community module that have native code (see
  # `Accord.TLA.Checker.Community`).
  defp native_overrides(module, ops, public) do
    Enum.reduce(Community.ops(module), {ops, public}, fn {name, _}, {ops, public} ->
      case Map.get(ops, name) do
        {:def, _, _} ->
          entry = {:native, module, name}

          {Map.put(ops, name, entry),
           if(Map.has_key?(public, name), do: Map.put(public, name, entry), else: public)}

        _ ->
          {ops, public}
      end
    end)
  end

  defp decl_entry(name, :const, {:root, _}), do: {:const, name}
  defp decl_entry(name, :var, {:root, index}), do: {:var, Map.fetch!(index, name)}

  defp decl_entry(name, _kind, {:inst, _id, entries, _}) do
    Map.get(entries, name) || raise Error, message: "no substitution for #{name}"
  end

  defp unit_entries(%{kind: kind} = def, id, ops, public, state) when kind in [:op, :fun] do
    entry = {:def, def, id}
    ops = Map.put(ops, def.name, entry)
    public = if def.local, do: public, else: Map.put(public, def.name, entry)
    state = def.body |> let_instances([]) |> Enum.reduce(state, &let_instance(&1, id, &2, ops))
    {ops, public, state}
  end

  defp unit_entries(%{kind: :instance} = inst, id, ops, public, state) do
    {inst_id, frame, state} = instance_scope(inst, id, state, ops)

    case inst.name do
      nil ->
        # `INSTANCE M` imports the definitions of M, not its constants
        # and variables (the substitutions replace them).
        inst_public =
          state.scopes
          |> Map.fetch!(inst_id)
          |> Map.fetch!(:public)
          |> Map.reject(fn {_, entry} -> match?({:subst, _, _, _}, entry) end)

        ops = Map.merge(ops, inst_public)
        public = if inst.local, do: public, else: Map.merge(public, inst_public)
        {ops, public, state}

      name ->
        entry = {:instance, inst_id, inst.params, frame}
        ops = Map.put(ops, name, entry)
        public = if inst.local, do: public, else: Map.put(public, name, entry)
        {ops, public, state}
    end
  end

  # The instances in the LET expressions of a definition body. Each one
  # gets a scope; the substitutions see the bound names of the LET, which
  # the evaluation puts in the frame of the instance.
  defp let_instances({:let, defs, body}, acc) do
    acc =
      Enum.reduce(defs, acc, fn
        %{kind: :instance} = inst, acc -> [inst | acc]
        %{body: b}, acc -> let_instances(b, acc)
        _, acc -> acc
      end)

    let_instances(body, acc)
  end

  defp let_instances(t, acc) when is_tuple(t), do: t |> Tuple.to_list() |> let_instances(acc)
  defp let_instances(l, acc) when is_list(l), do: Enum.reduce(l, acc, &let_instances/2)

  defp let_instances(%{} = m, acc) when not is_struct(m),
    do: m |> Map.values() |> let_instances(acc)

  defp let_instances(_, acc), do: acc

  defp let_instance(inst, id, state, ops) do
    {inst_id, frame, state} = instance_scope(inst, id, state, ops)
    %{state | let_instances: Map.put(state.let_instances, {id, inst.pos}, {inst_id, frame})}
  end

  # `outer_ops`: the names of the module that has the INSTANCE. A module
  # inside that module sees them (the names defined before it).
  defp instance_scope(inst, id, state, outer_ops) do
    {target, state} = fetch_module(inst.module, state)
    {frame, state} = new_id(state)

    entries =
      case target do
        :native ->
          %{}

        mod ->
          {consts, vars} = declarations(mod, state, MapSet.new())

          explicit = Map.new(inst.subs)

          Map.new(consts ++ vars, fn n ->
            expr = Map.get(explicit, n, {:name, n, inst.pos})
            {n, {:subst, expr, id, frame}}
          end)
      end

    {inst_id, state} = build_scope(inst.module, {:inst, frame, entries, outer_ops}, state)
    {inst_id, frame, state}
  end

  # The constants and variables of a module and the modules it extends.
  defp declarations(mod, state, seen) do
    Enum.reduce(mod.extends, {Enum.map(mod.constants, &elem(&1, 0)), mod.variables}, fn name,
                                                                                        {cs, vs} ->
      if MapSet.member?(seen, name) do
        {cs, vs}
      else
        case fetch_module(name, state) do
          {:native, _} ->
            {cs, vs}

          {ext, _} ->
            {ecs, evs} = declarations(ext, state, MapSet.put(seen, name))
            {Enum.uniq(cs ++ ecs), Enum.uniq(vs ++ evs)}
        end
      end
    end)
  end

  # -- Constants from the config --

  defp apply_constants(ctx, config) do
    originals =
      Map.new(config.constants, fn
        {:replace, name, _} -> {name, lookup(ctx, ctx.root, name)}
        _ -> {nil, nil}
      end)

    config.constants
    |> Enum.reduce(ctx, &apply_constant/2)
    |> own_names(originals)
  end

  # In the body of a replacement `name <- target`, `name` is the original
  # definition (TLC does not loop when `target` uses `name`). The target
  # gets a scope: the root scope with the original entry of `name`.
  defp own_names(ctx, originals) do
    Enum.reduce(originals, ctx, fn
      {nil, _}, ctx ->
        ctx

      {_name, nil}, ctx ->
        ctx

      {name, original}, ctx ->
        root = Map.fetch!(ctx.scopes, ctx.root)
        id = ctx.scopes |> Map.keys() |> Enum.max() |> Kernel.+(1)
        # The definitions of the root module in the copy have the copy as
        # their scope, so that the body of `target` sees the original.
        ops =
          Map.new(root.ops, fn
            {k, {:def, d, sid}} when sid == ctx.root -> {k, {:def, d, id}}
            other -> other
          end)

        copy = %{root | id: id, ops: Map.put(ops, name, original)}

        scopes =
          ctx.scopes
          |> Map.put(id, copy)
          |> Map.new(fn {sid, scope} ->
            case Map.get(scope.ops, name) do
              {:alias, sid0, target} when sid0 == ctx.root and sid != id ->
                entry = {:alias, id, target}

                {sid,
                 %{
                   scope
                   | ops: Map.put(scope.ops, name, entry),
                     public: maybe_put(scope.public, name, entry)
                 }}

              _ ->
                {sid, scope}
            end
          end)

        let_instances =
          for {{sid, pos}, v} <- ctx.let_instances,
              sid == ctx.root,
              into: ctx.let_instances,
              do: {{id, pos}, v}

        %{
          ctx
          | scopes: scopes,
            root_scopes: MapSet.put(ctx.root_scopes, id),
            let_instances: let_instances
        }
    end)
  end

  defp apply_constant(c, ctx) do
    case c do
      {:value, name, value} ->
        value = config_value(value)

        if constant?(ctx, name) do
          %{ctx | constants: Map.put(ctx.constants, name, value)}
        else
          # A config value for a definition replaces the definition.
          override(ctx, name, {:value, value}, :root)
        end

      {:replace, name, target} ->
        override(ctx, name, {:alias, ctx.root, target}, :root)

      {:op_case, name, args, value} ->
        key = Value.tuple(Enum.map(args, &config_value/1))

        table =
          case Map.get(ctx.constants, name) do
            {:op_table, t} -> t
            _ -> %{}
          end

        %{
          ctx
          | constants:
              Map.put(ctx.constants, name, {:op_table, Map.put(table, key, config_value(value))})
        }

      {:module_value, mod, name, value} ->
        override(ctx, name, {:value, config_value(value)}, {:module, mod})

      {:module_replace, mod, name, target} ->
        # `name <-[mod] target`: `name` in the module `mod`; `target` is a
        # definition of the root module.
        override(ctx, name, {:alias, ctx.root, target}, {:module, mod})
    end
  end

  defp constant?(ctx, name) do
    match?({:const, _}, ctx.scopes |> Map.fetch!(ctx.root) |> Map.fetch!(:ops) |> Map.get(name))
  end

  @doc false
  def config_value({:set, elems}), do: Value.set(Enum.map(elems, &config_value/1))
  def config_value(v), do: v

  # Replaces `name` in every scope of the root context (or of one module).
  # When `name` is a definition, the replacement is for the definition, so
  # it applies also where an instance or another module uses it (as in
  # TLC, where the replacement goes on the definition itself).
  defp override(ctx, name, entry, where) do
    root_def = lookup(ctx, ctx.root, name)

    scopes =
      Map.new(ctx.scopes, fn {id, scope} ->
        applies =
          case where do
            :root ->
              Map.has_key?(scope.ops, name) and
                (root_context?(ctx, scope) or
                   same_definition?(ctx, Map.get(scope.ops, name), root_def))

            {:module, mod} ->
              scope.module == mod and Map.has_key?(scope.ops, name)
          end

        if applies do
          exports =
            if root_context?(ctx, scope),
              do: scope.exports,
              else: Map.put_new(scope.exports, name, Map.get(scope.ops, name))

          {id,
           %{
             scope
             | ops: Map.put(scope.ops, name, entry),
               public: maybe_put(scope.public, name, entry),
               exports: exports
           }}
        else
          {id, scope}
        end
      end)

    %{ctx | scopes: scopes}
  end

  defp same_definition?(_ctx, {:native, m, n}, {:native, m, n}), do: true

  defp same_definition?(ctx, {:def, d1, s1}, {:def, d2, s2}),
    do:
      d1.name == d2.name and d1.pos == d2.pos and
        Map.fetch!(ctx.scopes, s1).module == Map.fetch!(ctx.scopes, s2).module

  defp same_definition?(_ctx, _a, _b), do: false

  defp maybe_put(map, key, value),
    do: if(Map.has_key?(map, key), do: Map.put(map, key, value), else: map)

  # A scope of the root module or of a module that it extends (not an
  # instance).
  defp root_context?(ctx, scope), do: MapSet.member?(ctx.root_scopes, scope.id)

  @doc "Looks up a name in a scope."
  def lookup(%__MODULE__{scopes: scopes}, scope_id, name) do
    scopes |> Map.fetch!(scope_id) |> Map.fetch!(:ops) |> Map.get(name)
  end

  @doc "The entry of `I!name`, where `scope_id` is the scope of the instance `I`."
  def export(%__MODULE__{scopes: scopes}, scope_id, name) do
    scope = Map.fetch!(scopes, scope_id)
    Map.get(scope.exports, name) || Map.get(scope.ops, name)
  end

  @doc "The definition of a name in the root scope."
  def root_entry(ctx, name), do: lookup(ctx, ctx.root, name)
end
