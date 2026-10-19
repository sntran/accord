defmodule Accord.TLA.Checker.Eval do
  @moduledoc """
  Evaluates TLA+ expressions, and generates states from actions.

  ## Evaluation

  `eval/2` gives the value of an expression in an environment. The
  environment has the current state, the next state (for primed
  variables), the bound variables, and the scope of the definition that
  is being evaluated.

  An operator argument that is not a literal or a bound variable is
  passed lazily, as a thunk: TLA+ operators substitute their arguments, so
  `Op(v) == v'` primes the expression of its argument. A thunk that is
  made during an evaluation is evaluated at most one time for each prime
  level.

  ## Generation

  `gen/3` generates the assignments that an action allows, with the
  rules of TLC:

  - In a conjunction, the conjuncts run from left to right.
  - `x' = e` assigns `x'` when it has no value yet. Otherwise it is a
    condition. `x' \\in S` assigns each element of `S`, one branch for
    each element.
  - `UNCHANGED e` assigns each variable of `e` its current value.
  - A disjunction and `\\E` give one branch for each alternative.
  - Any other expression is a condition.

  The same rules generate the initial states (with unprimed variables).

  Each generated step has the name of its action: the last definition
  that the generation entered before it reached a conjunction, as TLC
  names the actions of `Next`.
  """

  alias Accord.TLA.Checker.{Community, Constant, Context, Stdlib, Value}
  import Value, only: [error: 1]

  defstruct [
    :ctx,
    :scope,
    bound: %{},
    state: nil,
    next: nil,
    primed: false,
    at: nil,
    frames: %{},
    gen: false,
    label: nil,
    label_mode: false,
    level: 1,
    # In ENABLED: a variable of an instance that a substitution replaces
    # with an expression can take a value as a pseudo variable, as in TLC.
    pseudo: false
  ]

  @core ~w(= /= \\in \\notin \\subseteq \\cup \\cap \\ SUBSET UNION DOMAIN)

  @doc "A new environment for the root scope of a context."
  def new(ctx, opts \\ []) do
    %__MODULE__{
      ctx: ctx,
      scope: ctx.root,
      state: Keyword.get(opts, :state),
      next: Keyword.get(opts, :next),
      level: Keyword.get(opts, :level, 1)
    }
  end

  @doc "Clears the cache of thunk values. The checker calls it between states."
  def reset_cache, do: Process.put(:tla_thunk_cache, %{})

  # -- Evaluation --

  @doc "Evaluates an expression."
  def eval({:value, v}, _env), do: v
  def eval({:num, n}, _env), do: n
  def eval({:str, s}, _env), do: s
  def eval({:dec, d}, _env), do: error("real numbers are not supported: #{d}")
  def eval({:name, n, _}, env), do: name(n, env)

  # `A \cdot B` on a step: some middle state that A reaches and from
  # which B reaches the next state.
  def eval({:app, "\\cdot", [a, b], _}, env) do
    nvars = tuple_size(env.ctx.variables)

    a
    |> gen(%{env | next: %{}}, :next)
    |> Enum.any?(fn {m, _} ->
      map_size(m) == nvars and
        bool(b, %{
          env
          | state: List.to_tuple(for(i <- 0..(nvars - 1)//1, do: Map.fetch!(m, i))),
            gen: false
        })
    end)
  end

  def eval({:app, op, args, _}, env) when op in @core, do: core(op, args, env)
  def eval({:app, op, args, _}, env), do: call(op, args, env)

  def eval({:and, items}, env) do
    Enum.reduce_while(items, true, fn item, _ ->
      if bool(item, env), do: {:cont, true}, else: {:halt, false}
    end)
  end

  def eval({:or, items}, env) do
    Enum.reduce_while(items, false, fn item, _ ->
      if bool(item, env), do: {:halt, true}, else: {:cont, false}
    end)
  end

  def eval({:not, e}, env), do: not bool(e, env)
  def eval({:implies, a, b}, env), do: not bool(a, env) or bool(b, env)
  def eval({:equiv, a, b}, env), do: bool(a, env) == bool(b, env)

  def eval({:if, c, a, b}, env), do: if(bool(c, env), do: eval(a, env), else: eval(b, env))

  def eval({:case, arms, other}, env) do
    case Enum.find(arms, fn {c, _} -> bool(c, env) end) do
      {_, e} -> eval(e, env)
      nil when other != nil -> eval(other, env)
      nil -> error("no arm of a CASE is true, and the CASE has no OTHER")
    end
  end

  def eval({:let, defs, body}, env), do: eval(body, let_env(defs, env))
  def eval({:label, _, e}, env), do: eval(e, env)

  def eval({:forall, binds, body}, env) do
    each_binding(binds, env, true, fn env2, _acc ->
      if bool(body, env2), do: {:cont, true}, else: {:halt, false}
    end)
  end

  def eval({:exists, binds, body}, env) do
    each_binding(binds, env, false, fn env2, _acc ->
      if bool(body, env2), do: {:halt, true}, else: {:cont, false}
    end)
  end

  def eval({:choose, {target, set}, body}, env) do
    if set == nil, do: error("TLC cannot evaluate an unbounded CHOOSE")

    values = set |> eval(env) |> Value.enum() |> Value.sort()

    case Enum.find(values, &bool(body, bind(env, target, &1))) do
      nil -> error("no element of the set satisfies the CHOOSE")
      v -> v
    end
  end

  def eval({:set, elems}, env), do: Value.set(Enum.map(elems, &eval(&1, env)))

  def eval({:set_map, e, binds}, env) do
    binds
    |> each_binding(env, [], fn env2, acc -> {:cont, [eval(e, env2) | acc]} end)
    |> Value.set()
  end

  def eval({:set_filter, {target, set}, pred}, env) do
    s = eval(set, env)

    if Value.infinite?(s) do
      frozen = freeze(env)
      {:filter, s, fn x -> bool(pred, bind(frozen, target, x)) end}
    else
      s
      |> Value.enum()
      |> Enum.filter(&bool(pred, bind(env, target, &1)))
      |> Value.set()
    end
  end

  def eval({:tuple, elems}, env), do: Value.tuple(Enum.map(elems, &eval(&1, env)))

  def eval({:func, binds, body}, env) do
    {domain, keys} = fun_domain(binds, env)

    case keys do
      {:ok, keys} ->
        keys
        |> Map.new(fn k -> {k, eval(body, bind_key(env, binds, k))} end)
        |> Value.fun()

      :infinite ->
        frozen = freeze(env)
        {:lazy_fun, domain, fn k -> eval(body, bind_key(frozen, binds, k)) end}
    end
  end

  def eval({:apply, f, args}, env) do
    fv = eval(f, env)

    arg =
      case args do
        [a] -> eval(a, env)
        many -> Value.tuple(Enum.map(many, &eval(&1, env)))
      end

    Value.apply_fun(fv, arg)
  end

  def eval({:dot, e, field}, env) do
    case eval(e, env) do
      {:fun, m} = r ->
        case Map.fetch(m, field) do
          {:ok, v} -> v
          :error -> error("the record #{Value.show(r)} has no field #{field}")
        end

      other ->
        error("`.#{field}` needs a record, not #{Value.show(other)}")
    end
  end

  def eval({:record, fields}, env),
    do: Value.record(Enum.map(fields, fn {f, e} -> {f, eval(e, env)} end))

  def eval({:record_set, fields}, env),
    do: {:record_set, Enum.map(fields, fn {f, e} -> {f, eval(e, env)} end)}

  def eval({:fun_set, d, r}, env), do: {:fun_set, eval(d, env), eval(r, env)}
  def eval({:times, sets}, env), do: {:times, Enum.map(sets, &eval(&1, env))}

  def eval({:except, f, updates}, env) do
    Enum.reduce(updates, eval(f, env), fn {path, value}, acc ->
      except_path(acc, path, value, env)
    end)
  end

  def eval({:at}, %{at: nil}), do: error("`@` outside of EXCEPT")
  def eval({:at}, %{at: {:at, v}}), do: v

  def eval({:prime, _e}, %{primed: true}), do: error("a primed expression cannot be primed again")
  def eval({:prime, e}, env), do: eval(e, %{env | primed: true})

  def eval({:unchanged, e}, env) do
    if env.primed, do: error("UNCHANGED inside a primed expression")
    Value.eq?(eval(e, %{env | primed: true}), eval(e, env))
  end

  def eval({:enabled, a}, env), do: enabled?(a, env)

  def eval({:box_action, a, sub}, env) do
    bool(a, env) or Value.eq?(eval(sub, %{env | primed: true}), eval(sub, env))
  end

  def eval({:diamond_action, a, sub}, env) do
    bool(a, env) and not Value.eq?(eval(sub, %{env | primed: true}), eval(sub, env))
  end

  def eval({:inst, path, name, args, _}, env) do
    {target, env2} = navigate(path, name, env)
    invoke_entry(target, name, args, env, env2)
  end

  def eval({:op_arg, op}, _env), do: error("the operator #{op} is used as a value")
  def eval({:lambda, _, _}, _env), do: error("LAMBDA is used as a value")

  def eval({kind, _}, _env) when kind in [:always, :eventually],
    do: error("a temporal formula cannot be evaluated as a value")

  def eval({kind, _, _}, _env) when kind in [:leadsto, :wf, :sf],
    do: error("a temporal formula cannot be evaluated as a value")

  def eval(other, _env), do: error("cannot evaluate #{inspect(other)}")

  @doc "Evaluates an expression that must be a boolean."
  def bool(e, env) do
    case eval(e, env) do
      b when is_boolean(b) -> b
      other -> error("expected a boolean, not #{Value.show(other)}")
    end
  end

  # -- Core operators --

  defp core("=", [a, b], env), do: Value.eq?(eval(a, env), eval(b, env))
  defp core("/=", [a, b], env), do: not Value.eq?(eval(a, env), eval(b, env))
  defp core("\\in", [a, b], env), do: Value.member?(eval(a, env), eval(b, env))
  defp core("\\notin", [a, b], env), do: not Value.member?(eval(a, env), eval(b, env))
  defp core("\\subseteq", [a, b], env), do: Value.subseteq?(eval(a, env), eval(b, env))
  defp core("\\cup", [a, b], env), do: Value.union(eval(a, env), eval(b, env))
  defp core("\\cap", [a, b], env), do: Value.intersection(eval(a, env), eval(b, env))
  defp core("\\", [a, b], env), do: Value.difference(eval(a, env), eval(b, env))
  defp core("SUBSET", [a], env), do: {:subset, eval(a, env)}

  defp core("UNION", [a], env) do
    a
    |> eval(env)
    |> Value.enum()
    |> Enum.reduce(MapSet.new(), &MapSet.union(&2, Value.to_set(&1)))
  end

  defp core("DOMAIN", [a], env), do: Value.domain(eval(a, env))

  # -- Names and operator calls --

  defp name("TRUE", _env), do: true
  defp name("FALSE", _env), do: false

  defp name(n, env) do
    case Map.fetch(env.bound, n) do
      {:ok, v} ->
        bound_value(v, n, env)

      :error ->
        case Context.lookup(env.ctx, env.scope, n) do
          nil -> builtin_name(n, env)
          entry -> invoke_entry(entry, n, [], env, env)
        end
    end
  end

  defp builtin_name("BOOLEAN", _env), do: MapSet.new([false, true])
  defp builtin_name("STRING", _env), do: :string

  defp builtin_name(n, env) do
    if Stdlib.fallback?(n), do: Stdlib.call(n, [], env), else: error("unknown name #{n}")
  end

  defp bound_value({:thunk, _, _, _, _, _, _} = t, _n, env), do: force(t, env)

  defp bound_value({:let_def, %{kind: :op, params: []} = d, closure}, n, env),
    do: let_value(d, n, closure, env)

  defp bound_value({:let_def, %{kind: :fun} = d, closure}, n, env),
    do:
      fun_def_value(d, %{
        env
        | scope: closure.scope,
          bound: Map.put(closure.bound, n, {:let_def, d, closure}),
          frames: closure.frames
      })

  defp bound_value({:let_def, _d, _}, n, _env), do: error("the operator #{n} needs arguments")
  defp bound_value({:op_value, _, 0, _} = op, _n, env), do: apply_op(op, [], env)
  defp bound_value({:op_value, n, _, _}, _n, _env), do: error("the operator #{n} needs arguments")
  defp bound_value(v, _n, _env), do: v

  # A zero-arity LET definition, cached in evaluation.
  defp let_value(d, n, closure, env) do
    callee = %{
      env
      | scope: closure.scope,
        bound: Map.put(closure.bound, n, {:let_def, d, closure}),
        frames: closure.frames
    }

    if env.gen or closure.ref == nil do
      eval(d.body, callee)
    else
      cached({closure.ref, n, env.primed}, fn -> eval(d.body, callee) end)
    end
  end

  defp call(op, args, env) do
    case Map.fetch(env.bound, op) do
      {:ok, {:let_def, d, closure}} ->
        call_let(d, op, closure, prepare(args, d.params, env), env)

      {:ok, {:op_value, _, _, _} = opv} ->
        apply_op(opv, Enum.map(args, &arg_value(&1, env)), env)

      {:ok, other} ->
        if args == [], do: other, else: error("#{op} is not an operator")

      :error ->
        case Context.lookup(env.ctx, env.scope, op) do
          nil ->
            if Stdlib.fallback?(op),
              do: Stdlib.call(op, prepare_native(op, args, env), env),
              else: error("unknown operator #{op}")

          entry ->
            invoke_entry(entry, op, args, env, env)
        end
    end
  end

  # Calls a scope entry. `args` are expressions of the caller (`caller`);
  # `env` is where the entry is (for an instance path, the instance).
  defp invoke_entry(entry, name, args, caller, env) do
    case entry do
      # A definition of constant level: one evaluation (as TLC, which
      # evaluates them before the search).
      {:def, %{kind: :op, params: []} = d, sid} when args == [] ->
        if Constant.definition?(env.ctx, sid, d),
          do: constant_value(d, sid, env),
          else: eval(d.body, %{env | scope: sid, bound: %{}})

      {:def, %{kind: :op} = d, sid} ->
        values = prepare(args, d.params, caller)
        eval(d.body, %{env | scope: sid, bound: param_map(d, values)})

      {:def, %{kind: :fun} = d, sid} ->
        if args != [], do: error("the function #{name} is applied with ( ), not [ ]")
        fun_def_value(d, %{env | scope: sid, bound: %{}})

      {:native, mod, op} ->
        Stdlib.call_native(mod, op, prepare_native(op, args, caller, mod), env)

      {:const, c} ->
        case Map.fetch(env.ctx.constants, c) do
          {:ok, {:op_table, table}} when args != [] ->
            key = Value.tuple(Enum.map(args, &eval(&1, caller)))

            case Map.fetch(table, key) do
              {:ok, v} -> v
              :error -> error("the config gives no value for #{c} at #{Value.show(key)}")
            end

          {:ok, v} when args == [] ->
            v

          {:ok, _} ->
            error("the constant #{c} is not an operator")

          :error ->
            error("the constant #{c} has no value in the config")
        end

      {:var, i} ->
        if args != [], do: error("the variable #{name} is not an operator")
        read_var(i, env)

      {:value, v} ->
        v

      {:alias, sid, target} ->
        case Context.lookup(env.ctx, sid, target) do
          nil -> error("the config replaces #{name} with #{target}, which is not defined")
          target_entry -> invoke_entry(target_entry, target, args, caller, %{env | scope: sid})
        end

      {:subst, expr, outer, frame} ->
        outer_env = %{env | scope: outer, bound: Map.get(env.frames, frame, %{})}

        case {args, expr} do
          {[], _} ->
            # A pseudo variable (see `:pseudo`) that ENABLED gave a value.
            key = {:pseudo, env.scope, name}

            if env.primed and is_map(env.next) and Map.has_key?(env.next, key),
              do: Map.fetch!(env.next, key),
              else: eval(expr, outer_env)

          {_, {:name, g, _}} ->
            invoke_named(g, args, caller, outer_env)

          {_, {:op_arg, sym}} ->
            invoke_named(sym, args, caller, outer_env)

          {_, {:lambda, _, _} = l} ->
            apply_op(op_value(l, outer_env), Enum.map(args, &arg_value(&1, caller)), env)

          _ ->
            error("cannot apply the substitution for #{name}")
        end

      {:instance, _, _, _} ->
        error("the instance #{name} is used without `!`")
    end
  end

  defp constant_value(d, sid, env) do
    key = {env.ctx.id, sid, d.name}

    case Map.fetch(Process.get(:tla_constants) || %{}, key) do
      {:ok, v} ->
        v

      :error ->
        v = eval(d.body, %{env | scope: sid, bound: %{}, state: nil, next: nil, primed: false, gen: false})
        Process.put(:tla_constants, Map.put(Process.get(:tla_constants) || %{}, key, v))
        v
    end
  end

  defp invoke_named(name, args, caller, env) do
    if name in @core do
      core(name, Enum.map(args, &value_expr(&1, caller)), env)
    else
      case Context.lookup(env.ctx, env.scope, name) do
        nil -> Stdlib.call(name, prepare_native(name, args, caller), env)
        entry -> invoke_entry(entry, name, args, caller, env)
      end
    end
  end

  # An already evaluated value as an expression.
  defp value_expr(e, env), do: {:value, eval(e, env)}

  defp param_map(d, values), do: param_map(d.params, values, %{})

  defp param_map([{name, _} | params], [v | values], acc),
    do: param_map(params, values, Map.put(acc, name, v))

  defp param_map([], [], acc), do: acc

  defp call_let(d, name, closure, values, env) do
    bound =
      closure.bound
      |> Map.put(name, {:let_def, d, closure})
      |> Map.merge(param_map(d, values))

    eval(d.body, %{env | scope: closure.scope, bound: bound, frames: closure.frames})
  end

  # Arguments for the parameters of a user definition: operators for
  # operator parameters, and values or thunks for the others.
  defp prepare([arg | args], [{_name, arity} | params], env) do
    v = if arity == 0, do: lazy(arg, env), else: op_value(arg, env)
    [v | prepare(args, params, env)]
  end

  defp prepare([], [], _env), do: []

  defp prepare(args, params, _env),
    do: error("wrong number of arguments: #{length(args)} for #{length(params)}")

  defp prepare_native(op, args, env, mod \\ nil)

  # AssertError(msg, e) is true when e fails to evaluate; the checker does
  # not compare its error text with the text of TLC.
  defp prepare_native("AssertError", [msg, e], env, _mod) do
    failed =
      try do
        eval(e, env)
        false
      rescue
        Value.Error -> true
      end

    [eval(msg, env), failed]
  end

  defp prepare_native(op, args, env, mod) do
    case Community.op_params(mod, op) || Stdlib.op_params(op) do
      nil -> eval_all(args, env)
      arities -> native_args(args, arities, env)
    end
  end

  defp eval_all([a | rest], env), do: [eval(a, env) | eval_all(rest, env)]
  defp eval_all([], _env), do: []

  defp native_args([a | rest], [0 | arities], env),
    do: [eval(a, env) | native_args(rest, arities, env)]

  defp native_args([a | rest], [_ | arities], env),
    do: [op_value(a, env) | native_args(rest, arities, env)]

  defp native_args(rest, [], env), do: eval_all(rest, env)
  defp native_args([], _, _env), do: []

  defp lazy({:num, n}, _env), do: n
  defp lazy({:str, s}, _env), do: s
  defp lazy({:value, v}, _env), do: v

  defp lazy({:name, n, _} = e, env) do
    case Map.fetch(env.bound, n) do
      {:ok, {:let_def, _, _}} -> thunk(e, env)
      {:ok, {:op_value, _, _, _}} -> thunk(e, env)
      {:ok, v} -> v
      :error -> thunk(e, env)
    end
  end

  defp lazy(e, env), do: thunk(e, env)

  defp thunk(e, env), do: {:thunk, make_ref(), e, env.scope, env.bound, env.frames, not env.gen}

  defp force({:thunk, ref, e, scope, bound, frames, cacheable}, env) do
    env2 = %{env | scope: scope, bound: bound, frames: frames}

    if cacheable and not env.gen,
      do: cached({ref, env.primed}, fn -> eval(e, env2) end),
      else: eval(e, env2)
  end

  defp cached(key, fun) do
    cache = Process.get(:tla_thunk_cache) || %{}

    case Map.fetch(cache, key) do
      {:ok, v} ->
        v

      :error ->
        v = fun.()
        Process.put(:tla_thunk_cache, Map.put(Process.get(:tla_thunk_cache) || %{}, key, v))
        v
    end
  end

  defp arg_value({:value, v}, _env), do: v

  defp arg_value(arg, env) do
    case arg do
      {:op_arg, _} -> op_value(arg, env)
      {:lambda, _, _} -> op_value(arg, env)
      _ -> eval(arg, env)
    end
  end

  # -- Operator values --

  @doc false
  def op_value({:lambda, params, body}, env),
    do:
      {:op_value, "LAMBDA", length(params),
       {:lambda, params, body, env.scope, env.bound, env.frames}}

  def op_value({:op_arg, sym}, env), do: {:op_value, sym, 2, {:named, sym, env.scope}}

  def op_value({:name, n, _}, env) do
    case Map.fetch(env.bound, n) do
      {:ok, {:op_value, _, _, _} = opv} -> opv
      {:ok, {:let_def, d, closure}} -> {:op_value, n, length(d.params), {:let, d, closure}}
      _ -> {:op_value, n, nil, {:named, n, env.scope}}
    end
  end

  def op_value({:inst, path, name, [], _}, env),
    do: {:op_value, name, nil, {:inst, path, name, env}}

  def op_value(other, _env), do: error("expected an operator argument, not #{inspect(other)}")

  @doc "Applies an operator value to values."
  def apply_op({:op_value, _name, _arity, impl}, values, env) do
    exprs = Enum.map(values, &{:value, &1})

    case impl do
      {:lambda, params, body, scope, bound, frames} ->
        bound = Map.merge(bound, params |> Enum.zip(values) |> Map.new())
        eval(body, %{env | scope: scope, bound: bound, frames: frames})

      {:let, d, closure} ->
        call_let(d, d.name, closure, values, env)

      {:named, name, scope} ->
        env2 = %{env | scope: scope}

        if name in @core,
          do: core(name, exprs, env2),
          else: invoke_named(name, exprs, env2, env2)

      {:inst, path, name, caller} ->
        {target, env2} = navigate(path, name, caller)
        invoke_entry(target, name, exprs, %{caller | state: env.state, next: env.next}, env2)
    end
  end

  # -- Instances --

  # Follows `M!N!Op`: gives the entry of `name` and the environment of
  # the instance.
  defp navigate(path, name, env) do
    {scope_env, entry_owner} =
      Enum.reduce(path, {env, nil}, fn {seg, args}, {cur, owner} ->
        step(seg, args, cur, owner, env)
      end)

    entry =
      case {entry_owner, name} do
        {{:def, d, sid}, n} when is_integer(n) ->
          {:sub_expr, d, sid, n}

        {{:sub_expr, _, _, _} = sub, n} when is_integer(n) ->
          {:sub_expr_of, sub, n}

        _ ->
          Context.lookup(env.ctx, scope_env.scope, name) ||
            error("#{name} is not defined in the instance")
      end

    {sub_entry(entry, env), scope_env}
  end

  defp step(seg, args, cur, _owner, caller) do
    entry =
      case Map.fetch(cur.bound, seg) do
        {:ok, {:let_instance, _, _, _} = li} -> li
        _ -> Context.lookup(cur.ctx, cur.scope, seg)
      end

    case entry do
      {:let_instance, sid, frame, bound} when args == [] ->
        {%{cur | scope: sid, bound: %{}, frames: Map.put(cur.frames, frame, bound)}, nil}

      {:instance, sid, params, frame} ->
        values = prepare(args, params, caller)
        frames = Map.put(cur.frames, frame, param_map(%{params: params}, values))
        {%{cur | scope: sid, bound: %{}, frames: frames}, nil}

      {:def, _d, _sid} = def when args == [] ->
        {cur, def}

      nil ->
        error("#{seg} is not an instance")

      _ ->
        error("#{seg} is not an instance")
    end
  end

  # `Inv!2`: the second conjunct of the definition of Inv.
  defp sub_entry({:sub_expr, d, sid, n}, _env),
    do: {:def, %{d | body: select(d.body, n), params: []}, sid}

  defp sub_entry({:sub_expr_of, inner, n}, env) do
    {:def, d, sid} = sub_entry(inner, env)
    {:def, %{d | body: select(d.body, n)}, sid}
  end

  defp sub_entry(entry, _env), do: entry

  defp select({kind, items}, n) when kind in [:and, :or] and n >= 1 and n <= length(items),
    do: Enum.at(items, n - 1)

  defp select({:let, _defs, body}, n), do: select(body, n)
  defp select(_e, n), do: error("cannot select part #{n} of the expression")

  # -- Variables --

  defp read_var(i, %{primed: true, next: next, ctx: ctx}) do
    case next do
      %{} = m ->
        case Map.fetch(m, i) do
          {:ok, v} -> v
          :error -> error("the variable #{elem(ctx.variables, i)}' has no value yet")
        end

      t when is_tuple(t) ->
        elem(t, i)

      nil ->
        error("the primed variable #{elem(ctx.variables, i)}' is used in a state expression")
    end
  end

  defp read_var(i, %{state: state, ctx: ctx}) do
    case state do
      t when is_tuple(t) ->
        elem(t, i)

      %{} = m ->
        case Map.fetch(m, i) do
          {:ok, v} -> v
          :error -> error("the variable #{elem(ctx.variables, i)} has no value yet")
        end

      nil ->
        error("the variable #{elem(ctx.variables, i)} is used in a constant expression")
    end
  end

  # -- LET --

  @doc false
  def let_env(defs, env) do
    ref = if env.gen, do: nil, else: make_ref()

    Enum.reduce(defs, env, fn
      %{kind: :instance} = inst, acc ->
        case Map.fetch(acc.ctx.let_instances, {acc.scope, inst.pos}) do
          {:ok, {sid, frame}} ->
            %{acc | bound: Map.put(acc.bound, inst.name, {:let_instance, sid, frame, acc.bound})}

          :error ->
            error("INSTANCE inside LET is not supported here: #{inst.module}")
        end

      d, acc ->
        closure = %{scope: acc.scope, bound: acc.bound, frames: acc.frames, ref: ref}
        %{acc | bound: Map.put(acc.bound, d.name, {:let_def, d, closure})}
    end)
  end

  # -- Bindings --

  # Calls `fun.(env, acc)` for each combination of the bound variables;
  # `fun` gives `{:cont, acc}` or `{:halt, acc}`.
  defp each_binding(binds, env, acc, fun) do
    {_, acc} = bindings(binds, env, acc, fun)
    acc
  end

  defp bindings([], env, acc, fun) do
    case fun.(env, acc) do
      {:cont, acc} -> {:cont, acc}
      {:halt, acc} -> {:halt, acc}
    end
  end

  defp bindings([{target, set} | rest], env, acc, fun) do
    if set == nil, do: error("TLC cannot evaluate an unbounded quantifier")

    set
    |> eval(env)
    |> Value.enum()
    |> Enum.reduce_while({:cont, acc}, fn v, {_, acc} ->
      case bindings(rest, bind(env, target, v), acc, fun) do
        {:cont, acc} -> {:cont, {:cont, acc}}
        {:halt, acc} -> {:halt, {:halt, acc}}
      end
    end)
  end

  @doc false
  def bind(env, name, v) when is_binary(name), do: %{env | bound: Map.put(env.bound, name, v)}

  def bind(env, {:tuple, names}, v) do
    case v do
      {:seq, t} when tuple_size(t) == length(names) ->
        names
        |> Enum.with_index()
        |> Enum.reduce(env, fn {n, i}, acc -> bind(acc, n, elem(t, i)) end)

      _ ->
        error("cannot bind #{Value.show(v)} to a tuple of #{length(names)} names")
    end
  end

  # -- Functions --

  defp fun_domain([{_target, set}], env) do
    d = eval(set, env)
    {d, keys(d)}
  end

  defp fun_domain(binds, env) do
    sets = Enum.map(binds, fn {_t, s} -> eval(s, env) end)
    d = {:times, sets}
    {d, keys(d)}
  end

  defp keys(d) do
    if finite?(d), do: {:ok, Enum.map(Value.enum(d), &Value.canon/1)}, else: :infinite
  end

  defp finite?(:nat), do: false
  defp finite?(:int), do: false
  defp finite?(:string), do: false
  defp finite?(:any), do: false
  defp finite?({:seq_set, _}), do: false
  defp finite?({:interval, _, _}), do: true
  defp finite?({:subset, s}), do: finite?(s)
  defp finite?({:fun_set, a, b}), do: finite?(a) and finite?(b)
  defp finite?({:times, sets}), do: Enum.all?(sets, &finite?/1)
  defp finite?({:record_set, fields}), do: Enum.all?(fields, fn {_, s} -> finite?(s) end)
  defp finite?(_), do: true

  defp bind_key(env, [{target, _}], k), do: bind(env, target, k)

  defp bind_key(env, binds, {:seq, t}) do
    binds
    |> Enum.with_index()
    |> Enum.reduce(env, fn {{target, _}, i}, acc -> bind(acc, target, elem(t, i)) end)
  end

  # A function definition `f[x \in S] == e`: lazy, so that it can be
  # recursive.
  defp fun_def_value(d, env) do
    {domain, _} = fun_domain(d.binds, env)
    frozen = freeze(env)
    {:lazy_fun, domain, fn k -> eval(d.body, bind_key(frozen, d.binds, k)) end}
  end

  # An environment for a closure: no generation, no partial state.
  defp freeze(env), do: %{env | gen: false}

  defp except_path(fv, [step | rest], value, env) do
    key =
      case step do
        {:index, [a]} -> eval(a, env)
        {:index, many} -> Value.tuple(Enum.map(many, &eval(&1, env)))
        {:field, name} -> name
      end

    old = Value.apply_fun(fv, key)

    new =
      case rest do
        [] -> eval(value, %{env | at: {:at, old}})
        _ -> except_path(old, rest, value, env)
      end

    Value.update(fv, key, new)
  end

  # -- ENABLED --

  @doc "`ENABLED a` in the current state."
  def enabled?(a, env) do
    if env.primed, do: error("ENABLED inside a primed expression")
    env = %{env | next: %{}, gen: true, label_mode: false, pseudo: true}
    gen(a, env, :next) != []
  end

  # -- Generation --

  @doc """
  Generates the assignments that an action allows.

  `mode` is `:next` (the action assigns primed variables; `env.next` is
  the partial next state) or `:init` (the predicate assigns unprimed
  variables; `env.state` is the partial state). Gives a list of
  `{assignments, label}`.
  """
  def gen(e, env, mode) do
    env = %{env | gen: true}
    do_gen(e, env, mode)
  end

  defp partial(env, :next), do: env.next
  defp partial(env, :init), do: env.state

  defp with_partial(env, :next, p), do: %{env | next: p}
  defp with_partial(env, :init, p), do: %{env | state: p}

  defp leaf(env, mode), do: [{partial(env, mode), env.label}]

  defp do_gen({:and, items}, env, mode) do
    env = %{env | label_mode: false}

    Enum.reduce(items, leaf(env, mode), fn item, acc ->
      Enum.flat_map(acc, fn {p, label} ->
        gen_item(item, with_partial(%{env | label: label}, mode, p), mode)
      end)
    end)
  end

  defp do_gen({:or, items}, env, mode), do: Enum.flat_map(items, &do_gen(&1, env, mode))

  defp do_gen({:exists, binds, body}, env, mode) do
    binds
    |> each_binding(env, [], fn env2, acc -> {:cont, [do_gen(body, env2, mode) | acc]} end)
    |> Enum.reverse()
    |> Enum.concat()
  end

  defp do_gen({:forall, binds, body}, env, mode) do
    env = %{env | label_mode: false}

    envs =
      binds |> each_binding(env, [], fn env2, acc -> {:cont, [env2 | acc]} end) |> Enum.reverse()

    Enum.reduce(envs, leaf(env, mode), fn benv, acc ->
      Enum.flat_map(acc, fn {p, label} ->
        gen_item(body, with_partial(%{benv | label: label}, mode, p), mode)
      end)
    end)
  end

  defp do_gen({:implies, a, b}, env, mode) do
    env = %{env | label_mode: false}
    if bool(a, env), do: do_gen(b, env, mode), else: leaf(env, mode)
  end

  # `f[x]` where `f` is a function definition: TLC generates with the
  # body of the function, so its disjunctions give more steps.
  defp do_gen({:apply, f, args} = e, env, mode) do
    case fun_body(f, env) do
      {:ok, binds, body, fenv} ->
        arg =
          case args do
            [a] -> eval(a, env)
            many -> Value.tuple(Enum.map(many, &eval(&1, env)))
          end

        {domain, _} = fun_domain(binds, fenv)

        unless Value.member?(arg, domain),
          do: error("#{Value.show(arg)} is not in the domain of the function")

        fenv = %{
          bind_key(fenv, binds, Value.canon(arg))
          | state: env.state,
            next: env.next,
            label: env.label,
            label_mode: false
        }

        do_gen(body, fenv, mode)

      :no ->
        guard(e, env, mode)
    end
  end

  defp do_gen({:if, c, a, b}, env, mode) do
    env = %{env | label_mode: false}
    if bool(c, env), do: do_gen(a, env, mode), else: do_gen(b, env, mode)
  end

  defp do_gen({:case, arms, other}, env, mode) do
    env = %{env | label_mode: false}

    case Enum.find(arms, fn {c, _} -> bool(c, env) end) do
      {_, e} -> do_gen(e, env, mode)
      nil when other != nil -> do_gen(other, env, mode)
      nil -> error("no arm of a CASE is true, and the CASE has no OTHER")
    end
  end

  defp do_gen({:let, defs, body}, env, mode), do: do_gen(body, let_env(defs, env), mode)
  defp do_gen({:label, _, e}, env, mode), do: do_gen(e, env, mode)

  defp do_gen({:app, "=", [lhs, rhs], _} = e, env, mode) do
    case target(lhs, env, mode) do
      {:ok, i} ->
        p = partial(env, mode)

        if Map.has_key?(p, i) do
          guard(e, env, mode)
        else
          v = env |> rhs_env() |> then(&eval(rhs, &1)) |> Value.canon()
          leaf(with_partial(env, mode, Map.put(p, i, v)), mode)
        end

      :no ->
        guard(e, env, mode)
    end
  end

  defp do_gen({:app, "\\in", [lhs, set], _} = e, env, mode) do
    case target(lhs, env, mode) do
      {:ok, i} ->
        p = partial(env, mode)

        if Map.has_key?(p, i) do
          guard(e, env, mode)
        else
          set
          |> eval(rhs_env(env))
          |> Value.enum()
          |> Enum.flat_map(fn v ->
            leaf(with_partial(env, mode, Map.put(p, i, Value.canon(v))), mode)
          end)
        end

      :no ->
        guard(e, env, mode)
    end
  end

  # `x' \subseteq S` assigns each subset of S (as `x' \in SUBSET S`).
  defp do_gen({:app, "\\subseteq", [lhs, set], pos} = e, env, mode) do
    case target(lhs, env, mode) do
      {:ok, i} ->
        if Map.has_key?(partial(env, mode), i),
          do: guard(e, env, mode),
          else: do_gen({:app, "\\in", [lhs, {:value, {:subset, eval(set, env)}}], pos}, env, mode)

      :no ->
        guard(e, env, mode)
    end
  end

  defp do_gen({:unchanged, e}, env, :next) do
    case unchanged_vars(e, env) do
      {:ok, vars} ->
        Enum.reduce_while(vars, leaf(env, :next), fn i, [{p, label}] ->
          current =
            case i do
              {:pseudo, sid, n} -> eval({:name, n, nil}, %{env | scope: sid, primed: false})
              _ -> read_var(i, %{env | primed: false})
            end

          case Map.fetch(p, i) do
            {:ok, v} -> if v == current, do: {:cont, [{p, label}]}, else: {:halt, []}
            :error -> {:cont, [{Map.put(p, i, current), label}]}
          end
        end)

      :complex ->
        guard({:unchanged, e}, env, :next)
    end
  end

  defp do_gen({:box_action, a, sub}, env, mode),
    do: do_gen(a, env, mode) ++ do_gen({:unchanged, sub}, env, mode)

  # `<<A>>_sub`: the steps of A that change `sub`. A step that does not
  # give a value to all the variables of `sub` counts as a change.
  defp do_gen({:diamond_action, a, sub}, env, :next) do
    a
    |> do_gen(env, :next)
    |> Enum.filter(fn {p, _} ->
      try do
        not Value.eq?(
          eval(sub, %{env | next: p, primed: true, gen: false}),
          eval(sub, %{env | gen: false})
        )
      rescue
        Value.Error -> true
      end
    end)
  end

  # Action composition `A \cdot B`: a step of A, then a step of B from
  # the middle state. TLC counts the middle states as generated.
  defp do_gen({:app, "\\cdot", [a, b], _}, env, :next) do
    nvars = tuple_size(env.ctx.variables)
    middles = do_gen(a, %{env | next: %{}}, :next)
    Process.put(:tla_extra_generated, Process.get(:tla_extra_generated, 0) + length(middles))

    Enum.flat_map(middles, fn {t, _} ->
      if map_size(t) != nvars,
        do: error("the first action of `\\cdot` does not give a value to all the variables")

      middle = List.to_tuple(for i <- 0..(nvars - 1)//1, do: Map.fetch!(t, i))

      b
      |> do_gen(%{env | state: middle}, :next)
      |> Enum.map(fn {u, _} -> {u, env.label} end)
    end)
  end

  defp do_gen({:name, n, _} = e, env, mode), do: gen_named(n, [], e, env, mode)
  defp do_gen({:app, n, args, _} = e, env, mode), do: gen_named(n, args, e, env, mode)

  defp do_gen({:inst, path, name, args, _} = e, env, mode) do
    {entry, env2} = navigate(path, name, env)

    case entry do
      {:def, %{kind: :op} = d, sid} ->
        values = prepare(args, d.params, env)

        callee = %{
          env2
          | scope: sid,
            bound: param_map(d, values),
            label: label(env, name),
            state: env.state,
            next: env.next
        }

        do_gen(d.body, callee, mode)

      _ ->
        guard(e, env, mode)
    end
  end

  defp do_gen(e, env, mode), do: guard(e, env, mode)

  defp label(env, name) when is_binary(name), do: if(env.label_mode, do: name, else: env.label)
  defp label(env, _), do: env.label

  # Expands a definition in generation, so its assignments count.
  defp gen_named(n, args, e, env, mode) do
    cond do
      n in @core ->
        guard(e, env, mode)

      true ->
        case Map.fetch(env.bound, n) do
          {:ok, {:thunk, _, te, scope, bound, frames, _}} when args == [] ->
            do_gen(te, %{env | scope: scope, bound: bound, frames: frames}, mode)

          {:ok, {:let_def, d, closure}} ->
            values = prepare(args, d.params, env)

            bound =
              closure.bound
              |> Map.put(n, {:let_def, d, closure})
              |> Map.merge(param_map(d, values))

            do_gen(
              d.body,
              %{env | scope: closure.scope, bound: bound, frames: closure.frames},
              mode
            )

          {:ok, _} ->
            guard(e, env, mode)

          :error ->
            gen_entry(Context.lookup(env.ctx, env.scope, n), n, args, e, env, mode)
        end
    end
  end

  defp gen_entry(entry, n, args, e, env, mode), do: gen_entry(entry, n, args, e, env, env, mode)

  # `caller` is the environment of the arguments; `env` gives the scope of
  # the name.
  defp gen_entry(entry, n, args, e, caller, env, mode) do
    case entry do
      # A constant definition is a value for TLC: a condition.
      {:def, %{kind: :op, params: []} = d, sid} when args == [] and not is_nil(d) ->
        if Constant.definition?(env.ctx, sid, d),
          do: guard(e, caller, mode),
          else: do_gen(d.body, %{caller | scope: sid, bound: %{}, frames: env.frames, label: label(caller, n)}, mode)

      {:def, %{kind: :op} = d, sid} ->
        values = prepare(args, d.params, caller)

        do_gen(
          d.body,
          %{
            caller
            | scope: sid,
              bound: param_map(d, values),
              frames: env.frames,
              label: label(caller, n)
          },
          mode
        )

      {:alias, sid, target} ->
        gen_entry(
          Context.lookup(env.ctx, sid, target),
          target,
          args,
          e,
          caller,
          %{env | scope: sid},
          mode
        )

      {:subst, expr, outer, frame} when args == [] ->
        do_gen(
          expr,
          %{caller | scope: outer, bound: Map.get(env.frames, frame, %{}), frames: env.frames},
          mode
        )

      # A constant operator of an instance, replaced by an operator of the
      # outer module.
      {:subst, {:name, g, _}, outer, frame} ->
        outer_env = %{env | scope: outer, bound: Map.get(env.frames, frame, %{})}

        case Map.fetch(outer_env.bound, g) do
          {:ok, _} ->
            guard(e, caller, mode)

          :error ->
            gen_entry(Context.lookup(env.ctx, outer, g), g, args, e, caller, outer_env, mode)
        end

      _ ->
        guard(e, caller, mode)
    end
  end

  defp guard(e, env, mode) do
    if bool(e, env), do: leaf(env, mode), else: []
  end

  # An item of a conjunction (or of a bounded \A). When all the variables
  # have a value, TLC only evaluates the rest of the items.
  # (TLC does this in the next-state relation only with warnings on, its
  # default; `-nowarning` turns it off.)
  defp gen_item(item, env, mode) do
    if all_assigned?(partial(env, mode), tuple_size(env.ctx.variables)) and
         (mode == :init or Process.get(:tla_warn, true)),
       do: guard(item, env, mode),
       else: do_gen(item, env, mode)
  end

  defp all_assigned?(p, n) when map_size(p) < n, do: false
  defp all_assigned?(p, n) when map_size(p) == n, do: Enum.all?(Map.keys(p), &is_integer/1)
  defp all_assigned?(p, n), do: Enum.count(Map.keys(p), &is_integer/1) == n

  # The bound variables and the body of `f` when it is a function
  # definition (or a function constructor).
  defp fun_body({:func, binds, body}, env), do: {:ok, binds, body, env}

  defp fun_body({:name, n, _}, env) do
    case Map.fetch(env.bound, n) do
      {:ok, {:let_def, %{kind: :fun} = d, closure}} ->
        bound = Map.put(closure.bound, n, {:let_def, d, closure})

        {:ok, d.binds, d.body,
         %{env | scope: closure.scope, bound: bound, frames: closure.frames}}

      {:ok, {:let_def, %{kind: :op, params: [], body: {:func, _, _} = body}, closure}} ->
        fun_body(body, %{env | scope: closure.scope, bound: closure.bound, frames: closure.frames})

      {:ok, _} ->
        :no

      :error ->
        fun_entry(Context.lookup(env.ctx, env.scope, n), env)
    end
  end

  defp fun_body(_f, _env), do: :no

  defp fun_entry({:def, %{kind: :fun} = d, sid}, env),
    do: {:ok, d.binds, d.body, %{env | scope: sid, bound: %{}}}

  defp fun_entry({:def, %{kind: :op, params: [], body: {:func, _, _} = body}, sid}, env),
    do: fun_body(body, %{env | scope: sid, bound: %{}})

  defp fun_entry({:alias, sid, target}, env),
    do: fun_entry(Context.lookup(env.ctx, sid, target), %{env | scope: sid})

  defp fun_entry(_, _env), do: :no

  # The environment for the right side of an assignment.
  defp rhs_env(env), do: env

  # The variable that `lhs` assigns: `x'` in :next mode, `x` in :init mode.
  defp target({:name, n, _} = lhs, env, mode) do
    case Map.fetch(env.bound, n) do
      # An operator argument: the argument expression decides.
      {:ok, {:thunk, _, te, scope, bound, frames, _}} ->
        target(te, %{env | scope: scope, bound: bound, frames: frames}, mode)

      _ when mode == :init ->
        var_of(lhs, env)

      _ ->
        :no
    end
  end

  defp target({:label, _, e}, env, mode), do: target(e, env, mode)
  defp target({:prime, inner}, env, :next), do: var_of(inner, env)
  defp target(_lhs, _env, :next), do: :no
  defp target({:prime, _}, _env, :init), do: :no
  defp target(lhs, env, :init), do: var_of(lhs, env)

  defp var_of({:name, n, _}, env) do
    case Map.fetch(env.bound, n) do
      # An operator argument: `Op(v) == v' = 1` with `Op(x)` assigns x.
      {:ok, {:thunk, _, te, scope, bound, frames, _}} ->
        var_of(te, %{env | scope: scope, bound: bound, frames: frames})

      {:ok, _} ->
        :no

      :error ->
        var_of_entry(n, env)
    end
  end

  defp var_of({:label, _, e}, env), do: var_of(e, env)
  defp var_of(_, _env), do: :no

  defp var_of_entry(n, env) do
    case Context.lookup(env.ctx, env.scope, n) do
      {:var, i} ->
        {:ok, i}

      {:subst, expr, outer, frame} ->
        case var_of(expr, %{env | scope: outer, bound: Map.get(env.frames, frame, %{})}) do
          :no when env.pseudo -> {:ok, {:pseudo, env.scope, n}}
          other -> other
        end

      _ ->
        :no
    end
  end

  # The variables of `UNCHANGED e`, when `e` is a variable, a tuple of
  # them, or a definition of such a tuple.
  defp unchanged_vars({:tuple, elems}, env) do
    Enum.reduce_while(elems, {:ok, []}, fn e, {:ok, acc} ->
      case unchanged_vars(e, env) do
        {:ok, vs} -> {:cont, {:ok, acc ++ vs}}
        :complex -> {:halt, :complex}
      end
    end)
  end

  defp unchanged_vars({:name, n, _}, env) do
    case Map.fetch(env.bound, n) do
      {:ok, {:thunk, _, te, scope, bound, frames, _}} ->
        unchanged_vars(te, %{env | scope: scope, bound: bound, frames: frames})

      {:ok, _} ->
        :complex

      :error ->
        unchanged_entry(n, env)
    end
  end

  defp unchanged_vars({:inst, path, name, [], _}, env) do
    case navigate(path, name, env) do
      {{:def, %{kind: :op, params: []} = d, sid}, env2} ->
        unchanged_vars(d.body, %{env2 | scope: sid, bound: %{}})

      {{:var, i}, _} ->
        {:ok, [i]}

      {{:subst, expr, outer, frame}, env2} ->
        unchanged_vars(expr, %{env2 | scope: outer, bound: Map.get(env2.frames, frame, %{})})

      _ ->
        :complex
    end
  end

  defp unchanged_vars(_e, _env), do: :complex

  defp unchanged_entry(n, env) do
    case Context.lookup(env.ctx, env.scope, n) do
      {:var, i} ->
        {:ok, [i]}

      {:def, %{kind: :op, params: []} = d, sid} ->
        unchanged_vars(d.body, %{env | scope: sid, bound: %{}})

      {:subst, expr, outer, frame} ->
        case unchanged_vars(expr, %{env | scope: outer, bound: Map.get(env.frames, frame, %{})}) do
          :complex when env.pseudo -> {:ok, [{:pseudo, env.scope, n}]}
          other -> other
        end

      _ ->
        :complex
    end
  end
end
