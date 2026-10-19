defmodule Accord.TLA.Checker.Spec do
  @moduledoc """
  Reads the behavior specification and the properties of a model.

  A behavior specification has the form

      Init /\\ [][Next]_vars /\\ WF_vars(A) /\\ \\A p \\in P : SF_vars(B(p))

  `analyze/2` gives its initial predicate, its next-state action, and its
  fairness conditions. Definitions are expanded, also through instances
  (`Spec == M!Spec`), until the parts are found.

  `property/2` splits a property into obligations:

  - `{:init, pred}` — a state predicate: it must hold in each initial state
  - `{:invariant, pred}` — `[]P` for a state predicate `P`
  - `{:action, a, sub}` — `[][A]_v`: each step must be an `A` step or
    leave `v` unchanged
  - `{:live, fairness, pattern}` — a liveness obligation, with the
    fairness of the property (from `F => G`). The pattern is
    `{:leadsto, p, q}`, `{:always_eventually, p}`, `{:eventually, p}`,
    `{:eventually_always, p}`, or `{:fair, :weak | :strong, sub, a}` (a
    fairness condition that the behaviors must satisfy).

  A closure `{expr, scope, bound, frames}` keeps the scope of each part.
  """

  alias Accord.TLA.Checker.{Temporal, Context, Eval, Value}
  import Value, only: [error: 1]

  @type closure :: {tuple(), term(), map(), map()}

  @doc "Analyzes the behavior specification of the config."
  def analyze(ctx, config) do
    env = Eval.new(ctx)

    cond do
      config.specification ->
        parts = flatten(ref(config.specification, env), env)

        inits = for {:init, c} <- parts, do: c
        nexts = for {:next, a, sub} <- parts, do: {a, sub}
        fairness = for {:fair, f} <- parts, do: f

        others = for {:other, e} <- parts, do: e

        if others != [],
          do:
            error(
              "the specification #{config.specification} has a part that is not supported: #{inspect(hd(others) |> elem(0))}"
            )

        case nexts do
          [{next, sub}] -> %{init: inits, next: next, sub: sub, fairness: fairness}
          [] -> %{init: inits, next: nil, sub: nil, fairness: fairness}
          _ -> error("the specification has more than one [][Next]_v")
        end

      config.init && config.next ->
        %{
          init: [closure(ref(config.init, env), env)],
          next: closure(ref(config.next, env), env),
          sub: nil,
          fairness: []
        }

      config.init == nil and config.next == nil ->
        # A model of constants: TLC only checks the assumptions.
        %{init: nil, next: nil, sub: nil, fairness: []}

      true ->
        error("the config needs SPECIFICATION, or INIT and NEXT")
    end
  end

  @doc """
  Splits the next-state action into the actions of TLC: the disjuncts,
  one action for each value of a `\\E` over a constant set, and the body
  of a definition applied to constant arguments. Gives
  `[{closure, name}]`; the name is the name of the last definition (or
  `default`). TLC generates the steps of one action after the other.
  """
  def actions(ctx, {e, scope, bound, frames}, default) do
    env = %{Eval.new(ctx) | scope: scope, bound: bound, frames: frames}
    split(e, env, default)
  end

  defp split(e, env, name) do
    case e do
      {:or, items} ->
        Enum.flat_map(items, &split(&1, env, name))

      {:label, _, inner} ->
        split(inner, env, name)

      {:let, defs, body} ->
        split(body, Eval.let_env(defs, %{env | gen: true}), name)

      {:exists, binds, body} ->
        case constant_bindings(binds, env) do
          {:ok, envs} -> Enum.flat_map(envs, &split(body, &1, name))
          :error -> [{closure(e, env), name}]
        end

      {:name, n, _} ->
        split_call(e, n, [], env, name)

      {:app, n, args, _} ->
        split_call(e, n, args, env, name)

      _ ->
        [{closure(e, env), name}]
    end
  end

  # The values of the bound variables, when the sets are constant.
  defp constant_bindings(binds, env) do
    if Enum.all?(binds, fn {_, set} -> set != nil and constant?(set, env) end),
      do: {:ok, bindings(env, binds)},
      else: :error
  rescue
    Value.Error -> :error
  end

  defp constant?(e, env),
    do: Accord.TLA.Checker.Constant.expression?(e, env.ctx, env.scope, Map.keys(env.bound))

  defp split_call(e, n, args, env, name) do
    with false <- Map.has_key?(env.bound, n),
         {:def, %{kind: :op} = d, sid} <- Context.lookup(env.ctx, env.scope, n),
         true <- length(d.params) == length(args),
         true <- Enum.all?(d.params, fn {_, arity} -> arity == 0 end),
         true <- Enum.all?(args, &constant?(&1, env)) do
      values = Enum.map(args, &Eval.eval(&1, env))
      bound = d.params |> Enum.map(&elem(&1, 0)) |> Enum.zip(values) |> Map.new()
      split(d.body, %{env | scope: sid, bound: bound}, n)
    else
      _ -> [{closure(e, env), name}]
    end
  rescue
    Value.Error -> [{closure(e, env), name}]
  end

  defp ref(name, env) do
    if Context.lookup(env.ctx, env.scope, name) == nil,
      do: error("#{name} is not defined in the root module")

    {:name, name, nil}
  end

  defp closure(expr, env), do: {expr, env.scope, env.bound, env.frames}

  # The parts of a conjunction of temporal formulas.
  defp flatten({:and, items}, env), do: Enum.flat_map(items, &flatten(&1, env))
  defp flatten({:label, _, e}, env), do: flatten(e, env)

  defp flatten({:always, {:box_action, a, sub}}, env),
    do: [{:next, closure(a, env), closure(sub, env)}]

  defp flatten({:always, {:name, _, _} = n}, env) do
    case expand(n, env) do
      {:ok, {{:box_action, a, sub}, env2}} -> [{:next, closure(a, env2), closure(sub, env2)}]
      _ -> [{:other, {:always, n}}]
    end
  end

  defp flatten({kind, sub, a}, env) when kind in [:wf, :sf],
    do: [{:fair, {strength(kind), closure(sub, env), closure(a, env)}}]

  defp flatten({:forall, binds, body} = e, env) do
    if temporal?(body, env) do
      env
      |> bindings(binds)
      |> Enum.flat_map(&flatten(body, &1))
    else
      [{:init, closure(e, env)}]
    end
  end

  defp flatten(e, env) do
    if temporal?(e, env) do
      case expand(e, env) do
        {:ok, {body, env2}} -> flatten(body, env2)
        :error -> [{:other, e}]
      end
    else
      [{:init, closure(e, env)}]
    end
  end

  defp strength(:wf), do: :weak
  defp strength(:sf), do: :strong

  @doc false
  # The environments for all values of the bound variables.
  def bindings(env, binds) do
    Enum.reduce(binds, [env], fn {target, set}, envs ->
      Enum.flat_map(envs, fn e ->
        set |> Eval.eval(e) |> Value.enum() |> Enum.map(&Eval.bind(e, target, &1))
      end)
    end)
  end

  # Expands a definition: gives its body and the environment for it.
  defp expand({:name, n, _}, env), do: expand_call(n, [], env)
  defp expand({:app, n, args, _}, env), do: expand_call(n, args, env)

  defp expand({:inst, path, name, args, _}, env) do
    {_, env2} = navigate(path, env)
    expand_entry(Context.lookup(env.ctx, env2.scope, name), name, args, env, env2)
  end

  defp expand(_e, _env), do: :error

  defp expand_call(n, args, env) do
    case Map.fetch(env.bound, n) do
      {:ok, {:let_def, d, closure}} ->
        bound = Map.merge(closure.bound, params(d, args, env))
        {:ok, {d.body, %{env | scope: closure.scope, bound: bound, frames: closure.frames}}}

      # An operator parameter (`Op(F(_)) == F(...)`): the operator it has.
      {:ok, {:op_value, _, _, impl}} ->
        case impl do
          {:named, name, scope} ->
            expand_entry(Context.lookup(env.ctx, scope, name), name, args, env, %{
              env
              | scope: scope
            })

          {:let, d, closure} ->
            bound = Map.merge(closure.bound, params(d, args, env))
            {:ok, {d.body, %{env | scope: closure.scope, bound: bound, frames: closure.frames}}}

          {:lambda, names, body, scope, bound, frames} ->
            d = %{params: Enum.map(names, &{&1, 0})}

            {:ok,
             {body,
              %{env | scope: scope, bound: Map.merge(bound, params(d, args, env)), frames: frames}}}

          _ ->
            :error
        end

      {:ok, _} ->
        :error

      :error ->
        expand_entry(Context.lookup(env.ctx, env.scope, n), n, args, env, env)
    end
  end

  defp expand_entry(entry, _n, args, caller, env) do
    case entry do
      {:def, %{kind: :op} = d, sid} ->
        {:ok, {d.body, %{env | scope: sid, bound: params(d, args, caller)}}}

      {:alias, sid, target} ->
        expand_entry(Context.lookup(env.ctx, sid, target), target, args, caller, %{
          env
          | scope: sid
        })

      {:subst, expr, outer, frame} when args == [] ->
        {:ok, {expr, %{env | scope: outer, bound: Map.get(env.frames, frame, %{})}}}

      _ ->
        :error
    end
  end

  # Operator arguments for temporal expansion: evaluated values, or the
  # expression itself when it is temporal.
  defp params(d, args, env) do
    d.params
    |> Enum.zip(args)
    |> Map.new(fn
      {{name, 0}, arg} ->
        if temporal?(arg, env),
          do:
            {name,
             {:let_def, %{kind: :op, name: name, params: [], body: arg},
              %{scope: env.scope, bound: env.bound, frames: env.frames, ref: nil}}},
          else: {name, {:thunk, make_ref(), arg, env.scope, env.bound, env.frames, false}}

      {{name, _arity}, arg} ->
        {name, Eval.op_value(arg, env)}
    end)
  end

  defp navigate(path, env) do
    Enum.reduce(path, {nil, env}, fn {seg, args}, {_, cur} ->
      case Context.lookup(cur.ctx, cur.scope, seg) do
        {:instance, sid, params, frame} ->
          values =
            params |> Enum.zip(args) |> Map.new(fn {{p, _}, a} -> {p, Eval.eval(a, env)} end)

          {nil, %{cur | scope: sid, bound: %{}, frames: Map.put(cur.frames, frame, values)}}

        _ ->
          error("#{seg} is not an instance")
      end
    end)
  end

  # -- Levels --

  @doc "Tells if an expression is a temporal formula."
  def temporal?(e, env), do: level(e, env, MapSet.new()) == :temporal

  @doc "Tells if an expression is an action (it has primes, but is not temporal)."
  def action?(e, env), do: level(e, env, MapSet.new()) == :action

  # :temporal > :action > :state
  defp level(e, env, seen) do
    case e do
      {kind, _} when kind in [:always, :eventually] ->
        :temporal

      {kind, _, _} when kind in [:leadsto, :wf, :sf] ->
        :temporal

      {kind, _, _} when kind in [:temporal_forall, :temporal_exists] ->
        :temporal

      {kind, _, _} when kind in [:box_action, :diamond_action] ->
        :action

      {:prime, _} ->
        :action

      {:unchanged, _} ->
        :action

      {:enabled, _} ->
        :state

      {:name, n, _} ->
        name_level(n, [], env, seen)

      {:app, n, args, _} ->
        max_level([name_level(n, args, env, seen) | Enum.map(args, &level(&1, env, seen))])

      {:inst, path, name, args, _} ->
        inst_level(path, name, args, env, seen)

      {:let, defs, body} ->
        level(body, let_bound(defs, env), seen)

      t when is_tuple(t) ->
        t |> Tuple.to_list() |> Enum.map(&sub_level(&1, env, seen)) |> max_level()

      _ ->
        :state
    end
  end

  defp sub_level(x, env, seen) when is_tuple(x), do: level(x, env, seen)

  defp sub_level(x, env, seen) when is_list(x),
    do: x |> Enum.map(&sub_level(&1, env, seen)) |> max_level()

  defp sub_level(_, _env, _seen), do: :state

  defp let_bound(defs, env) do
    Enum.reduce(defs, env, fn d, acc ->
      %{
        acc
        | bound:
            Map.put(
              acc.bound,
              d.name,
              {:let_def, d, %{scope: acc.scope, bound: acc.bound, frames: acc.frames, ref: nil}}
            )
      }
    end)
  end

  defp name_level(n, _args, env, seen) do
    case Map.fetch(env.bound, n) do
      {:ok, {:let_def, d, closure}} ->
        key = {:let, d.name, d.body}

        if MapSet.member?(seen, key),
          do: :state,
          else:
            level(
              d.body,
              %{env | scope: closure.scope, bound: closure.bound},
              MapSet.put(seen, key)
            )

      {:ok, {:thunk, _, e, scope, bound, _, _}} ->
        level(e, %{env | scope: scope, bound: bound}, seen)

      {:ok, _} ->
        :state

      :error ->
        entry_level(Context.lookup(env.ctx, env.scope, n), env, seen)
    end
  end

  defp entry_level(entry, env, seen) do
    case entry do
      {:def, %{kind: :op} = d, sid} ->
        key = {sid, d.name}

        cond do
          MapSet.member?(seen, key) ->
            :state

          # A memo: the level of a definition does not depend on where it
          # is used (without the memo, shared definitions make the
          # analysis exponential).
          (cached = Map.get(Process.get(:tla_levels) || %{}, {env.ctx.id, key})) != nil ->
            cached

          true ->
            l = level(d.body, %{env | scope: sid, bound: %{}}, MapSet.put(seen, key))

            Process.put(
              :tla_levels,
              Map.put(Process.get(:tla_levels) || %{}, {env.ctx.id, key}, l)
            )

            l
        end

      {:alias, sid, target} ->
        entry_level(Context.lookup(env.ctx, sid, target), %{env | scope: sid}, seen)

      {:subst, expr, outer, _} ->
        level(expr, %{env | scope: outer, bound: %{}}, seen)

      _ ->
        :state
    end
  end

  defp inst_level(path, name, _args, env, seen) do
    {_, env2} = navigate(Enum.map(path, fn {s, _} -> {s, []} end), env)
    entry_level(Context.lookup(env.ctx, env2.scope, name), env2, seen)
  end

  defp max_level(levels) do
    cond do
      :temporal in levels -> :temporal
      :action in levels -> :action
      true -> :state
    end
  end

  # -- Properties --

  @doc """
  Splits a property (a name in the root scope) into obligations:

  - `{:init, pred}` — a state predicate on the initial states.
  - `{:invariant, pred}` — `[]P` with `P` a state predicate.
  - `{:action, a, sub}` — `[][A]_sub`, on each step.
  - `{:live, formula, atoms}` — the negation of a temporal formula, for
    the liveness check (see `Accord.TLA.Checker.Temporal`). `atoms` maps
    an atom id to `{:state | :action, closure}`.
  """
  def property(ctx, name) do
    env = Eval.new(ctx)
    obligations(ref(name, env), env)
  end

  defp obligations({:and, items}, env), do: Enum.flat_map(items, &obligations(&1, env))
  defp obligations({:label, _, e}, env), do: obligations(e, env)

  defp obligations({:forall, binds, body} = e, env) do
    if temporal?(body, env) do
      env |> bindings(binds) |> Enum.flat_map(&obligations(body, &1))
    else
      [{:init, closure(e, env)}]
    end
  end

  defp obligations({:always, {:box_action, a, sub}}, env),
    do: [{:action, closure(a, env), closure(sub, env)}]

  defp obligations({:always, p} = e, env) do
    cond do
      not temporal?(p, env) and not action?(p, env) ->
        [{:invariant, closure(p, env)}]

      not temporal?(p, env) ->
        case expand(p, env) do
          {:ok, {{:box_action, a, sub}, env2}} ->
            [{:action, closure(a, env2), closure(sub, env2)}]

          _ ->
            live(e, env)
        end

      true ->
        live(e, env)
    end
  end

  defp obligations(e, env) do
    cond do
      temporal?(e, env) ->
        case expand(e, env) do
          {:ok, {body, env2}} -> obligations(body, env2)
          :error -> live(e, env)
        end

      action?(e, env) ->
        error("a property cannot be an action without [][...]_v")

      true ->
        [{:init, closure(e, env)}]
    end
  end

  defp live(e, env) do
    formula = e |> ltl(env, false) |> Temporal.simplify()
    {formula, atoms} = number_atoms(formula)
    [{:live, formula, atoms}]
  end

  # Gives the atoms ids; equal atoms get the same id.
  defp number_atoms(formula) do
    {f, {_, atoms}} = number(formula, {%{}, %{}})
    {f, Map.new(atoms, fn {atom, id} -> {id, atom} end)}
  end

  defp number({:atom, kind, c, pol}, {ids, atoms}) do
    case Map.fetch(atoms, {kind, c}) do
      {:ok, id} ->
        {{:lit, id, pol}, {ids, atoms}}

      :error ->
        (fn id -> {{:lit, id, pol}, {ids, Map.put(atoms, {kind, c}, id)}} end).(map_size(atoms))
    end
  end

  defp number({kind, items}, acc) when kind in [:and, :or] do
    {items, acc} = Enum.map_reduce(items, acc, &number/2)
    {{kind, items}, acc}
  end

  defp number({kind, f}, acc) when kind in [:always, :eventually] do
    {f, acc} = number(f, acc)
    {{kind, f}, acc}
  end

  defp number(b, acc) when is_boolean(b), do: {b, acc}

  @doc false
  # The formula `e` (when `pos`) or its negation, in negation normal form,
  # with atoms `{:atom, :state | :action, closure, polarity}`.
  def ltl(e, env, pos) do
    if temporal?(e, env), do: temporal_ltl(e, env, pos), else: atom(e, env, pos)
  end

  defp atom(e, env, pos) do
    kind = if action?(e, env), do: :action, else: :state
    {:atom, kind, closure(e, env), pos}
  end

  defp junction(:and, true), do: :and
  defp junction(:and, false), do: :or
  defp junction(:or, true), do: :or
  defp junction(:or, false), do: :and

  defp temporal_ltl(e, env, pos) do
    case e do
      {:and, items} ->
        {junction(:and, pos), Enum.map(items, &ltl(&1, env, pos))}

      {:or, items} ->
        {junction(:or, pos), Enum.map(items, &ltl(&1, env, pos))}

      {:not, a} ->
        ltl(a, env, not pos)

      {:implies, a, b} ->
        {junction(:or, pos), [ltl(a, env, not pos), ltl(b, env, pos)]}

      {:equiv, a, b} ->
        both = {:and, [ltl(a, env, true), ltl(b, env, true)]}
        neither = {:and, [ltl(a, env, false), ltl(b, env, false)]}
        f = {:or, [both, neither]}
        if pos, do: f, else: Temporal.negate(f)

      {:if, c, a, b} ->
        f =
          {:or,
           [
             {:and, [ltl(c, env, true), ltl(a, env, true)]},
             {:and, [ltl(c, env, false), ltl(b, env, true)]}
           ]}

        if pos, do: f, else: Temporal.negate(f)

      {:label, _, inner} ->
        ltl(inner, env, pos)

      {:let, defs, body} ->
        ltl(body, let_bound(defs, env), pos)

      {:always, a} ->
        if pos, do: {:always, ltl(a, env, true)}, else: {:eventually, ltl(a, env, false)}

      {:eventually, a} ->
        if pos, do: {:eventually, ltl(a, env, true)}, else: {:always, ltl(a, env, false)}

      {:leadsto, p, q} ->
        ltl({:always, {:implies, p, {:eventually, q}}}, env, pos)

      {:wf, sub, a} ->
        # WF_v(A) == []<>(~ENABLED <<A>>_v \/ <<A>>_v)
        angle = {:diamond_action, a, sub}

        f =
          {:always,
           {:eventually, {:or, [atom({:enabled, angle}, env, false), atom(angle, env, true)]}}}

        if pos, do: f, else: Temporal.negate(f)

      {:sf, sub, a} ->
        # SF_v(A) == <>[]~ENABLED <<A>>_v \/ []<><<A>>_v
        angle = {:diamond_action, a, sub}

        f =
          {:or,
           [
             {:eventually, {:always, atom({:enabled, angle}, env, false)}},
             {:always, {:eventually, atom(angle, env, true)}}
           ]}

        if pos, do: f, else: Temporal.negate(f)

      {:forall, binds, body} ->
        {junction(:and, pos), env |> bindings(binds) |> Enum.map(&ltl(body, &1, pos))}

      {:exists, binds, body} ->
        {junction(:or, pos), env |> bindings(binds) |> Enum.map(&ltl(body, &1, pos))}

      _ ->
        case expand(e, env) do
          {:ok, {body, env2}} -> ltl(body, env2, pos)
          :error -> error("this temporal property is not supported: #{inspect(e, limit: 6)}")
        end
    end
  end
end
