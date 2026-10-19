defmodule Accord.TLA.Checker.Semantic.Level do
  @moduledoc """
  The level checks of SANY: a port of `LevelNode.java` and of the
  `levelCheck` methods of the semantic nodes (`OpApplNode`, `OpDefNode`,
  `SubstInNode`, `InstanceNode`, `LetInNode`, `AssumeNode`,
  `TheoremNode`, `AssumeProveNode`, `NewSymbNode`, `ModuleNode`).

  The levels: 0 constant, 1 state, 2 action, 3 temporal. The level data
  of a node (`ld`):

    * `level`: the level of the node.
    * `lp`: the parameters (constants, operator parameters) that the
      level of the node depends on (`levelParams`).
    * `ap`, `nlp`: all the parameters, and the parameters in non-Leibniz
      positions (`allParams`, `nonLeibnizParams`).
    * `lc`: the maximum level of each parameter (`levelConstraints`).
    * `alc`: for an operator parameter and a position, the minimum of the
      maximum level of the argument (`argLevelConstraints`).
    * `alp`: `{op, i, p}` when the parameter p occurs in the argument i of
      the operator parameter op (`argLevelParams`).

  The data of a definition (`dd`) has also the maximum level and the
  weight of each argument, the `minMaxLevel` and `opLevelCond` tables,
  and the Leibniz flags. The symbols are keys by their ids.
  """

  alias Accord.TLA.Checker.Semantic, as: S

  @empty %{
    level: 0,
    lp: MapSet.new(),
    ap: MapSet.new(),
    nlp: MapSet.new(),
    lc: %{},
    alc: %{},
    alp: MapSet.new(),
    ok: true
  }

  @def_kinds [:builtin, :def, :fun, :theorem, :instance_def]
  @op_def_kinds [:builtin, :def, :fun, :instance_def]
  @keys [:lvl_nodes, :lvl_defs, :lvl_syms, :lvl_mods, :lvl_const, :lvl_insts, :lvl_body]

  @doc """
  Checks the levels of the modules `infos` (in the order of the
  analysis, the root last) and of the instances `insts`. The errors go
  to the list of `Accord.TLA.Checker.Semantic`.
  """
  def check(_root, infos, insts) do
    old = Enum.map(@keys, &{&1, Process.get(&1)})
    Enum.each(@keys, &Process.put(&1, %{}))

    try do
      Enum.each(infos, &module_ld/1)
      Enum.each(insts, &instance_ld/1)
      :ok
    after
      Enum.each(old, fn {k, v} -> if v == nil, do: Process.delete(k), else: Process.put(k, v) end)
    end
  end

  # -- Symbols --

  defp reg(nil), do: nil

  defp reg(%{id: id} = sym) do
    syms = Process.get(:lvl_syms)
    unless Map.has_key?(syms, id), do: Process.put(:lvl_syms, Map.put(syms, id, sym))
    sym
  end

  defp kind(id), do: Process.get(:lvl_syms) |> Map.get(id, %{}) |> Map.get(:kind)

  defp param?(id), do: kind(id) in [:param, :constant, :variable, :new]

  defp def_like?(%{kind: k}), do: k in @def_kinds
  defp op_def?(%{kind: k}), do: k in @op_def_kinds

  # The level of a declaration or a parameter.
  defp sym_level(%{kind: :variable}), do: 1
  defp sym_level(%{kind: :new, new_kind: k}) when k in [:variable, :state], do: 1
  defp sym_level(%{kind: :new, new_kind: :action}), do: 2
  defp sym_level(%{kind: :new, new_kind: :temporal}), do: 3
  defp sym_level(_), do: 0

  # The level parameters of a declaration: a CONSTANT or a parameter is
  # its own parameter.
  defp sym_params(%{kind: k, id: id}) when k in [:constant, :param], do: MapSet.new([id])
  defp sym_params(_), do: MapSet.new()

  # -- Level data --

  defp lc_put(lc, id, l), do: Map.update(lc, id, l, &min(&1, l))
  defp alc_put(alc, key, l), do: Map.update(alc, key, l, &max(&1, l))
  defp lc_all(lc, more), do: Enum.reduce(more, lc, fn {k, l}, lc -> lc_put(lc, k, l) end)
  defp alc_all(alc, more), do: Enum.reduce(more, alc, fn {k, l}, alc -> alc_put(alc, k, l) end)

  # The union of the data of sub-nodes (`levelCheckSubnodes`).
  defp merge(lds) do
    Enum.reduce(lds, @empty, fn ld, acc ->
      %{
        level: max(acc.level, ld.level),
        lp: MapSet.union(acc.lp, ld.lp),
        ap: MapSet.union(acc.ap, ld.ap),
        nlp: MapSet.union(acc.nlp, ld.nlp),
        lc: lc_all(acc.lc, ld.lc),
        alc: alc_all(acc.alc, ld.alc),
        alp: MapSet.union(acc.alp, ld.alp),
        ok: acc.ok and ld.ok
      }
    end)
  end

  # ASSUME and ASSUME/PROVE: a constant in the node can have at most the
  # action level (`addTemporalLevelConstraintToConstants`).
  defp temporal_constraint(ld) do
    lc =
      Enum.reduce(ld.lp, ld.lc, fn id, lc ->
        if kind(id) == :constant, do: lc_put(lc, id, 2), else: lc
      end)

    %{ld | lc: lc}
  end

  # -- Nodes --

  defp ld_of(nil), do: @empty

  defp ld_of(%{id: id} = n) do
    case Map.fetch(Process.get(:lvl_nodes), id) do
      {:ok, ld} ->
        ld

      :error ->
        ld = compute(n)
        Process.put(:lvl_nodes, Map.put(Process.get(:lvl_nodes), id, ld))
        ld
    end
  end

  defp ld_of(_), do: @empty

  defp compute(%{t: :appl} = n), do: appl(n)
  defp compute(%{t: :oparg, op: op}), do: oparg(op)
  defp compute(%{t: :label, body: body}), do: ld_of(body)
  defp compute(%{t: :let} = n), do: let(n)
  defp compute(%{t: :assume_prove} = n), do: assume_prove(n)
  defp compute(%{t: :new} = n), do: new_symb(n)
  defp compute(%{t: :at, except: {:except, f}}), do: %{ld_of(f) | nlp: MapSet.new()}
  defp compute(_), do: @empty

  # An operator argument: the data of the operator.
  defp oparg(op) do
    reg(op)

    if def_like?(op) do
      dd = def_data(op)

      %{
        @empty
        | level: dd.level,
          lp: dd.lp,
          ap: dd.ap,
          lc: dd.lc,
          alc: dd.alc,
          alp: dd.alp,
          ok: dd.ok
      }
    else
      ps = sym_params(op)
      %{@empty | level: sym_level(op), lp: ps, ap: ps}
    end
  end

  # LET: the level of the body, with the constraints of the definitions.
  defp let(%{defs: defs, body: body}) do
    b = ld_of(body)

    dds =
      defs
      |> Enum.map(&S.def_of/1)
      |> Enum.filter(&(&1.kind in [:def, :fun]))
      |> Enum.map(fn d -> {d, def_data(d)} end)

    lc = Enum.reduce(dds, b.lc, fn {_, dd}, lc -> lc_all(lc, dd.lc) end)
    alc = Enum.reduce(dds, b.alc, fn {_, dd}, alc -> alc_all(alc, dd.alc) end)

    alp =
      Enum.reduce(dds, b.alp, fn {d, dd}, alp ->
        ps = MapSet.new(params_of(d), & &1.id)

        dd.alp
        |> Enum.reject(fn {op, _, p} -> op in ps or p in ps end)
        |> MapSet.new()
        |> MapSet.union(alp)
      end)

    ok = Enum.all?(dds, fn {_, dd} -> dd.ok end) and b.ok
    %{b | lc: lc, alc: alc, alp: alp, ok: ok, nlp: MapSet.new()}
  end

  defp assume_prove(%{items: items, goal: goal}) do
    ld = merge(Enum.map(items, &ld_of/1) ++ [ld_of(goal)])
    ld = %{ld | nlp: MapSet.new()}
    if ld.ok, do: temporal_constraint(ld), else: ld
  end

  # NEW x \\in S: the level of the declaration and of S; S is not
  # temporal.
  defp new_symb(%{sym: sym, range: range} = n) do
    reg(sym)
    level = sym_level(sym)

    case range do
      nil ->
        %{@empty | level: level}

      r ->
        rl = ld_of(r)
        level = max(level, rl.level)

        ok =
          if level == 3 do
            S.err(
              4356,
              n[:pos],
              "Level error: a temporal formula is used as the set of a NEW symbol."
            )

            false
          else
            rl.ok
          end

        %{rl | level: level, ok: ok, nlp: MapSet.new()}
    end
  end

  # -- Applications (`OpApplNode.levelCheck`) --

  defp appl(%{op: op} = n) do
    reg(op)
    args = n.args || []
    arg_lds = Enum.map(args, &ld_of/1)

    {bound, ranges} =
      case n do
        %{bounds: bounds} ->
          syms = Enum.flat_map(bounds, fn {ss, _} -> List.wrap(ss) end)
          {syms, Enum.map(bounds, &elem(&1, 1))}

        %{unbounded: syms} ->
          {syms, []}

        _ ->
          {[], []}
      end

    Enum.each(bound, &reg/1)
    range_lds = Enum.map(ranges, &ld_of/1)
    bound_ids = MapSet.new(bound, & &1.id)
    ok = Enum.all?(arg_lds ++ range_lds, & &1.ok)

    ld =
      if def_like?(op) do
        appl_def(n, op, args, arg_lds, range_lds, bound_ids, ok)
      else
        appl_decl(op, arg_lds, ok)
      end

    temporal_checks(n, op, arg_lds, range_lds, ld)
  end

  defp appl_def(n, op, args, arg_lds, range_lds, bound_ids, ok) do
    dd = def_data(op)
    name = op.name
    indexed = Enum.with_index(Enum.zip(args, arg_lds))
    nargs = length(args)

    # The level of each argument; the arguments of an operator argument.
    ok =
      Enum.reduce(indexed, ok, fn {{a, ld}, i}, ok ->
        ok =
          if a != nil and ld.level > max_level(dd, i) do
            if dd.ok and ld.ok,
              do:
                S.err(
                  4205,
                  n[:pos],
                  "Level error in applying operator #{name}: the level of argument #{i + 1} exceeds the maximum level allowed by the operator."
                )

            false
          else
            ok
          end

        case a do
          %{t: :oparg, op: aop} ->
            if def_like?(aop) do
              odd = def_data(aop)

              ok =
                Enum.reduce(0..(odd.arity - 1)//1, ok, fn j, ok ->
                  if max_level(odd, j) < min_max(dd, i, j) do
                    if dd.ok and ld.ok,
                      do:
                        S.err(
                          4272,
                          n[:pos],
                          "Level error in applying operator #{name}: the permitted level of argument #{j + 1} of the operator argument #{i + 1} must be at least #{min_max(dd, i, j)}."
                        )

                    false
                  else
                    ok
                  end
                end)

              for j <- 0..(nargs - 1)//1, k <- 0..(odd.arity - 1)//1, reduce: ok do
                ok ->
                  if olc?(dd, i, j, k) and Enum.at(arg_lds, j).level > max_level(odd, k) do
                    if ld.ok and Enum.at(arg_lds, j).ok,
                      do:
                        S.err(
                          4273,
                          n[:pos],
                          "Level error in applying operator #{name}: the level of argument #{j + 1} exceeds the maximum level allowed by the operator."
                        )

                    false
                  else
                    ok
                  end
              end
            else
              ok
            end

          _ ->
            ok
        end
      end)

    ok =
      Enum.reduce(range_lds, ok, fn r, ok ->
        if r.level > 2 do
          if r.ok,
            do:
              S.err(
                4315,
                n[:pos],
                "Level error in applying operator #{name}: the level of the range of a bound variable exceeds the maximum level allowed by the operator."
              )

          false
        else
          ok
        end
      end)

    # The level.
    level =
      Enum.reduce(indexed, dd.level, fn {{a, ld}, i}, l ->
        if a != nil and weight(dd, i) == 1, do: max(l, ld.level), else: l
      end)

    level = Enum.reduce(range_lds, level, &max(&1.level, &2))

    # levelParams, allParams, nonLeibnizParams.
    lp =
      Enum.reduce(indexed, dd.lp, fn {{a, ld}, i}, lp ->
        if a != nil and weight(dd, i) == 1, do: MapSet.union(lp, ld.lp), else: lp
      end)

    ap = Enum.reduce(arg_lds, dd.ap, &MapSet.union(&2, &1.ap))

    nlp =
      Enum.reduce(indexed, dd.nlp, fn {{_a, ld}, i}, nlp ->
        nlp = MapSet.union(nlp, ld.nlp)
        ii = if dd.arity == -1, do: 0, else: i
        if Enum.at(dd.leib_arg, ii, true), do: nlp, else: MapSet.union(nlp, ld.ap)
      end)

    lp = Enum.reduce(range_lds, lp, &MapSet.union(&2, &1.lp))
    ap = Enum.reduce(range_lds, ap, &MapSet.union(&2, &1.ap))
    nlp = Enum.reduce(range_lds, nlp, &MapSet.union(&2, &1.nlp))
    lp = MapSet.difference(lp, bound_ids)
    ap = MapSet.difference(ap, bound_ids)
    nlp = MapSet.difference(nlp, bound_ids)

    # levelConstraints.
    lc =
      Enum.reduce(arg_lds, dd.lc, fn ld, lc ->
        Enum.reduce(ld.lc, lc, fn {p, l}, lc ->
          if p in bound_ids, do: lc, else: lc_put(lc, p, l)
        end)
      end)

    lc = Enum.reduce(range_lds, lc, &lc_all(&2, &1.lc))

    lc =
      Enum.reduce(indexed, lc, fn {{a, ld}, i}, lc ->
        if a, do: Enum.reduce(ld.lp, lc, &lc_put(&2, &1, max_level(dd, i))), else: lc
      end)

    {lc, nlp} =
      Enum.reduce(indexed, {lc, nlp}, fn {{a, _ld}, i}, {lc, nlp} ->
        case a do
          %{t: :oparg, op: aop} ->
            if def_like?(aop) do
              odd = def_data(aop)

              for j <- 0..(nargs - 1)//1,
                  k <- 0..(odd.arity - 1)//1,
                  olc?(dd, i, j, k),
                  reduce: {lc, nlp} do
                {lc, nlp} ->
                  aj = Enum.at(arg_lds, j)
                  lc = Enum.reduce(aj.lp, lc, &lc_put(&2, &1, max_level(odd, k)))

                  nlp =
                    if not odd.leib and not Enum.at(odd.leib_arg, k, true),
                      do: MapSet.union(nlp, aj.ap),
                      else: nlp

                  {lc, nlp}
              end
            else
              {lc, nlp}
            end

          _ ->
            {lc, nlp}
        end
      end)

    params = dd.params

    get_arg = fn pid ->
      case Enum.find_index(params, &(&1 == pid)) do
        nil -> nil
        i -> Enum.at(args, i)
      end
    end

    lc =
      Enum.reduce(dd.alp, lc, fn {aop, ai, ap_}, lc ->
        case get_arg.(aop) do
          %{t: :oparg, op: o} ->
            if def_like?(o), do: lc_put(lc, ap_, max_level(def_data(o), ai)), else: lc

          _ ->
            lc
        end
      end)

    # argLevelConstraints.
    alc = Enum.reduce(arg_lds ++ range_lds, dd.alc, &alc_all(&2, &1.alc))

    alc =
      Enum.reduce(indexed, alc, fn {{a, _ld}, i}, alc ->
        case a do
          %{t: :oparg, op: aop} ->
            if def_like?(aop) do
              alc
            else
              reg(aop)
              alen = aop.arity || 0

              alc =
                Enum.reduce(0..(alen - 1)//1, alc, &alc_put(&2, {aop.id, &1}, min_max(dd, i, &1)))

              for j <- 0..(nargs - 1)//1, k <- 0..(alen - 1)//1, olc?(dd, i, j, k), reduce: alc do
                alc -> alc_put(alc, {aop.id, k}, Enum.at(arg_lds, j).level)
              end
            end

          _ ->
            alc
        end
      end)

    alc =
      Enum.reduce(dd.alp, alc, fn {aop, ai, _}, alc ->
        case get_arg.(aop) do
          nil -> alc
          a -> alc_put(alc, {aop, ai}, ld_of(a).level)
        end
      end)

    # argLevelParams.
    alp =
      Enum.reduce(arg_lds, MapSet.new(), fn ld, alp ->
        Enum.reduce(ld.alp, alp, fn {_, _, p} = x, alp ->
          if p in bound_ids, do: alp, else: MapSet.put(alp, x)
        end)
      end)

    alp = Enum.reduce(range_lds, alp, &MapSet.union(&2, &1.alp))

    alp =
      Enum.reduce(dd.alp, alp, fn {aop, ai, ap_} = x, alp ->
        case get_arg.(aop) do
          nil ->
            case get_arg.(ap_) do
              nil -> MapSet.put(alp, x)
              a -> Enum.reduce(ld_of(a).lp, alp, &MapSet.put(&2, {aop, ai, &1}))
            end

          %{t: :oparg, op: o} ->
            reg(o)
            if def_like?(o), do: alp, else: MapSet.put(alp, {o.id, ai, ap_})

          _ ->
            alp
        end
      end)

    alp =
      Enum.reduce(indexed, alp, fn {{a, _ld}, i}, alp ->
        case a do
          %{t: :oparg, op: aop} ->
            if def_like?(aop) do
              alp
            else
              alen = aop.arity || 0

              for j <- 0..(nargs - 1)//1, k <- 0..(alen - 1)//1, olc?(dd, i, j, k), reduce: alp do
                alp -> Enum.reduce(Enum.at(arg_lds, j).lp, alp, &MapSet.put(&2, {aop.id, k, &1}))
              end
            end

          _ ->
            alp
        end
      end)

    %{level: level, lp: lp, ap: ap, nlp: nlp, lc: lc, alc: alc, alp: alp, ok: ok and dd.ok}
  end

  # An application of a declared operator (a CONSTANT, a parameter).
  defp appl_decl(op, arg_lds, ok) do
    level = Enum.reduce(arg_lds, sym_level(op), &max(&1.level, &2))
    lp = Enum.reduce(arg_lds, MapSet.new([op.id]), &MapSet.union(&2, &1.lp))
    ap = Enum.reduce(arg_lds, MapSet.new([op.id]), &MapSet.union(&2, &1.ap))
    nlp = Enum.reduce(arg_lds, MapSet.new(), &MapSet.union(&2, &1.nlp))
    lc = Enum.reduce(arg_lds, %{}, &lc_all(&2, &1.lc))

    alc =
      arg_lds
      |> Enum.with_index()
      |> Enum.reduce(%{}, fn {ld, i}, alc ->
        alc |> alc_put({op.id, i}, ld.level) |> alc_all(ld.alc)
      end)

    alp =
      arg_lds
      |> Enum.with_index()
      |> Enum.reduce(MapSet.new(), fn {ld, i}, alp ->
        alp = Enum.reduce(ld.lp, alp, &MapSet.put(&2, {op.id, i, &1}))
        MapSet.union(alp, ld.alp)
      end)

    %{level: level, lp: lp, ap: ap, nlp: nlp, lc: lc, alc: alc, alp: alp, ok: ok}
  end

  # The checks of temporal operators (end of `OpApplNode.levelCheck`).
  defp temporal_checks(n, op, arg_lds, range_lds, ld) do
    name = op.name
    args = n.args || []
    pos = n[:pos]

    ok =
      cond do
        name in ["[]", "<>"] ->
          case args do
            [%{t: :appl, op: %{name: inner}}] ->
              want = if name == "[]", do: "$SquareAct", else: "$AngleAct"

              if hd(arg_lds).level == 2 and inner != want do
                if name == "[]",
                  do: S.err(4310, pos, "[] followed by action not of form [A]_v."),
                  else: S.err(4311, pos, "<> followed by action not of form <<A>>_v.")

                false
              else
                ld.ok
              end

            _ ->
              ld.ok
          end

        name in ["~>", "-+->"] ->
          if Enum.any?(arg_lds, &(&1.level == 2)) do
            S.err(
              4312,
              pos,
              "Action used where only temporal formula or state predicate allowed."
            )

            false
          else
            ld.ok
          end

        name in ["\\land", "\\lor", "=>", "\\equiv", "$ConjList", "$DisjList"] ->
          if Enum.any?(arg_lds, &(&1.level == 3)) and Enum.any?(arg_lds, &(&1.level == 2)) do
            what =
              case name do
                "$ConjList" -> "Conjunction list"
                "$DisjList" -> "Disjunction list"
                other -> other
              end

            S.err(4313, pos, "#{what} has both temporal formula and action as arguments.")
            false
          else
            ld.ok
          end

        ld.level == 3 and name in ["$BoundedExists", "$BoundedForall"] ->
          if Enum.any?(range_lds, &(&1.level == 2)) do
            S.err(4314, pos, "Action-level bound of quantified temporal formula.")
            false
          else
            ld.ok
          end

        true ->
          ld.ok
      end

    %{ld | ok: ok}
  end

  # -- Definitions (`OpDefNode.levelCheck`) --

  defp max_level(dd, i), do: Enum.at(dd.max, if(dd.arity == -1, do: 0, else: i), 3)
  defp weight(dd, i), do: Enum.at(dd.weights, if(dd.arity == -1, do: 0, else: i), 0)

  defp min_max(%{minmax: nil}, _i, _j), do: 0
  defp min_max(dd, i, j), do: dd.minmax |> Enum.at(i, []) |> Enum.at(j, 0)

  defp olc?(dd, i, j, k), do: MapSet.member?(dd.olc, {i, j, k})

  # The parameters of a definition; for `I(x)!Op(y)`, x then y.
  defp params_of(%{kind: :instance_def} = sym), do: sym.inst.params ++ params_of(sym.base_sym)
  defp params_of(sym), do: List.wrap(S.def_of(sym)[:params])

  defp def_data(%{id: id} = sym) do
    case Map.fetch(Process.get(:lvl_defs), id) do
      {:ok, {_, dd}} ->
        dd

      :error ->
        sym = if sym.kind == :instance_def, do: sym, else: S.def_of(sym)
        d0 = init_def(sym)
        put_def(id, {:busy, d0})
        dd = if sym.kind == :builtin, do: d0, else: compute_def(sym, d0)
        put_def(id, {:done, dd})
        dd
    end
  end

  defp put_def(id, v), do: Process.put(:lvl_defs, Map.put(Process.get(:lvl_defs), id, v))

  defp init_def(%{kind: :builtin} = b) do
    {max, weights} =
      if b.arity == -1 do
        {Enum.take(b.max, 1), Enum.take(b.weights, 1)}
      else
        {b.max, b.weights}
      end

    leib_arg = Enum.map(b.weights, &(&1 > 0))

    Map.merge(@empty, %{
      level: b.level,
      arity: b.arity,
      params: [],
      max: max,
      weights: weights,
      leib_arg: leib_arg,
      leib: Enum.all?(leib_arg),
      minmax: nil,
      olc: MapSet.new()
    })
  end

  defp init_def(sym) do
    params = params_of(sym)
    Enum.each(params, &reg/1)
    n = length(params)

    Map.merge(@empty, %{
      arity: n,
      params: Enum.map(params, & &1.id),
      param_syms: params,
      max: List.duplicate(3, n),
      weights: List.duplicate(0, n),
      leib_arg: List.duplicate(true, n),
      leib: true,
      minmax: nil,
      olc: MapSet.new()
    })
  end

  # The data of the body of a definition. For `I!Op`, the body of Op
  # with the substitution of the instance (`SubstInNode`).
  defp body_ld(%{kind: :instance_def, inst: inst, base_sym: base}) do
    key = {inst.id, base.id}

    case Map.fetch(Process.get(:lvl_body), key) do
      {:ok, ld} ->
        ld

      :error ->
        ld = subst_in(inst, body_ld(base))
        Process.put(:lvl_body, Map.put(Process.get(:lvl_body), key, ld))
        ld
    end
  end

  defp body_ld(sym), do: ld_of(S.def_of(sym)[:body])

  defp compute_def(sym, d) do
    body = body_ld(sym)
    params = d.params
    psyms = Map.get(d, :param_syms, [])

    level = max(d.level, body.level)

    max =
      params
      |> Enum.zip(d.max)
      |> Enum.map(fn {p, m} -> if Map.has_key?(body.lc, p), do: min(m, body.lc[p]), else: m end)

    weights =
      params
      |> Enum.zip(d.weights)
      |> Enum.map(fn {p, w} -> if p in body.lp, do: max(w, 1), else: w end)

    minmax =
      Enum.map(psyms, fn ps ->
        Enum.map(0..((ps.arity || 0) - 1)//1, fn j -> Map.get(body.alc, {ps.id, j}, 0) end)
      end)

    olc =
      for {pi, i} <- Enum.with_index(psyms),
          {pj, j} <- Enum.with_index(params),
          k <- 0..((pi.arity || 0) - 1)//1,
          MapSet.member?(body.alp, {pi.id, k, pj}),
          into: MapSet.new(),
          do: {i, j, k}

    pset = MapSet.new(params)
    lp = d.lp |> MapSet.union(body.lp) |> MapSet.difference(pset)
    ap = d.ap |> MapSet.union(body.ap) |> MapSet.difference(pset)
    nlp0 = MapSet.union(d.nlp, body.nlp)

    leib_arg =
      params
      |> Enum.zip(d.leib_arg)
      |> Enum.map(fn {p, l} -> l and p not in nlp0 end)

    nlp = MapSet.difference(nlp0, pset)
    lc = Map.drop(body.lc, params)
    alc = Map.reject(body.alc, fn {{p, _}, _} -> p in pset end)

    alp =
      body.alp
      |> Enum.reject(fn {op, _, p} -> op in pset and p in pset end)
      |> MapSet.new()
      |> MapSet.union(d.alp)

    %{
      d
      | level: level,
        max: max,
        weights: weights,
        minmax: minmax,
        olc: olc,
        lp: lp,
        ap: ap,
        nlp: nlp,
        leib_arg: leib_arg,
        leib: d.leib and Enum.all?(leib_arg),
        lc: lc,
        alc: alc,
        alp: alp,
        ok: body.ok
    }
  end

  # -- Substitutions (`SubstInNode`, `Subst`) --

  defp subst_lds(inst) do
    Enum.map(inst.substs, fn {decl, e} ->
      reg(decl)
      {decl, e, ld_of(e)}
    end)
  end

  defp get_sub(subs, id), do: Enum.find(subs, fn {d, _, _} -> d.id == id end)

  # The parameters that replace p: the parameters of its substitute.
  defp param_set(subs, p) do
    case get_sub(subs, p) do
      nil -> [p]
      {_, _, ld} -> MapSet.to_list(ld.lp)
    end
  end

  defp subst_in(inst, body) do
    subs = subst_lds(inst)

    level =
      Enum.reduce(subs, body.level, fn {d, _, ld}, l ->
        if d.id in body.lp, do: max(l, ld.level), else: l
      end)

    lp =
      Enum.reduce(body.lp, MapSet.new(), fn p, acc ->
        MapSet.union(acc, MapSet.new(param_set(subs, p)))
      end)

    {ap, nlp} =
      Enum.reduce(subs, {body.ap, body.nlp}, fn {d, _, ld}, {ap, nlp} ->
        if d.id in ap do
          ap = ap |> MapSet.delete(d.id) |> MapSet.union(ld.ap)
          nlp = MapSet.union(nlp, ld.nlp)
          nlp = if d.id in nlp, do: nlp |> MapSet.delete(d.id) |> MapSet.union(ld.ap), else: nlp
          {ap, nlp}
        else
          {ap, nlp}
        end
      end)

    const = module_const?(inst.info)
    ok = body.ok and Enum.all?(subs, fn {_, _, ld} -> ld.ok end)

    %{
      level: level,
      lp: lp,
      ap: ap,
      nlp: nlp,
      lc: sub_lc(body, subs, const),
      alc: sub_alc(body, subs),
      alp: sub_alp(body, subs),
      ok: ok
    }
  end

  defp sub_lc(body, subs, const) do
    lc =
      Enum.reduce(body.lc, %{}, fn {p, l}, acc ->
        l =
          cond do
            const -> l
            kind(p) == :constant -> 0
            kind(p) == :variable -> 1
            true -> l
          end

        Enum.reduce(param_set(subs, p), acc, &lc_put(&2, &1, l))
      end)

    Enum.reduce(body.alp, lc, fn {op, i, p}, acc ->
      case get_sub(subs, op) do
        {_, %{t: :oparg, op: o}, _} ->
          if op_def?(o) do
            m = max_level(def_data(o), i)
            Enum.reduce(param_set(subs, p), acc, &lc_put(&2, &1, m))
          else
            acc
          end

        _ ->
          acc
      end
    end)
  end

  defp sub_alc(body, subs) do
    alc =
      Enum.reduce(body.alc, %{}, fn {{p, pos}, l}, acc ->
        case get_sub(subs, p) do
          nil ->
            alc_put(acc, {p, pos}, l)

          {_, %{t: :oparg, op: o}, _} ->
            reg(o)
            if def_like?(o), do: acc, else: alc_put(acc, {o.id, pos}, l)

          _ ->
            acc
        end
      end)

    Enum.reduce(body.alp, alc, fn {op, i, p}, acc ->
      case get_sub(subs, p) do
        nil ->
          acc

        {_, _, pld} ->
          o =
            case get_sub(subs, op) do
              nil -> op
              {_, %{t: :oparg, op: so}, _} -> reg(so).id
              _ -> nil
            end

          if o && param?(o), do: alc_put(acc, {o, i}, pld.level), else: acc
      end
    end)
  end

  defp sub_alp(body, subs) do
    Enum.reduce(body.alp, MapSet.new(), fn {op, i, p} = x, acc ->
      case get_sub(subs, op) do
        nil ->
          MapSet.put(acc, x)

        {_, %{t: :oparg, op: o}, _} ->
          reg(o)

          if def_like?(o),
            do: acc,
            else: Enum.reduce(param_set(subs, p), acc, &MapSet.put(&2, {o.id, i, &1}))

        _ ->
          acc
      end
    end)
  end

  # -- INSTANCE (`InstanceNode.levelCheck`) --

  defp instance_ld(inst) do
    case Map.fetch(Process.get(:lvl_insts), inst.id) do
      {:ok, ld} ->
        ld

      :error ->
        ld = with_module(inst.in, fn -> compute_instance(inst) end)
        Process.put(:lvl_insts, Map.put(Process.get(:lvl_insts), inst.id, ld))
        ld
    end
  end

  defp compute_instance(inst) do
    m = inst.info
    mld = module_ld(m)
    const = module_const?(m)
    subs = subst_lds(inst)
    pos = inst.pos
    mname = m.name

    ok = mld.ok and Enum.all?(subs, fn {_, _, ld} -> ld.ok end)

    ok =
      Enum.reduce(subs, ok, fn {d, e, ld}, ok ->
        ok =
          if not const and ld.level > sym_level(d) do
            if ld.ok,
              do:
                S.err(
                  4245,
                  pos,
                  "Level error in instantiating module '#{mname}': the level of the expression or operator substituted for '#{d.name}' must be at most #{sym_level(d)}."
                )

            false
          else
            ok
          end

        case e do
          %{t: :oparg, op: o} ->
            if op_def?(o) and not def_data(o).leib do
              S.err(
                4244,
                pos,
                "Error in instantiating module '#{mname}': a non-Leibniz operator substituted for '#{d.name}'."
              )
            end

          _ ->
            :ok
        end

        ok
      end)

    ok =
      Enum.reduce(subs, ok, fn {d, e, ld}, ok ->
        plevel = Map.get(mld.lc, d.id)

        ok =
          if plevel != nil and ld.level > plevel do
            if ld.ok,
              do:
                S.err(
                  4245,
                  pos,
                  "Level error in instantiating module '#{mname}': the level of the expression or operator substituted for '#{d.name}' must be at most #{plevel}."
                )

            false
          else
            ok
          end

        case {d.arity || 0, e} do
          {alen, %{t: :oparg, op: o}} when alen > 0 ->
            if op_def?(o) do
              odd = def_data(o)

              Enum.reduce(0..(alen - 1), ok, fn j, ok ->
                alevel = Map.get(mld.alc, {d.id, j})

                if alevel != nil and max_level(odd, j) < alevel do
                  if odd.ok,
                    do:
                      S.err(
                        4246,
                        pos,
                        "Level error in instantiating module '#{mname}': the level of the argument #{j + 1} of the operator #{o.name} must be at least #{alevel}."
                      )

                  false
                else
                  ok
                end
              end)
            else
              ok
            end

          _ ->
            ok
        end
      end)

    ok =
      Enum.reduce(mld.alp, ok, fn {aop, ai, ap_}, ok ->
        with {_, %{t: :oparg, op: o}, _} <- get_sub(subs, aop),
             {_, _, jld} <- get_sub(subs, ap_),
             true <- op_def?(o),
             odd = def_data(o),
             true <- jld.level > max_level(odd, ai) do
          if odd.ok and jld.ok,
            do:
              S.err(
                4247,
                pos,
                "Level error when instantiating module '#{mname}': the level of the argument #{ai} of the operator #{o.name} must be at most #{max_level(odd, ai)}."
              )

          false
        else
          _ -> ok
        end
      end)

    params = MapSet.new(inst.params, & &1.id)
    keep? = fn p -> p not in params end

    lc =
      mld
      |> sub_lc(subs, const)
      |> Map.filter(fn {p, _} -> keep?.(p) end)

    lc =
      Enum.reduce(subs, lc, fn {_, _, ld}, lc ->
        Enum.reduce(ld.lc, lc, fn {p, l}, lc -> if keep?.(p), do: lc_put(lc, p, l), else: lc end)
      end)

    alc = mld |> sub_alc(subs) |> Map.filter(fn {{p, _}, _} -> keep?.(p) end)

    alc =
      Enum.reduce(subs, alc, fn {_, _, ld}, alc ->
        Enum.reduce(ld.alc, alc, fn {{p, _} = k, l}, alc ->
          if keep?.(p), do: alc_put(alc, k, l), else: alc
        end)
      end)

    alp_ok = fn {op, _, p} -> keep?.(op) and keep?.(p) end
    alp = mld |> sub_alp(subs) |> Enum.filter(alp_ok) |> MapSet.new()

    alp =
      Enum.reduce(subs, alp, fn {_, _, ld}, alp ->
        ld.alp |> Enum.filter(alp_ok) |> MapSet.new() |> MapSet.union(alp)
      end)

    %{@empty | lc: lc, alc: alc, alp: alp, ok: ok}
  end

  # -- Modules (`ModuleNode.levelCheck`, `isConstant`) --

  defp with_module(name, fun) do
    saved = Process.get(:sem_module)
    Process.put(:sem_module, name)

    try do
      fun.()
    after
      Process.put(:sem_module, saved)
    end
  end

  # The definitions of a module, with the definitions it extends and
  # instantiates (`getOpDefs`).
  defp op_defs(info) do
    info.ctx
    |> Map.values()
    |> Enum.concat(info.defs)
    |> Enum.filter(&(&1.kind in [:def, :fun, :instance_def]))
    |> Enum.uniq_by(& &1.id)
  end

  defp module_ld(info) do
    case Map.fetch(Process.get(:lvl_mods), info.name) do
      {:ok, ld} ->
        ld

      :error ->
        # A placeholder against loops.
        Process.put(:lvl_mods, Map.put(Process.get(:lvl_mods), info.name, @empty))
        ld = with_module(info.name, fn -> compute_module(info) end)
        Process.put(:lvl_mods, Map.put(Process.get(:lvl_mods), info.name, ld))
        ld
    end
  end

  defp compute_module(info) do
    recursive_section(info.recursive)

    defs = op_defs(info)
    dds = Enum.map(defs, fn d -> {d, def_data(d)} end)
    thm_defs = Enum.filter(info.defs, &(&1.kind == :theorem)) |> Enum.map(&def_data/1)

    thms = Enum.map(info.theorems, &theorem_ld/1)
    assumes = Enum.map(info.assumes, &assume_ld/1)

    insts =
      Process.get(:sem_insts, [])
      |> Enum.filter(&(&1.in == info.name))
      |> Enum.map(&instance_ld/1)

    consts = Enum.filter(info.decls, &(&1.kind == :constant))
    Enum.each(info.decls, &reg/1)
    lp = MapSet.new(consts, & &1.id)
    const = module_const?(info)
    lc = if const, do: %{}, else: Map.new(consts, &{&1.id, 0})

    {lc, alc, alp} =
      Enum.reduce(dds, {lc, %{}, MapSet.new()}, fn {d, dd}, {lc, alc, alp} ->
        ps = params_of(d) |> MapSet.new(& &1.id)

        alp =
          dd.alp
          |> Enum.reject(fn {op, _, p} -> op in ps or p in ps end)
          |> MapSet.new()
          |> MapSet.union(alp)

        {lc_all(lc, dd.lc), alc_all(alc, dd.alc), alp}
      end)

    top = merge(thms ++ assumes ++ insts)
    ok = Enum.all?(dds, fn {_, dd} -> dd.ok end) and Enum.all?(thm_defs, & &1.ok) and top.ok

    %{
      @empty
      | lp: lp,
        ap: lp,
        lc: lc_all(lc, top.lc),
        alc: alc_all(alc, top.alc),
        alp: MapSet.union(alp, top.alp),
        ok: ok
    }
  end

  defp module_const?(info) do
    case Map.fetch(Process.get(:lvl_const), info.name) do
      {:ok, c} ->
        c

      :error ->
        # A placeholder against loops.
        Process.put(:lvl_const, Map.put(Process.get(:lvl_const), info.name, false))

        c =
          with_module(info.name, fn ->
            not Enum.any?(info.decls, &(&1.kind == :variable)) and
              Enum.all?(op_defs(info), &(body_ld(&1).level == 0)) and
              Enum.all?(info.theorems, &(theorem_ld(&1).level == 0))
          end)

        Process.put(:lvl_const, Map.put(Process.get(:lvl_const), info.name, c))
        c
    end
  end

  # The operators of a RECURSIVE section (`ModuleNode.levelCheck`): a
  # first pass with the arguments at the action level, then a second
  # pass with the levels of all the operators of the section.
  defp recursive_section([]), do: :ok

  defp recursive_section(recs) do
    snapshot = {Process.get(:lvl_nodes), Process.get(:lvl_defs), Process.get(:lvl_body)}

    Enum.each(recs, fn r ->
      d = init_def(r)

      put_def(
        r.id,
        {:busy, %{d | max: List.duplicate(2, d.arity), weights: List.duplicate(1, d.arity)}}
      )
    end)

    first =
      Enum.map(recs, fn r ->
        {_, d} = Process.get(:lvl_defs)[r.id]
        dd = compute_def(S.def_of(r), d)
        put_def(r.id, {:busy, dd})

        dd.max
        |> Enum.with_index()
        |> Enum.each(fn {m, j} ->
          if m < 2,
            do:
              S.err(4290, r[:pos], "Argument #{j + 1} of recursive operator #{r.name} is primed.")
        end)

        {r, dd}
      end)

    max_level = first |> Enum.map(fn {_, dd} -> dd.level end) |> Enum.max(fn -> 0 end)
    rlp = Enum.reduce(first, MapSet.new(), fn {_, dd}, acc -> MapSet.union(acc, dd.lp) end)
    rap = Enum.reduce(first, MapSet.new(), fn {_, dd}, acc -> MapSet.union(acc, dd.ap) end)

    # The data of the other nodes from the first pass are not final.
    {nodes, defs, bodies} = snapshot
    Process.put(:lvl_nodes, nodes)
    Process.put(:lvl_body, bodies)

    Process.put(
      :lvl_defs,
      Enum.reduce(first, defs, fn {r, dd}, acc ->
        Map.put(
          acc,
          r.id,
          {:busy,
           %{
             dd
             | level: max(dd.level, max_level),
               lp: MapSet.union(dd.lp, rlp),
               ap: MapSet.union(dd.ap, rap)
           }}
        )
      end)
    )

    Enum.each(recs, fn r ->
      {_, d} = Process.get(:lvl_defs)[r.id]
      put_def(r.id, {:busy, compute_def(S.def_of(r), d)})
    end)

    Enum.each(recs, fn r ->
      {_, d} = Process.get(:lvl_defs)[r.id]
      put_def(r.id, {:done, d})
    end)
  end

  # -- Theorems, assumptions, proofs --

  # ASSUME: a constant formula.
  defp assume_ld(%{body: body, pos: pos}) do
    ld = ld_of(body)

    if ld.level != 0,
      do:
        S.err(
          4206,
          pos,
          "Level error: assumptions must be level 0 (Constant), but this one has level #{ld.level}."
        )

    if ld.ok, do: temporal_constraint(ld), else: ld
  end

  defp theorem_ld(%{body: body} = thm) do
    key = {:thm, body && body.id}

    case Map.fetch(Process.get(:lvl_nodes), key) do
      {:ok, ld} ->
        ld

      :error ->
        ld = statement_check(body, thm[:proof])
        Process.put(:lvl_nodes, Map.put(Process.get(:lvl_nodes), key, ld))
        ld
    end
  end

  # A theorem or a proof step (`TheoremNode.levelCheck`).
  defp statement_check(stmt, proof) do
    sld = stmt_ld(stmt)
    pld = proof_ld(proof)

    case stmt do
      %{t: :pick, ranges: ranges} when sld.level == 3 ->
        Enum.each(ranges, fn r ->
          if r && ld_of(r).level != 0,
            do: S.err(4354, nil, "Non-constant bound of temporal PICK.")
        end)

      _ ->
        :ok
    end

    if sld.level == 3, do: temporal_proof(proof)
    merge([sld, pld])
  end

  defp stmt_ld(nil), do: @empty
  defp stmt_ld(%{t: :take, ranges: rs}), do: merge(Enum.map(rs, &ld_of/1))
  defp stmt_ld(%{t: :witness, args: as}), do: merge(Enum.map(as, &ld_of/1))
  defp stmt_ld(%{t: :have, arg: a}), do: ld_of(a)
  defp stmt_ld(%{t: :pfcase, arg: a}), do: ld_of(a)

  defp stmt_ld(%{t: :pick, ranges: rs, body: b, syms: syms}) do
    ld = merge(Enum.map(Enum.reject(rs, &is_nil/1), &ld_of/1) ++ [ld_of(b)])
    ids = MapSet.new(syms, & &1.id)
    %{ld | lp: MapSet.difference(ld.lp, ids), ap: MapSet.difference(ld.ap, ids)}
  end

  defp stmt_ld(n), do: ld_of(n)

  defp proof_ld(%{t: :proof, steps: steps}) do
    merge(Enum.map(steps, fn s -> statement_check(s.node, s.proof) end))
  end

  defp proof_ld(_), do: @empty

  # A proof of a temporal goal: HAVE, TAKE, WITNESS, and CASE are
  # constant (`LevelCheckTemporal`).
  defp temporal_proof(%{t: :proof, steps: steps}) do
    Enum.each(steps, fn s ->
      case s.node do
        %{t: t} = n when t in [:take, :witness, :have] ->
          if stmt_ld(n).level != 0,
            do: S.err(4352, s.pos, "Non-constant TAKE, WITNESS, or HAVE for temporal goal.")

        %{t: :pfcase} = n ->
          if stmt_ld(n).level != 0, do: S.err(4353, s.pos, "Non-constant CASE for temporal goal.")
          temporal_proof(s.proof)

        nil when s.kind == :qed ->
          temporal_proof(s.proof)

        _ ->
          :ok
      end
    end)
  end

  defp temporal_proof(_), do: :ok
end
