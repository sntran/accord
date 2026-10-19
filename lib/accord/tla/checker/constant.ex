defmodule Accord.TLA.Checker.Constant do
  @moduledoc """
  Finds the definitions of constant level: they use no variable (and no
  prime, ENABLED, action, or temporal operator). TLC evaluates each of
  them one time; the checker keeps the value of each one after the first
  evaluation (see `Accord.TLA.Checker.Eval`). This gives the same effects
  as TLC for operators with side effects (TLCSet, Print), and saves the
  evaluation of the constant sets of a model.

  The analysis of a definition depends on its scope: in an instance, a
  substitution can replace a constant with a state expression.
  """

  alias Accord.TLA.Checker.Context

  @not_constant ~w(TLCGet CounterExample Trace _TLCState _Counts PickSuccessor)

  @doc "Tells if the zero-arity definition `d` in scope `sid` is of constant level."
  def definition?(ctx, sid, d) do
    key = {ctx.id, sid, d.name}
    cache = Process.get(:tla_constant_defs) || %{}

    case Map.fetch(cache, key) do
      {:ok, v} ->
        v

      :error ->
        # A recursive definition is constant when the rest of its body is.
        Process.put(:tla_constant_defs, Map.put(cache, key, true))
        v = d.kind == :op and d.params == [] and expr?(d.body, ctx, sid, MapSet.new())
        Process.put(:tla_constant_defs, Map.put(Process.get(:tla_constant_defs), key, v))
        v
    end
  end

  @doc """
  Tells if an expression of scope `sid` is of constant level. `local`:
  the bound names (they have constant values).
  """
  def expression?(e, ctx, sid, local), do: expr?(e, ctx, sid, MapSet.new(local))

  # `local`: the names that the expression binds (quantifiers, LET, the
  # parameters of a definition).
  defp expr?(e, ctx, sid, local) do
    case e do
      {kind, _} when kind in [:prime, :unchanged, :enabled, :always, :eventually] ->
        false

      {kind, _, _}
      when kind in [
             :box_action,
             :diamond_action,
             :leadsto,
             :wf,
             :sf,
             :temporal_forall,
             :temporal_exists
           ] ->
        false

      {:name, n, _} ->
        name?(n, [], ctx, sid, local)

      {:app, n, args, _} ->
        name?(n, args, ctx, sid, local) and Enum.all?(args, &expr?(&1, ctx, sid, local))

      # An instance: the analysis does not follow it.
      {:inst, _, _, _, _} ->
        false

      {:let, defs, body} ->
        local = Enum.reduce(defs, local, &MapSet.put(&2, &1.name))

        Enum.all?(defs, fn
          %{kind: :instance} ->
            false

          %{kind: :recursive} ->
            true

          %{kind: :fun} = d ->
            binds?(d.binds, ctx, sid, local) and
              expr?(d.body, ctx, sid, bind_names(d.binds, local))

          d ->
            expr?(
              d.body,
              ctx,
              sid,
              Enum.reduce(d.params, local, fn {p, _}, acc -> MapSet.put(acc, p) end)
            )
        end) and expr?(body, ctx, sid, local)

      {kind, binds, body} when kind in [:forall, :exists, :func] ->
        binds?(binds, ctx, sid, local) and expr?(body, ctx, sid, bind_names(binds, local))

      {:set_map, body, binds} ->
        binds?(binds, ctx, sid, local) and expr?(body, ctx, sid, bind_names(binds, local))

      {:set_filter, {target, set}, pred} ->
        expr?(set, ctx, sid, local) and expr?(pred, ctx, sid, bind_names([{target, set}], local))

      {:choose, {target, set}, body} ->
        (set == nil or expr?(set, ctx, sid, local)) and
          expr?(body, ctx, sid, bind_names([{target, set}], local))

      {:lambda, names, body} ->
        expr?(body, ctx, sid, Enum.reduce(names, local, &MapSet.put(&2, &1)))

      t when is_tuple(t) ->
        t |> Tuple.to_list() |> Enum.all?(&sub?(&1, ctx, sid, local))

      _ ->
        true
    end
  end

  defp sub?(x, ctx, sid, local) when is_tuple(x), do: expr?(x, ctx, sid, local)
  defp sub?(x, ctx, sid, local) when is_list(x), do: Enum.all?(x, &sub?(&1, ctx, sid, local))
  defp sub?(_, _ctx, _sid, _local), do: true

  defp binds?(binds, ctx, sid, local),
    do: Enum.all?(binds, fn {_, set} -> set == nil or expr?(set, ctx, sid, local) end)

  defp bind_names(binds, local) do
    Enum.reduce(binds, local, fn
      {{:tuple, names}, _}, acc -> Enum.reduce(names, acc, &MapSet.put(&2, name_of(&1)))
      {name, _}, acc -> MapSet.put(acc, name_of(name))
    end)
  end

  defp name_of({:name, n, _}), do: n
  defp name_of(n) when is_binary(n), do: n

  defp name?(n, _args, ctx, sid, local) do
    if MapSet.member?(local, n), do: true, else: entry?(Context.lookup(ctx, sid, n), ctx)
  end

  defp entry?(entry, ctx) do
    case entry do
      nil ->
        true

      {:var, _} ->
        false

      {:const, _} ->
        true

      # TLC gives these operators a state or action level, so a
      # definition that uses them is not a constant.
      {:native, _, name} ->
        name not in @not_constant

      {:value, _} ->
        true

      {:def, d, sid} ->
        body?(d, ctx, sid)

      {:alias, sid, target} ->
        entry?(Context.lookup(ctx, sid, target), ctx)

      {:subst, expr, outer, frame} ->
        not let_frame?(ctx, frame) and expr?(expr, ctx, outer, MapSet.new())

      _ ->
        false
    end
  end

  # A substitution of an INSTANCE inside LET can give a name of the LET
  # (a state expression), which the analysis does not see.
  defp let_frame?(ctx, frame),
    do: Enum.any?(ctx.let_instances, fn {_, {_, f}} -> f == frame end)

  # A definition with parameters: its body with the parameters as local
  # names (the arguments are checked where it is applied).
  defp body?(%{params: []} = d, ctx, sid), do: definition?(ctx, sid, d)

  defp body?(d, ctx, sid) do
    key = {ctx.id, sid, d.name, :body}
    cache = Process.get(:tla_constant_defs) || %{}

    case Map.fetch(cache, key) do
      {:ok, v} ->
        v

      :error ->
        Process.put(:tla_constant_defs, Map.put(cache, key, true))

        local =
          case d.kind do
            :fun -> bind_names(d.binds, MapSet.new())
            _ -> MapSet.new(d.params, &elem(&1, 0))
          end

        v = expr?(d.body, ctx, sid, local)
        Process.put(:tla_constant_defs, Map.put(Process.get(:tla_constant_defs), key, v))
        v
    end
  end
end
