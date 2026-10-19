defmodule Accord.TLA.Checker.Purity do
  @moduledoc """
  Finds the operators that an expression calls, also through
  definitions, instances, and the arguments of operators: the operators
  with side effects (`Print`, `TLCSet`, ...), and the operators whose
  value can change between two evaluations in the same state.
  """

  alias Accord.TLA.Checker.{Context, Eval}

  @effects ~w(Print PrintT TLCSet IOExec IOExecTemplate IOEnvExec IOEnvExecTemplate IOPut IOSerialize Serialize)

  @volatile @effects ++
              ~w(TLCGet TLCGetOrDefault TLCGetAndSet TLCDefer RandomElement RandomSubset
                 RandomSetOfSubsets RandomSubsetSet TestRandomSetOfSubsets JavaTime PickSuccessor
                 JsonSerialize ndJsonSerialize JsonDeserialize ndJsonDeserialize IOEnv
                 IODeserialize Deserialize CounterExample)

  @doc "Tells if an expression calls an operator with side effects."
  def effects?(ctx, e, scope, bound), do: uses?(ctx, e, scope, bound, @effects, MapSet.new())

  @doc """
  Tells if the value of an expression can change between two
  evaluations in the same state: it calls an operator with side effects,
  or an operator whose value is not a function of the state (random
  values, `TLCGet`, the time).
  """
  def volatile?(ctx, e, scope, bound), do: uses?(ctx, e, scope, bound, @volatile, MapSet.new())

  defp uses?(ctx, e, scope, bound, ops, seen) do
    case e do
      {:name, n, _} ->
        name_uses?(ctx, n, scope, bound, ops, seen)

      {:app, n, args, _} ->
        name_uses?(ctx, n, scope, bound, ops, seen) or
          Enum.any?(args, &uses?(ctx, &1, scope, bound, ops, seen))

      {:inst, path, name, args, _} ->
        Enum.any?(args, &uses?(ctx, &1, scope, bound, ops, seen)) or
          Enum.any?(path, fn {_, a} -> uses?(ctx, a, scope, bound, ops, seen) end) or
          inst_uses?(ctx, path, name, scope, bound, ops, seen)

      t when is_tuple(t) ->
        t |> Tuple.to_list() |> Enum.any?(&sub_uses?(ctx, &1, scope, bound, ops, seen))

      l when is_list(l) ->
        Enum.any?(l, &sub_uses?(ctx, &1, scope, bound, ops, seen))

      _ ->
        false
    end
  end

  defp sub_uses?(ctx, x, scope, bound, ops, seen) when is_tuple(x) or is_list(x),
    do: uses?(ctx, x, scope, bound, ops, seen)

  defp sub_uses?(ctx, %{} = m, scope, bound, ops, seen) when not is_struct(m),
    do: m |> Map.values() |> uses?(ctx, scope, bound, ops, seen)

  defp sub_uses?(_ctx, _x, _scope, _bound, _ops, _seen), do: false

  defp inst_uses?(ctx, path, name, scope, bound, ops, seen) do
    case Eval.inst_entry(path, name, %{Eval.new(ctx) | scope: scope, bound: bound}) do
      {:def, d, sid} -> uses?(ctx, d.body, sid, %{}, ops, MapSet.put(seen, {sid, d.name}))
      {:native, _, n} -> n in ops
      _ -> false
    end
  rescue
    # An instance that the analysis cannot follow can have side effects.
    _ -> true
  end

  defp name_uses?(ctx, n, scope, bound, ops, seen) do
    case Map.fetch(bound, n) do
      {:ok, {:thunk, _, e, tscope, tbound, _, _}} ->
        uses?(ctx, e, tscope, tbound, ops, seen)

      {:ok, _} ->
        false

      :error ->
        key = {scope, n}

        if MapSet.member?(seen, key) do
          false
        else
          seen = MapSet.put(seen, key)

          case Context.lookup(ctx, scope, n) do
            {:native, _, name} -> name in ops
            {:def, %{kind: :fun} = d, sid} -> uses?(ctx, d.body, sid, %{}, ops, seen)
            {:def, d, sid} -> uses?(ctx, d.body, sid, %{}, ops, seen)
            {:alias, sid, target} -> name_uses?(ctx, target, sid, %{}, ops, seen)
            {:subst, expr, outer, _} -> uses?(ctx, expr, outer, %{}, ops, seen)
            _ -> false
          end
        end
    end
  end
end
