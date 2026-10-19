defmodule Accord.TLA.Checker.Stdlib do
  @moduledoc """
  The standard modules, as native Elixir code.

  TLC implements the standard modules in Java. This module does the same
  in Elixir, so they need no `.tla` files:

  - `Naturals`, `Integers`
  - `Sequences`, `FiniteSets`, `Bags`
  - `TLC`, `TLCExt`, `Randomization`, `Toolbox`

  `Reals` is known but not supported: its operators raise an error.
  """

  alias Accord.TLA.Checker.{Community, Eval, Value}
  import Value, only: [error: 1]

  @int2 ["+", "-", "*", "^", "\\div", "%", "<", ">", "<=", ">=", ".."]

  @modules %{
    "Naturals" => ["Nat" | @int2],
    "Integers" => ["Nat", "Int", "-." | @int2],
    "Reals" => ["Nat", "Int", "Real", "Infinity", "-.", "/" | @int2],
    "Sequences" => ["Seq", "Len", "\\o", "Append", "Head", "Tail", "SubSeq", "SelectSeq"],
    "FiniteSets" => ["IsFiniteSet", "Cardinality"],
    "Bags" => [
      "IsABag",
      "BagToSet",
      "SetToBag",
      "BagIn",
      "EmptyBag",
      "(+)",
      "(-)",
      "BagUnion",
      "\\sqsubseteq",
      "SubBag",
      "BagOfAll",
      "BagCardinality",
      "CopiesIn"
    ],
    "TLC" => [
      "Print",
      "PrintT",
      "Assert",
      "JavaTime",
      "TLCGet",
      "TLCSet",
      ":>",
      "@@",
      "Permutations",
      "SortSeq",
      "RandomElement",
      "Any",
      "ToString",
      "TLCEval"
    ],
    "TLCExt" => [
      "AssertEq",
      "AssertError",
      "TLCModelValue",
      "TLCNoOp",
      "TLCDefer",
      "TLCCache",
      "TLCGetOrDefault",
      "TLCGetAndSet",
      "PickSuccessor",
      "TLCFP",
      "TLCEvalDefinition",
      "Trace",
      "CounterExample",
      "ToTrace"
    ],
    "_Possible" => ["_Counts", "_CheckName", "_PrintCounts"],
    "Json" => [
      "ToJson",
      "ToJsonArray",
      "ToJsonObject",
      "JsonSerialize",
      "JsonDeserialize",
      "ndJsonSerialize",
      "ndJsonDeserialize"
    ],
    "Randomization" => ["RandomSubset", "RandomSetOfSubsets", "TestRandomSetOfSubsets"],
    "Toolbox" => []
  }

  # Native operators with operator parameters: the arity of each parameter.
  @op_params %{
    "SelectSeq" => [0, 1],
    "SortSeq" => [0, 2],
    "BagOfAll" => [1, 0],
    "TLCCache" => [0, 0],
    "TLCGetAndSet" => [0, 2, 0, 0],
    "AssertError" => [0, 0]
  }

  @doc "Tells if a module is a native standard module."
  def native?(name), do: Map.has_key?(@modules, name)

  @doc "The scope entries of a native module."
  def ops(module) do
    names =
      case module do
        "TLCExt" -> @modules["TLCExt"] ++ @modules["TLC"]
        _ -> Map.fetch!(@modules, module)
      end

    Map.new(names, &{&1, {:native, module, &1}})
  end

  @doc "Tells if `op` is a native operator, for a spec that uses it without EXTENDS."
  def fallback?(op), do: Enum.any?(@modules, fn {_, names} -> op in names end)

  @doc "The arity of each parameter of a native operator."
  def arities(_mod, op, n), do: Map.get(@op_params, op, List.duplicate(0, n))

  @doc "The arities of the parameters of a native operator, or nil when all are 0."
  def op_params(op), do: Map.get(@op_params, op)

  @doc "Calls a native operator by name (any module)."
  def call(op, args, env) do
    {mod, _} = Enum.find(@modules, fn {_, names} -> op in names end) || {nil, nil}
    call_native(mod, op, args, env)
  end

  @doc "Calls a native operator with evaluated arguments."
  def call_native(mod, op, args, env) do
    if mod != nil and (mod == "Json" or Community.module?(mod)),
      do: Community.call(mod, op, args, env),
      else: op(op, args, env)
  rescue
    e in Value.Error -> reraise %{e | module: true}, __STACKTRACE__
  end

  # -- Naturals and Integers --

  defp op("Nat", [], _), do: :nat
  defp op("Int", [], _), do: :int
  defp op("Real", [], _), do: error("Reals are not supported")
  defp op("Infinity", [], _), do: error("Reals are not supported")
  defp op("/", _, _), do: error("Reals are not supported: the operator /")
  defp op("-.", [a], _), do: -int(a)
  # TLC has 32-bit integers: a result out of range is an overflow error.
  defp op("+", [a, b], _), do: checked(int(a) + int(b), a, "+", b)
  defp op("-", [a, b], _), do: checked(int(a) - int(b), a, "-", b)
  defp op("*", [a, b], _), do: checked(int(a) * int(b), a, "*", b)

  defp op("^", [a, b], _) do
    a = int(a)
    b = int(b)

    cond do
      b < 0 -> error("#{a}^#{b}: the exponent is negative")
      a == 0 and b == 0 -> error("0^0 is not defined")
      true -> checked(Integer.pow(a, b), a, "^", b)
    end
  end

  defp checked(n, _a, _op, _b) when n >= -2_147_483_648 and n <= 2_147_483_647, do: n
  defp checked(_n, a, op, b), do: error("Overflow when computing #{a}#{op}#{b}")

  defp op("\\div", [a, b], _) do
    {a, b} = {int(a), int(b)}
    if b == 0, do: error("division by zero")
    Integer.floor_div(a, b)
  end

  defp op("%", [a, b], _) do
    {a, b} = {int(a), int(b)}
    if b <= 0, do: error("the second argument of % must be positive, not #{b}")
    Integer.mod(a, b)
  end

  defp op("<", [a, b], _), do: int(a) < int(b)
  defp op(">", [a, b], _), do: int(a) > int(b)
  defp op("<=", [a, b], _), do: int(a) <= int(b)
  defp op(">=", [a, b], _), do: int(a) >= int(b)
  defp op("..", [a, b], _), do: Value.interval(a, b)

  # -- Sequences --

  defp op("Seq", [s], _), do: {:seq_set, s}
  # A string is also a sequence (of characters) for Len, \o and SubSeq,
  # as in TLC.
  defp op("Len", [s], _) when is_binary(s), do: String.length(s)
  defp op("Len", [s], _), do: s |> seq() |> tuple_size()
  defp op("\\o", [a, b], _) when is_binary(a) and is_binary(b), do: a <> b
  defp op("\\o", [a, b], _), do: {:seq, List.to_tuple(Value.seq_list(a) ++ Value.seq_list(b))}

  defp op("SubSeq", [s, m, n], _) when is_binary(s) do
    {m, n} = {int(m), int(n)}
    if m > n, do: "", else: String.slice(s, (m - 1)..(n - 1)//1)
  end

  defp op("Append", [s, e], _),
    do: {:seq, s |> Value.seq_list() |> Kernel.++([Value.canon(e)]) |> List.to_tuple()}

  defp op("Head", [s], _) do
    case seq(s) do
      {} -> error("Head of the empty sequence")
      t -> elem(t, 0)
    end
  end

  defp op("Tail", [s], _) do
    case seq(s) do
      {} -> error("Tail of the empty sequence")
      t -> {:seq, Tuple.delete_at(t, 0)}
    end
  end

  defp op("SubSeq", [s, m, n], _) do
    t = seq(s)
    {m, n} = {int(m), int(n)}

    cond do
      n < m ->
        {:seq, {}}

      m < 1 or n > tuple_size(t) ->
        error("SubSeq(s, #{m}, #{n}) is out of range for a sequence of length #{tuple_size(t)}")

      true ->
        {:seq, t |> Tuple.to_list() |> Enum.slice((m - 1)..(n - 1)) |> List.to_tuple()}
    end
  end

  defp op("SelectSeq", [s, test], env) do
    {:seq,
     s
     |> Value.seq_list()
     |> Enum.filter(&truth(Eval.apply_op(test, [&1], env)))
     |> List.to_tuple()}
  end

  # -- FiniteSets --

  defp op("IsFiniteSet", [s], _) do
    case s do
      _ -> if Value.set?(s), do: Value.finite?(s), else: error("IsFiniteSet needs a set")
    end
  end

  defp op("Cardinality", [s], _), do: Value.size(s)

  # -- Bags: a bag is a function from elements to positive counts. --

  defp op("EmptyBag", [], _), do: {:seq, {}}

  defp op("IsABag", [b], _) do
    Value.fun?(b) and Enum.all?(Value.pairs(b), fn {_, n} -> is_integer(n) and n > 0 end)
  end

  defp op("BagToSet", [b], _), do: Value.domain(b) |> Value.to_set()

  defp op("SetToBag", [s], _),
    do: s |> Value.enum() |> Map.new(&{Value.canon(&1), 1}) |> Value.fun()

  defp op("BagIn", [e, b], _), do: Value.member?(e, Value.domain(b))

  defp op("CopiesIn", [e, b], _) do
    if Value.member?(e, Value.domain(b)), do: Value.apply_fun(b, e), else: 0
  end

  defp op("(+)", [a, b], _), do: bag_merge(a, b, &checked(&1 + &2, &1, "+", &2))

  defp op("(-)", [a, b], _) do
    a
    |> bag_map()
    |> Enum.map(fn {k, n} -> {k, n - Map.get(bag_map(b), k, 0)} end)
    |> Enum.filter(fn {_, n} -> n > 0 end)
    |> Map.new()
    |> Value.fun()
  end

  defp op("BagUnion", [s], env),
    do: s |> Value.enum() |> Enum.reduce({:seq, {}}, &op("(+)", [&2, &1], env))

  defp op("\\sqsubseteq", [a, b], _) do
    bm = bag_map(b)
    Enum.all?(bag_map(a), fn {k, n} -> n <= Map.get(bm, k, 0) end)
  end

  defp op("SubBag", [b], _) do
    b
    |> bag_map()
    |> Enum.reduce([%{}], fn {k, n}, acc ->
      for m <- acc, c <- 0..n, do: if(c > 0, do: Map.put(m, k, c), else: m)
    end)
    |> Enum.map(&Value.fun/1)
    |> Value.set()
  end

  defp op("BagOfAll", [f, b], env) do
    b
    |> bag_map()
    |> Enum.reduce(%{}, fn {k, n}, acc ->
      Map.update(acc, Value.canon(Eval.apply_op(f, [k], env)), n, &(&1 + n))
    end)
    |> Value.fun()
  end

  defp op("BagCardinality", [b], _),
    do: b |> bag_map() |> Map.values() |> Enum.reduce(0, &checked(&2 + &1, &2, "+", &1))

  # -- TLC --

  defp op("Print", [out, val], _) do
    Value.deep_normalize!(out)
    Value.deep_normalize!(val)
    IO.puts(Value.show(out) <> "  " <> Value.show(val))
    val
  end

  defp op("PrintT", [out], _) do
    IO.puts(Value.show(out))
    true
  end

  defp op("Assert", [val, out], _) do
    if val == true do
      true
    else
      error(
        "The first argument of Assert evaluated to FALSE; the second argument was: " <>
          Value.show(out)
      )
    end
  end

  defp op("JavaTime", [], _), do: System.os_time(:second)

  # Before the model checker starts (while TLC reads the spec), these
  # values do not exist.
  defp op("TLCGet", [key], env) do
    if Process.get(:tla_phase) == :processing and is_binary(key) and
         key in ~w(level distinct queue generated duration diameter config stats spec),
       do: error("TLCGet(#{Value.show(key)}) has no value before the model checker starts")

    case key do
      "level" -> if env.primed, do: env.level + 1, else: env.level
      "distinct" -> Process.get(:tla_stats_distinct, 0)
      "queue" -> Process.get(:tla_stats_queue, 0)
      "generated" -> Process.get(:tla_stats_generated, 0)
      "duration" -> 0
      "diameter" -> env.level
      "config" -> config_record(env)
      "all:named" -> named_registers()
      "all" -> index_registers()
      "stats" -> stats_record(env)
      "-D" <> property -> env.ctx.config |> system_property(property, key)
      other -> register(other)
    end
  end

  defp op("TLCSet", [key, value], _) do
    if is_integer(key) or is_binary(key),
      do: Process.put(:tla_registers, Map.put(Process.get(:tla_registers) || %{}, key, value))

    true
  end

  defp op(":>", [k, v], _), do: Value.fun(%{Value.canon(k) => v})

  defp op("@@", [f, g], _) do
    gm = Map.new(Value.pairs(g))
    fm = Map.new(Value.pairs(f))
    Value.fun(Map.merge(gm, fm))
  end

  defp op("Permutations", [s], _) do
    s
    |> Value.enum()
    |> permutations()
    |> Enum.map(fn perm -> Value.fun(Map.new(Enum.zip(Value.enum(s), perm))) end)
    |> Value.set()
  end

  defp op("SortSeq", [s, less], env) do
    list = Value.seq_list(s)
    sorted = Enum.sort(list, fn a, b -> truth(Eval.apply_op(less, [a, b], env)) or a == b end)
    {:seq, List.to_tuple(sorted)}
  end

  defp op("RandomElement", [s], _) do
    Value.normalize!(s)

    case s |> Value.enum() |> Value.sort() do
      [] -> error("RandomElement of the empty set")
      [x | _] -> x
    end
  end

  defp op("Any", [], _), do: :any
  defp op("ToString", [v], _), do: v |> Value.deep_normalize!() |> Value.show()
  # TLC's TLCEval normalizes its value (see Value.normalize!/1).
  defp op("TLCEval", [v], _), do: Value.deep_normalize!(v)

  # -- TLCExt --

  defp op("AssertEq", [a, b], _) do
    if Value.eq?(a, b) do
      true
    else
      Enum.each(["\"Assertion failed\"", Value.show(a), Value.show(b)], &IO.puts/1)
      false
    end
  end

  defp op("TLCGetOrDefault", [key, default], _) do
    Map.get(Process.get(:tla_registers) || %{}, key, default)
  end

  defp op("TLCGetAndSet", [key, opv, val, default], env) do
    old = Map.get(Process.get(:tla_registers) || %{}, key, default)

    Process.put(
      :tla_registers,
      Map.put(Process.get(:tla_registers) || %{}, key, Eval.apply_op(opv, [old, val], env))
    )

    old
  end

  defp op("PickSuccessor", [_], _), do: true

  defp op("_Counts", [], _),
    do: Map.get(Process.get(:tla_registers) || %{}, "s:_possible", Value.fun(%{}))

  defp op("_CheckName", [name], env) do
    {:fun, counts} = op("_Counts", [], env)
    Map.get(counts, name, 0) > 0
  end

  defp op("_PrintCounts", [], env) do
    IO.puts(Value.show(op("_Counts", [], env)))
    true
  end

  defp op("TLCFP", [v], _), do: :erlang.phash2(Value.canon(v))
  defp op("TLCEvalDefinition", [name], env), do: Eval.eval({:name, name, nil}, env)

  defp op("Trace", [], env) do
    case Process.get(:tla_trace_fun) do
      nil -> error("Trace is not available here")
      fun -> fun.(env)
    end
  end

  defp op("CounterExample", [], _),
    do: Value.record([{"state", MapSet.new()}, {"action", MapSet.new()}])

  defp op("ToTrace", [ce], _) do
    {:fun, m} = ce

    m
    |> Map.fetch!("state")
    |> Value.enum()
    |> Enum.sort_by(&Value.apply_fun(&1, 1))
    |> Enum.map(&Value.apply_fun(&1, 2))
    |> Value.tuple()
  end

  # AssertError(msg, e): TRUE when e fails to evaluate (the checker does
  # not compare its error text with the text of TLC). Called through an
  # operator replacement, e has already a value: FALSE.
  defp op("AssertError", [_msg, {:assert_error, failed}], _), do: failed
  defp op("AssertError", [_msg, _value], _), do: false

  defp op("TLCModelValue", [name], _) do
    v = {:mv, name}
    if Value.model_value_type(v), do: Process.put(:tla_typed_model_values, true)
    v
  end

  defp op("TLCNoOp", [v], _), do: v
  defp op("TLCDefer", [v], _), do: v
  defp op("TLCCache", [v, _key], _), do: v

  # -- Randomization (deterministic: the first subsets) --

  defp op("RandomSubset", [k, s], _) do
    k = int(k)
    if k < 0, do: error("#{k}")

    case s do
      # A large interval: no enumeration.
      {:interval, a, b} -> Value.interval(a, min(b, a + k - 1))
      _ -> s |> Value.enum() |> Value.sort() |> Enum.take(k) |> Value.set()
    end
  end

  defp op("RandomSetOfSubsets", [k, n, s], _) do
    {k, n} = {int(k), int(n)}
    elems = s |> Value.enum() |> Value.sort()

    {:subset, Value.set(elems)}
    |> Value.enum()
    |> Enum.filter(&(MapSet.size(&1) <= n))
    |> Enum.take(k)
    |> Value.set()
  end

  defp op("TestRandomSetOfSubsets", _args, _),
    do: error("TestRandomSetOfSubsets is not supported")

  defp op(name, args, _),
    do: error("the operator #{name} with #{length(args)} arguments is not supported")

  # -- Helpers --

  defp int(n) when is_integer(n), do: n
  defp int(v), do: error("expected an integer, not #{Value.show(v)}")

  defp seq({:seq, t}), do: t
  defp seq(v), do: error("expected a sequence, not #{Value.show(v)}")

  defp truth(true), do: true
  defp truth(false), do: false
  defp truth(v), do: error("expected a boolean, not #{Value.show(v)}")

  defp bag_map(b), do: Map.new(Value.pairs(b))

  defp bag_merge(a, b, f) do
    Map.merge(bag_map(a), bag_map(b), fn _k, x, y -> f.(x, y) end) |> Value.fun()
  end

  defp permutations([]), do: [[]]
  defp permutations(list), do: for(x <- list, rest <- permutations(list -- [x]), do: [x | rest])

  # -- TLCGet --

  defp register(key) when is_integer(key) or is_binary(key) do
    case Map.fetch(Process.get(:tla_registers) || %{}, key) do
      {:ok, v} -> v
      :error -> error("TLCGet(#{Value.show(key)}) has no value")
    end
  end

  defp register(key), do: error("TLCGet(#{Value.show(key)}) is not supported")

  # The named registers ("s:..."), each as a sequence of one value (one
  # worker).
  defp named_registers do
    (Process.get(:tla_registers) || %{})
    |> Enum.filter(fn {k, _} -> is_binary(k) and String.starts_with?(k, "s:") end)
    |> Map.new(fn {k, v} -> {k, Value.tuple([v])} end)
    |> Value.fun()
  end

  # The registers with an integer index, each as a sequence of one value
  # (one worker).
  defp index_registers do
    (Process.get(:tla_registers) || %{})
    |> Enum.filter(fn {k, _} -> is_integer(k) end)
    |> Map.new(fn {k, v} -> {k, Value.tuple([v])} end)
    |> Value.fun()
  end

  defp config_record(env) do
    deadlock = Process.get(:tla_deadlock, env.ctx.config.check_deadlock)

    Value.record([
      {"mode", "bfs"},
      {"deadlock", deadlock},
      {"worker", 1},
      {"seed", "0"},
      {"fingerprint", "0"},
      {"install", ""}
    ])
  end

  defp stats_record(env) do
    Value.record([
      {"diameter", env.level},
      {"distinct", Process.get(:tla_stats_distinct, 0)},
      {"generated", Process.get(:tla_stats_generated, 0)},
      {"queue", Process.get(:tla_stats_queue, 0)},
      {"traces", 0},
      {"duration", 0}
    ])
  end

  # `TLCGet("-Dname")`: a system property of TLC. The checker takes them
  # from the option `:properties`; without a value, the key itself.
  defp system_property(_config, property, key) do
    Map.get(Process.get(:tla_properties) || %{}, property, key)
  end
end
