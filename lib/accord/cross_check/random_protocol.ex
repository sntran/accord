defmodule Accord.CrossCheck.RandomProtocol do
  @moduledoc """
  Writes random protocols for the cross-check.

  A random protocol is Elixir source code that uses the Accord DSL. The
  generator makes states, tracks, calls with branches, casts, events,
  state timeouts, guards, updates, `where:` constraints, and properties.
  Some protocols have two sessions and shared tracks. The same seed
  always gives the same source.

  The expressions use only forms that the TLA+ translation supports:
  integer literals, track fields, message arguments, the reply value,
  `+`, `-`, `*`, `div/2`, `rem/2`, comparisons, `and`, `or`, and `not`.

  By default, the generator does not use forms where the translation is
  known to differ from the monitor (see `known_divergences/0`). With
  `known: true`, it can use them, so that the cross-check finds them.
  """

  @doc """
  The forms where the TLA+ translation is known to differ from the
  runtime monitor. With `known: true`, the generator uses the first two.

  - `:overlap_branches` — two branches that accept the same reply or
    message. The monitor takes the first; the spec takes either.
  - `:negative_div` — `div/2` or `rem/2` with a negative operand. Elixir
    rounds toward zero; TLA+ rounds down.
  - `:underscore_args` — an update or `where:` head that ignores an
    argument (`_a`) before an argument that it reads. The spec reads
    the wrong argument.
  - `:tagged_pairs` — a reply with two values, `{:tag, a, b}`, read in an
    update `case`. The spec drops the update.
  """
  @spec known_divergences() :: [atom()]
  def known_divergences, do: [:overlap_branches, :negative_div, :underscore_args, :tagged_pairs]

  @doc """
  Gives the source code of the random protocol for `seed`.
  """
  @spec source(integer(), keyword()) :: String.t()
  def source(seed, opts \\ []) do
    :rand.seed(:exsss, {seed, 101, 7})
    module = module_name(seed)
    sessions = if chance(0.25), do: 2, else: 1
    states = for i <- 0..(between(2, 4) - 1), do: :"s#{i}"

    ctx = %{
      states: states,
      terminal: if(chance(0.4), do: [List.last(states)], else: []),
      tracks: gen_tracks(sessions),
      sessions: sessions,
      known: Keyword.get(opts, :known, false),
      domains: [],
      tags: []
    }

    {state_blocks, ctx} = gen_states(ctx)
    properties = gen_properties(ctx)

    domain_lines =
      Enum.map(Enum.reverse(ctx.domains), fn {name, domain} ->
        "    domain :#{name}, #{inspect(domain)}"
      end)

    model_lines = if(sessions > 1, do: ["    sessions #{sessions}"], else: []) ++ domain_lines

    model_block =
      if model_lines == [],
        do: "",
        else: "  model do\n#{Enum.join(model_lines, "\n")}\n  end\n"

    """
    defmodule #{inspect(module)} do
      @moduledoc false
      use Accord.Protocol, tla: :warn

      initial :s0

    #{Enum.map_join(ctx.tracks, "\n", &track_line/1)}

    #{model_block}
    #{Enum.join(state_blocks, "\n")}
    #{Enum.join(properties, "\n")}
    end
    """
  end

  @doc """
  Compiles the random protocol for `seed`.

  Gives `{:ok, module, source}`, or `{:error, reason, source}` when the
  protocol does not compile or Accord cannot make its TLA+ spec.
  """
  @spec compile(integer(), keyword()) ::
          {:ok, module(), String.t()} | {:error, String.t(), String.t()}
  def compile(seed, opts \\ []) do
    code = source(seed, opts)
    module = module_name(seed)
    :code.purge(module)
    :code.delete(module)

    {result, _diagnostics} =
      Code.with_diagnostics(fn ->
        try do
          Code.compile_string(code, "random_protocol_#{seed}.ex")
          :ok
        rescue
          e -> {:error, Exception.message(e)}
        end
      end)

    with :ok <- result,
         :ok <- module.__tla_status__() do
      {:ok, module, code}
    else
      {:error, reason} when is_binary(reason) -> {:error, reason, code}
      other -> {:error, "no TLA+ spec: #{inspect(other)}", code}
    end
  end

  @doc "The module name of the random protocol for `seed`."
  @spec module_name(integer()) :: module()
  def module_name(seed), do: Module.concat([Accord.CrossCheck.Random, "P#{seed}"])

  # -- Random helpers --

  defp chance(p), do: :rand.uniform() < p
  defp between(lo, hi), do: lo + :rand.uniform(hi - lo + 1) - 1
  defp pick(list), do: Enum.at(list, :rand.uniform(length(list)) - 1)

  # -- Tracks --

  # A track is %{name, kind, hi, shared}. The kind is :int (0..hi), :mode
  # (an atom in [:a, :b]), or :holder (nil or a model value).
  defp gen_tracks(sessions) do
    for i <- 1..between(1, 3) do
      hi = between(2, 3)

      %{
        name: :"t#{i}",
        kind: pick([:int, :int, :int, :mode, :holder]),
        hi: hi,
        # A default above 0 lets a decrement run in the initial state.
        default: between(0, hi - 1),
        shared: sessions > 1 and chance(0.5)
      }
    end
  end

  defp track_line(%{kind: :int} = t),
    do:
      "  track :#{t.name}, :non_neg_integer, default: #{t.default}, domain: 0..#{t.hi}#{shared(t)}"

  defp track_line(%{kind: :mode} = t),
    do: "  track :#{t.name}, :atom, default: :a, domain: [:a, :b]#{shared(t)}"

  defp track_line(%{kind: :holder} = t),
    do: "  track :#{t.name}, :term, default: nil, domain: {:model_values, 2}#{shared(t)}"

  defp shared(%{shared: true}), do: ", shared: true"
  defp shared(_), do: ""

  defp int_tracks(ctx), do: Enum.filter(ctx.tracks, &(&1.kind == :int))
  defp holder_tracks(ctx), do: Enum.filter(ctx.tracks, &(&1.kind == :holder))

  # -- States and transitions --

  defp gen_states(ctx) do
    Enum.map_reduce(ctx.states, ctx, fn name, ctx ->
      if name in ctx.terminal do
        {"  state :#{name}, terminal: true\n", ctx}
      else
        # The initial state has two or three transitions, so that the
        # model can leave it.
        count = if name == :s0, do: between(2, 3), else: between(1, 3)
        tags = [:m1, :m2, :m3, :m4, :m5] |> Enum.shuffle() |> Enum.take(count)
        {blocks, ctx} = Enum.map_reduce(tags, ctx, &gen_transition(&2, &1))
        timeout = if chance(0.15), do: ", state_timeout: {100, :#{pick(ctx.states -- [name])}}"
        {"  state :#{name}#{timeout} do\n#{Enum.join(blocks)}  end\n", ctx}
      end
    end)
  end

  defp target(ctx), do: pick(ctx.states)

  defp gen_transition(ctx, tag) do
    {args, ctx} = gen_args(ctx, tag)
    ctx = %{ctx | tags: [tag | ctx.tags]}
    env = %{ctx: ctx, ints: for(%{type: :int, name: n} <- args, do: n), terms: terms(args)}
    msg = message_pattern(tag, args)

    case pick([:call, :call, :call, :event, :cast_goto, :cast_branches, :cast]) do
      :call -> gen_call(env, tag, args, msg)
      :event -> {gen_step(env, "event", tag, args, msg), ctx}
      :cast_goto -> {gen_step(env, "cast", tag, args, msg), ctx}
      :cast_branches -> {gen_cast_branches(env, tag, args, msg), ctx}
      :cast -> {"    cast #{message_head(tag, args)}\n", ctx}
    end
  end

  defp terms(args), do: for(%{type: :term, name: n} <- args, do: n)

  # Message arguments: up to two. Each has its own domain in the model
  # block. A term argument has two model values, the same as a holder
  # track, so that an update can put it into the track.
  defp gen_args(ctx, tag) do
    args =
      for i <- 1..pick([0, 0, 1, 1, 2])//1 do
        name = :"#{tag}_a#{i}_#{length(ctx.domains) + i}"

        if holder_tracks(ctx) != [] and chance(0.3),
          do: %{name: name, type: :term, domain: {:model_values, 2}},
          else: %{name: name, type: :int, domain: 0..between(1, 3)}
      end

    {args, %{ctx | domains: Enum.reverse(Enum.map(args, &{&1.name, &1.domain})) ++ ctx.domains}}
  end

  defp message_head(tag, []), do: ":#{tag}"

  defp message_head(tag, args) do
    types = Enum.map_join(args, ", ", &"#{&1.name} :: #{arg_type(&1)}")
    "{:#{tag}, #{types}}"
  end

  defp arg_type(%{type: :int}), do: "non_neg_integer()"
  defp arg_type(%{type: :term}), do: "term()"

  defp message_pattern(tag, []), do: ":#{tag}"
  defp message_pattern(tag, args), do: "{:#{tag}, " <> Enum.map_join(args, ", ", & &1.name) <> "}"

  defp gen_step(env, keyword, tag, args, msg) do
    {update, bounds} = gen_update(env)
    guard = combine_guard(maybe_bool(env), bounds)

    lines =
      ["    #{keyword} #{message_head(tag, args)} do"] ++
        guard_line(guard, msg) ++
        ["      goto :#{target(env.ctx)}"] ++
        update_line(update, "fn #{msg}, tracks ->") ++ ["    end"]

    Enum.join(lines, "\n") <> "\n"
  end

  defp gen_cast_branches(env, tag, args, msg) do
    {update, bounds} = gen_update(env)
    guard = combine_guard(maybe_bool(env), bounds)

    # Two branches with exclusive predicates, `c` and `not c`. With known
    # divergences, the second branch can accept every message.
    cond_expr = gen_bool(env, 2)
    second = if env.ctx.known and chance(0.5), do: "true", else: "not (#{cond_expr})"

    lines =
      ["    cast #{message_head(tag, args)} do"] ++
        guard_line(guard, msg) ++
        [
          "      branch goto: :#{target(env.ctx)}, where: fn #{msg}, tracks -> #{cond_expr} end",
          "      branch goto: :#{target(env.ctx)}, where: fn #{msg}, tracks -> #{second} end"
        ] ++
        update_line(update, "fn #{msg}, tracks ->") ++ ["    end"]

    Enum.join(lines, "\n") <> "\n"
  end

  defp gen_call(env, tag, args, msg) do
    ctx = env.ctx
    value = :"#{tag}_v#{length(ctx.domains)}"
    ctx = %{ctx | domains: [{value, 0..between(1, 3)} | ctx.domains]}
    env = %{env | ctx: ctx}
    reply_env = %{env | ints: [value | env.ints]}
    # A `where:` sees only the reply and the tracks.
    where_env = %{env | ints: [value], terms: []}

    kinds = [:ok, :err, :val] |> Enum.shuffle() |> Enum.take(between(1, 3))

    branch_lines =
      Enum.flat_map(kinds, fn
        :val ->
          where =
            if chance(0.5),
              do:
                ",\n        where: fn {:val, #{value}}, tracks -> #{gen_bool(where_env, 2)} end",
              else: ""

          overlap =
            if ctx.known and chance(0.4),
              do: ["      branch({:val, #{value} :: non_neg_integer()}, goto: :#{target(ctx)})"],
              else: []

          [
            "      branch({:val, #{value} :: non_neg_integer()},\n        goto: :#{target(ctx)}#{where}\n      )"
            | overlap
          ]

        literal ->
          ["      branch :#{literal}, goto: :#{target(ctx)}"]
      end)

    {update_val, bounds_val} = gen_update(reply_env)
    {update_lit, bounds_lit} = gen_update(env)

    update =
      cond do
        update_val == nil and update_lit == nil ->
          []

        :val in kinds ->
          [
            "      update fn #{msg}, reply, tracks ->",
            "        case reply do",
            "          {:val, #{value}} -> #{update_val || "tracks"}",
            "          _ -> #{update_lit || "tracks"}",
            "        end",
            "      end"
          ]

        true ->
          ["      update fn #{msg}, _reply, tracks -> #{update_lit || "tracks"} end"]
      end

    # A bound from the reply update reads the reply value, which a guard
    # cannot see. That update has no bound.
    _ = bounds_val
    guard = combine_guard(maybe_bool(env), if(:val in kinds, do: [], else: bounds_lit))

    lines =
      ["    on #{message_head(tag, args)} do"] ++
        guard_line(guard, msg) ++ branch_lines ++ update ++ ["    end"]

    {Enum.join(lines, "\n") <> "\n", ctx}
  end

  defp guard_line(nil, _msg), do: []
  defp guard_line(expr, msg), do: ["      guard fn #{msg}, tracks -> #{expr} end"]

  defp update_line(nil, _head), do: []
  defp update_line(expr, head), do: ["      update #{head} #{expr} end"]

  # Most transitions have no guard. Many random guards are false in the
  # initial state, and a model that cannot leave its initial state is a
  # weak test.
  defp maybe_bool(env), do: if(chance(0.3), do: gen_bool(env, 2))

  defp combine_guard(nil, []), do: nil

  defp combine_guard(expr, bounds),
    do: Enum.join(Enum.reject([expr | bounds], &is_nil/1), " and ")

  # -- Updates --

  # Gives `{update_expression | nil, guard_bounds}`. Most increments add
  # the bound `tracks.t < hi` to the guard, so that most models stay
  # finite. An update without a bound can leave the domain. Then the model
  # has a TypeInvariant violation.
  defp gen_update(env) do
    if chance(0.25) do
      {nil, []}
    else
      {pairs, bounds} =
        env.ctx.tracks
        |> Enum.shuffle()
        |> Enum.take(between(1, 2))
        |> Enum.map(&gen_assignment(env, &1))
        |> Enum.unzip()

      {"%{tracks | " <> Enum.join(pairs, ", ") <> "}", Enum.reject(bounds, &is_nil/1)}
    end
  end

  defp gen_assignment(env, %{kind: :int, name: name, hi: hi}) do
    bound = fn expr -> if chance(0.9), do: expr end

    case pick([:inc, :inc, :dec, :const, :value]) do
      :inc ->
        {"#{name}: tracks.#{name} + 1", bound.("tracks.#{name} < #{hi}")}

      :dec ->
        {"#{name}: tracks.#{name} - 1", bound.("tracks.#{name} > 0")}

      :const ->
        {"#{name}: #{between(0, hi)}", nil}

      :value ->
        {"#{name}: #{pick(Enum.map(env.ints, &to_string/1) ++ ["#{between(0, hi)}"])}", nil}
    end
  end

  defp gen_assignment(_env, %{kind: :mode, name: name}),
    do: {"#{name}: #{pick([":a", ":b"])}", nil}

  defp gen_assignment(env, %{kind: :holder, name: name}),
    do: {"#{name}: #{pick(["nil" | Enum.map(env.terms, &to_string/1)])}", nil}

  # -- Expressions --

  defp gen_int(env, depth) do
    leaves =
      ["#{between(0, 3)}"] ++
        Enum.map(int_tracks(env.ctx), &"tracks.#{&1.name}") ++ Enum.map(env.ints, &to_string/1)

    if depth <= 0 or chance(0.6) do
      pick(leaves)
    else
      case pick([:+, :-, :*, :div, :rem]) do
        :* ->
          "(#{gen_int(env, depth - 1)} * #{between(0, 2)})"

        op when op in [:div, :rem] ->
          # Without known divergences, the left operand is a literal or a
          # message value (never negative), and the right operand is a
          # positive literal. A track is not safe: an update without a
          # bound can make it negative.
          left =
            if env.ctx.known,
              do: gen_int(env, depth - 1),
              else: pick(["#{between(0, 3)}" | Enum.map(env.ints, &to_string/1)])

          "#{op}(#{left}, #{between(1, 3)})"

        op ->
          "(#{gen_int(env, depth - 1)} #{op} #{gen_int(env, depth - 1)})"
      end
    end
  end

  defp gen_bool(env, depth) do
    comparisons = ["==", "!=", "<", "<=", ">", ">="]

    atomic =
      [fn -> "#{gen_int(env, 1)} #{pick(comparisons)} #{gen_int(env, 1)}" end] ++
        Enum.flat_map(env.ctx.tracks, fn
          %{kind: :mode, name: n} ->
            [fn -> "tracks.#{n} #{pick(["==", "!="])} #{pick([":a", ":b"])}" end]

          %{kind: :holder, name: n} ->
            [fn -> "tracks.#{n} #{pick(["==", "!="])} #{pick(["nil" | env_terms(env)])}" end]

          _ ->
            []
        end)

    if depth <= 0 or chance(0.5) do
      pick(atomic).()
    else
      case pick([:and, :or, :not]) do
        :not -> "not (#{gen_bool(env, depth - 1)})"
        op -> "(#{gen_bool(env, depth - 1)} #{op} #{gen_bool(env, depth - 1)})"
      end
    end
  end

  defp env_terms(env), do: Enum.map(Map.get(env, :terms, []), &to_string/1)

  # -- Properties --

  defp gen_properties(ctx) do
    env = %{ctx: ctx, ints: [], terms: []}

    1..between(1, 3)
    |> Enum.map(fn i ->
      body =
        case pick(property_kinds(ctx)) do
          :invariant ->
            "    invariant fn tracks -> #{gen_bool(env, 2)} end"

          :local ->
            "    invariant :#{pick(ctx.states)}, fn _msg, tracks -> #{gen_bool(env, 2)} end"

          :forbidden ->
            "    forbidden fn tracks -> #{gen_bool(env, 1)} end"

          :bounded ->
            t = pick(int_tracks(ctx))
            "    bounded :#{t.name}, max: #{between(1, t.hi)}"

          :action ->
            t = pick(int_tracks(ctx))

            "    action fn old, new -> new.#{t.name} #{pick([">=", "<=", "!="])} old.#{t.name} end"

          :correspondence ->
            # One correspondence for each protocol: two checks with the same
            # open event and different close sets do not compile (E038).
            [open, close] = ctx.tags |> Enum.uniq() |> Enum.sort() |> Enum.take(2)
            "    correspondence :#{open}, [:#{close}]"

          :exclusive ->
            "    exclusive :#{pick(ctx.states -- ctx.terminal)}"

          :distinct ->
            t = pick(Enum.reject(ctx.tracks, & &1.shared))
            "    distinct :#{t.name}, empty: #{empty(t)}"
        end

      "  property :p#{i} do\n#{body}\n  end\n"
    end)
    |> Enum.uniq()
  end

  defp empty(%{kind: :int}), do: "0"
  defp empty(%{kind: :mode}), do: ":a"
  defp empty(%{kind: :holder}), do: "nil"

  defp property_kinds(ctx) do
    ints = if int_tracks(ctx) != [], do: [:bounded, :action], else: []
    corr = if length(Enum.uniq(ctx.tags)) >= 2, do: [:correspondence], else: []
    own = Enum.any?(ctx.tracks, &(not &1.shared))

    multi =
      if ctx.sessions > 1,
        do: [:exclusive] ++ if(own, do: [:distinct], else: []),
        else: []

    [:invariant, :invariant, :local, :forbidden] ++ ints ++ corr ++ multi
  end
end
