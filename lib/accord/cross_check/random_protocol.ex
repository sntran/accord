defmodule Accord.CrossCheck.RandomProtocol do
  @moduledoc """
  Writes random protocols for the cross-check.

  A random protocol is Elixir source code that uses the Accord DSL. The
  generator makes states, tracks, calls with branches, casts, events,
  state timeouts, guards, updates, `where:` constraints, and properties.
  Some protocols have two sessions and shared tracks. The same seed
  always gives the same source.

  The expressions use only forms that the TLA+ translation supports:
  integer literals, track fields, message arguments, reply values, `+`,
  `-`, `*`, `div/2`, `rem/2`, comparisons, `and`, `or`, and `not`.

  The generator also uses the forms where the translation once differed
  from the monitor:

  - branches that accept the same reply or message (first-match
    selection);
  - `div/2` and `rem/2` on negative values;
  - function heads that ignore an argument (`_a`) before one they read;
  - replies with two values, `{:pair, a, b}`, read in an update `case`.
  """

  @doc """
  Gives the source code of the random protocol for `seed`.
  """
  @spec source(integer(), keyword()) :: String.t()
  def source(seed, _opts \\ []) do
    :rand.seed(:exsss, {seed, 101, 7})
    module = module_name(seed)
    sessions = if chance(0.25), do: 2, else: 1
    states = for i <- 0..(between(2, 4) - 1), do: :"s#{i}"

    ctx = %{
      states: states,
      terminal: if(chance(0.4), do: [List.last(states)], else: []),
      tracks: gen_tracks(sessions),
      sessions: sessions,
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

        timeout =
          if chance(0.15),
            do: "    state_timeout 100, goto: :#{pick(ctx.states -- [name])}\n",
            else: ""

        {"  state :#{name} do\n#{timeout}#{Enum.join(blocks)}  end\n", ctx}
      end
    end)
  end

  defp target(ctx), do: pick(ctx.states)

  defp gen_transition(ctx, tag) do
    {args, ctx} = gen_args(ctx, tag)
    ctx = %{ctx | tags: [tag | ctx.tags]}
    env = %{ctx: ctx, ints: for(%{type: :int, name: n} <- args, do: n), terms: terms(args)}

    case pick([:call, :call, :call, :event, :cast_goto, :cast_branches, :cast]) do
      :call -> gen_call(env, tag, args)
      :event -> {gen_step(env, "event", tag, args), ctx}
      :cast_goto -> {gen_step(env, "cast", tag, args), ctx}
      :cast_branches -> {gen_cast_branches(env, tag, args), ctx}
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

  # A function head for a message. An argument that the body does not
  # read is sometimes ignored (`_name`), so that the names after it are
  # not at the position of their list index.
  defp head(tag, args, body) do
    names =
      Enum.map(args, fn %{name: name} ->
        if body =~ ~r/\b#{name}\b/ or not chance(0.5), do: "#{name}", else: "_#{name}"
      end)

    case names do
      [] -> ":#{tag}"
      names -> "{:#{tag}, " <> Enum.join(names, ", ") <> "}"
    end
  end

  defp gen_step(env, keyword, tag, args) do
    {update, bounds} = gen_update(env)
    guard = combine_guard(maybe_bool(env), bounds)

    lines =
      ["    #{keyword} #{message_head(tag, args)} do"] ++
        guard_line(guard, tag, args) ++
        ["      goto :#{target(env.ctx)}"] ++
        update_line(update, tag, args, "tracks") ++ ["    end"]

    Enum.join(lines, "\n") <> "\n"
  end

  defp gen_cast_branches(env, tag, args) do
    {update, bounds} = gen_update(env)
    guard = combine_guard(maybe_bool(env), bounds)

    # Two branches. The second predicate is sometimes `not c` (no overlap)
    # and sometimes an independent predicate or `true` (overlap: the
    # monitor takes the first branch whose `where:` holds).
    first = gen_bool(env, 2)
    second = pick(["not (#{first})", gen_bool(env, 2), "true"])

    lines =
      ["    cast #{message_head(tag, args)} do"] ++
        guard_line(guard, tag, args) ++
        [
          "      branch goto: :#{target(env.ctx)}, where: fn #{head(tag, args, first)}, tracks -> #{first} end",
          "      branch goto: :#{target(env.ctx)}, where: fn #{head(tag, args, second)}, tracks -> #{second} end"
        ] ++
        update_line(update, tag, args, "tracks") ++ ["    end"]

    Enum.join(lines, "\n") <> "\n"
  end

  defp gen_call(env, tag, args) do
    ctx = env.ctx
    n = length(ctx.domains)
    value = :"#{tag}_v#{n}"
    pa = :"#{tag}_pa#{n}"
    pb = :"#{tag}_pb#{n}"

    ctx = %{
      ctx
      | domains:
          [{pb, 0..between(1, 2)}, {pa, 0..between(1, 3)}, {value, 0..between(1, 3)}] ++
            ctx.domains
    }

    env = %{env | ctx: ctx}
    # A `where:` sees only the reply and the tracks.
    where_env = %{env | ints: [value], terms: []}
    pair_where_env = %{env | ints: [pa, pb], terms: []}

    kinds = [:ok, :err, :val, :pair] |> Enum.shuffle() |> Enum.take(between(1, 4))

    branch_lines =
      Enum.flat_map(kinds, fn
        :val ->
          where =
            maybe_where(where_env, fn body -> "{:val, #{value}}" |> keep_used(body, [value]) end)

          # Sometimes a second branch accepts the same replies.
          overlap =
            if chance(0.3),
              do: ["      branch({:val, #{value} :: non_neg_integer()}, goto: :#{target(ctx)})"],
              else: []

          [
            "      branch({:val, #{value} :: non_neg_integer()},\n        goto: :#{target(ctx)}#{where}\n      )"
            | overlap
          ]

        :pair ->
          where =
            maybe_where(pair_where_env, fn body ->
              "{:pair, #{pa}, #{pb}}" |> keep_used(body, [pa, pb])
            end)

          [
            "      branch({:pair, #{pa} :: non_neg_integer(), #{pb} :: non_neg_integer()},\n        goto: :#{target(ctx)}#{where}\n      )"
          ]

        literal ->
          ["      branch :#{literal}, goto: :#{target(ctx)}"]
      end)

    has_values = Enum.any?(kinds, &(&1 in [:val, :pair]))
    reply_env = Map.put(env, :no_bounds, has_values)
    {update_val, _} = gen_update(%{reply_env | ints: [value | env.ints]})
    {update_pair, _} = gen_update(%{reply_env | ints: [pa, pb | env.ints]})
    {update_lit, bounds_lit} = gen_update(reply_env)

    arms =
      (if(:val in kinds and update_val,
         do: ["          #{keep_used("{:val, #{value}}", update_val, [value])} -> #{update_val}"],
         else: []
       ) ++
         if(:pair in kinds and update_pair,
           do: [
             "          #{keep_used("{:pair, #{pa}, #{pb}}", update_pair, [pa, pb])} -> #{update_pair}"
           ],
           else: []
         )) ++ ["          _ -> #{update_lit || "tracks"}"]

    update_body = Enum.join(arms, " ")

    update =
      cond do
        length(arms) == 1 and update_lit == nil ->
          []

        length(arms) > 1 ->
          [
            "      update fn #{head(tag, args, update_body)}, reply, tracks ->",
            "        case reply do"
          ] ++ arms ++ ["        end", "      end"]

        true ->
          ["      update fn #{head(tag, args, update_lit)}, _reply, tracks -> #{update_lit} end"]
      end

    # A bound from a reply update reads the reply, which a guard cannot
    # see. Those updates have no bound.
    guard =
      combine_guard(
        maybe_bool(env),
        if(has_values, do: [], else: bounds_lit)
      )

    lines =
      ["    on #{message_head(tag, args)} do"] ++
        guard_line(guard, tag, args) ++ branch_lines ++ update ++ ["    end"]

    {Enum.join(lines, "\n") <> "\n", ctx}
  end

  defp maybe_where(env, pattern) do
    if chance(0.5) do
      body = gen_bool(env, 2)
      ",\n        where: fn #{pattern.(body)}, tracks -> #{body} end"
    else
      ""
    end
  end

  # Ignores (`_name`) each name in a reply pattern that the body does not
  # read, sometimes.
  defp keep_used(pattern, body, names) do
    Enum.reduce(names, pattern, fn name, acc ->
      if body =~ ~r/\b#{name}\b/ or not chance(0.6),
        do: acc,
        else: String.replace(acc, ~r/\b#{name}\b/, "_#{name}")
    end)
  end

  defp guard_line(nil, _tag, _args), do: []

  defp guard_line(expr, tag, args),
    do: ["      guard fn #{head(tag, args, expr)}, tracks -> #{expr} end"]

  defp update_line(nil, _tag, _args, _tracks), do: []

  defp update_line(expr, tag, args, tracks),
    do: ["      update fn #{head(tag, args, expr)}, #{tracks} -> #{expr} end"]

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

    # Where the guard cannot hold a bound (an update of a call with reply
    # values), an increment is rare: without a bound, the model has no
    # end, and liveness needs a finite model.
    kinds =
      if Map.get(env, :no_bounds, false) and not chance(0.1),
        do: [:const, :value, :value],
        else: [:inc, :inc, :dec, :const, :value]

    case pick(kinds) do
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
          # The left operand can be negative. The right operand is a
          # literal that is not zero, positive or negative.
          "#{op}(#{gen_int(env, depth - 1)}, #{pick([1, 2, 3, -2])})"

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

          :liveness ->
            [trigger, target] = ctx.states |> Enum.shuffle() |> Enum.take(2)

            "    liveness in_state(:#{trigger}), leads_to: in_state(:#{target})#{fairness_opts(ctx)}"

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

  # Fairness for a liveness property: none (weak fairness on all steps),
  # or weak or strong fairness on some message tags.
  defp fairness_opts(ctx) do
    if chance(0.6) do
      tags = ctx.tags |> Enum.uniq() |> Enum.shuffle() |> Enum.take(between(1, 2))
      strong = if chance(0.3), do: ", fairness: :strong", else: ""
      ", assuming: [" <> Enum.map_join(tags, ", ", &":#{&1}") <> "]" <> strong
    else
      ""
    end
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

    [:invariant, :invariant, :local, :forbidden, :liveness, :liveness] ++ ints ++ corr ++ multi
  end
end
