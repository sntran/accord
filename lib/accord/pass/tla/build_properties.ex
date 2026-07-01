defmodule Accord.Pass.TLA.BuildProperties do
  @moduledoc """
  TLA+ pass: IR → [TLA.Property].

  Maps protocol property checks to TLA+ formulas:

  - `:invariant` → `[]P(vars)` — state invariant
  - `:local_invariant` → `[](state = S /\\ event = E => P)` — conditional
  - `:action` → `[][P(vars, vars')]_vars` — action property
  - `:liveness` → `P ~> Q` with WF/SF — temporal property
  - `:bounded` → `[](x <= N)` — bounded invariant
  - `:correspondence` → auxiliary counter invariant (unkeyed only)
  - `:forbidden` → `[](~P)` — negated invariant
  - `:reachable` → compile-time graph check; annotated in the spec, not
    asserted by TLC
  - `:ordered`, `:precedence`, keyed `:correspondence` → runtime-only:
    rendered as a visible comment block and reported by `mix accord.check`
  """

  alias Accord.IR
  alias Accord.Pass.TLA.Expr
  alias Accord.TLA.{Property, Sessions}

  @spec run(IR.t(), Sessions.t()) :: {:ok, [Property.t()]} | {:error, [Pentiment.Report.t()]}
  def run(%IR{} = ir, sessions \\ %Sessions{}) do
    track_names = MapSet.new(ir.tracks, &Atom.to_string(&1.name))
    ctx = %{ir: ir, track_names: track_names, sessions: sessions}

    results =
      ir.properties
      |> Enum.flat_map(fn prop ->
        Enum.map(prop.checks, fn check ->
          build_property(prop.name, check, ctx)
        end)
      end)
      |> Enum.reject(&is_nil/1)

    errors =
      Enum.flat_map(results, fn
        {:error, reports} -> reports
        %Property{} -> []
      end)

    case errors do
      [] -> {:ok, Enum.filter(results, &match?(%Property{}, &1))}
      errors -> {:error, errors}
    end
  end

  defp build_property(prop_name, %{kind: :invariant} = check, ctx) do
    tla_name = camelize(prop_name)

    with {:ok, expr} <- compile_check_expr(check, "invariant", ctx, "TRUE") do
      %Property{
        name: tla_name,
        kind: :invariant,
        formula: "#{tla_name} == #{Sessions.forall(ctx.sessions, expr)}",
        comment: "invariant: #{prop_name}"
      }
    end
  end

  defp build_property(prop_name, %{kind: :local_invariant} = check, ctx) do
    tla_name = camelize(prop_name) <> camelize(check.spec.state)
    state = Atom.to_string(check.spec.state)
    state_read = Sessions.read(ctx.sessions, "state")

    with {:ok, body} <- compile_check_expr(check, "local invariant", ctx, "TRUE") do
      inner = ~s[(#{state_read} = "#{state}") => (#{body})]

      %Property{
        name: tla_name,
        kind: :invariant,
        formula: "#{tla_name} == #{Sessions.forall(ctx.sessions, inner)}",
        comment: "local invariant: #{prop_name} in state #{state}"
      }
    end
  end

  defp build_property(prop_name, %{kind: :action} = check, ctx) do
    tla_name = camelize(prop_name)

    vars =
      ctx.ir.tracks
      |> Enum.map(fn t -> Atom.to_string(t.name) end)
      |> Enum.join(", ")

    bindings = extract_action_bindings(check.spec.ast)

    with {:ok, body} <-
           compile_check_expr(check, "action property", ctx, "TRUE", bindings) do
      formula = "#{tla_name} == [][#{Sessions.forall(ctx.sessions, body)}]_<<#{vars}>>"

      %Property{
        name: tla_name,
        kind: :temporal,
        formula: formula,
        comment: "action property: #{prop_name}"
      }
    end
  end

  defp build_property(prop_name, %{kind: :liveness} = check, ctx) do
    tla_name = camelize(prop_name)
    trigger = pred_to_tla(check.spec.trigger, ctx.sessions)
    target = pred_to_tla(check.spec.target, ctx.sessions)

    formula = "#{tla_name} == #{Sessions.forall(ctx.sessions, "#{trigger} ~> #{target}")}"

    fairness_tags =
      case Map.get(check.spec, :assuming) do
        nil -> nil
        tags -> Enum.map(tags, &Atom.to_string/1)
      end

    %Property{
      name: tla_name,
      kind: :temporal,
      formula: formula,
      comment: "liveness: #{prop_name}",
      fairness_tags: fairness_tags,
      fairness_strength: Map.get(check.spec, :fairness, :weak)
    }
  end

  defp build_property(prop_name, %{kind: :bounded} = check, ctx) do
    tla_name = camelize(prop_name)
    track = Atom.to_string(check.spec.track)
    max = check.spec.max

    formula =
      "#{tla_name} == " <>
        Sessions.forall(ctx.sessions, "#{Sessions.read(ctx.sessions, track)} =< #{max}")

    %Property{
      name: tla_name,
      kind: :invariant,
      formula: formula,
      comment: "bounded: #{prop_name} (#{track} <= #{max})"
    }
  end

  defp build_property(prop_name, %{kind: :correspondence} = check, ctx) do
    tla_name = camelize(prop_name)
    open = Atom.to_string(check.spec.open)

    if Map.get(check.spec, :by) do
      # Keyed correspondence counts per key value; the model's single
      # global counter cannot express that, so it is runtime-only.
      runtime_only(
        tla_name,
        "correspondence #{open} by :#{check.spec.by} (#{prop_name})"
      )
    else
      # Correspondence requires an auxiliary counter variable.
      # The invariant is that the counter is always >= 0.
      counter_read = Sessions.read(ctx.sessions, "#{open}_pending")

      %Property{
        name: tla_name,
        kind: :invariant,
        formula: "#{tla_name} == #{Sessions.forall(ctx.sessions, "#{counter_read} >= 0")}",
        comment: "correspondence: #{prop_name}"
      }
    end
  end

  defp build_property(prop_name, %{kind: :ordered} = check, _ctx) do
    runtime_only(
      camelize(prop_name),
      "ordered #{inspect(check.spec.event)} by :#{check.spec.by} (#{prop_name})"
    )
  end

  defp build_property(prop_name, %{kind: :precedence} = check, _ctx) do
    runtime_only(
      camelize(prop_name),
      "precedence #{inspect(check.spec.target)} requires " <>
        "#{inspect(check.spec.required)} (#{prop_name})"
    )
  end

  defp build_property(prop_name, %{kind: :forbidden} = check, ctx) do
    tla_name = camelize(prop_name)

    with {:ok, body} <-
           compile_check_expr(check, "forbidden condition", ctx, "FALSE") do
      %Property{
        name: tla_name,
        kind: :invariant,
        formula: "#{tla_name} == #{Sessions.forall(ctx.sessions, "~(#{body})")}",
        comment: "forbidden: #{prop_name}"
      }
    end
  end

  defp build_property(prop_name, %{kind: :exclusive} = check, ctx) do
    tla_name = camelize(prop_name) <> "Exclusive"
    state = Atom.to_string(check.spec.state)

    if Sessions.multi?(ctx.sessions) do
      # The payoff of multi-session checking: mutual exclusion across
      # sessions as a real TLC invariant.
      # Bound variables must not collide with the s1..sN session
      # constants.
      formula =
        "#{tla_name} == \\A si, sj \\in Sessions : " <>
          "(state[si] = \"#{state}\" /\\ state[sj] = \"#{state}\") => si = sj"

      %Property{
        name: tla_name,
        kind: :invariant,
        formula: formula,
        comment: "exclusive: #{prop_name} (at most one session in #{state})"
      }
    else
      # Only expressible across sessions; annotate honestly (see W003).
      %Property{
        name: tla_name,
        kind: :auxiliary,
        formula:
          "\\* exclusive: at most one session in \"#{state}\" — " <>
            "requires multi-session checking (sessions >= 2)",
        comment: "exclusive: #{prop_name}"
      }
    end
  end

  defp build_property(prop_name, %{kind: :distinct} = check, ctx) do
    tla_name = camelize(prop_name) <> "Distinct"
    track = Atom.to_string(check.spec.track)
    empty = render_empty(check.spec.empty)

    if Sessions.multi?(ctx.sessions) do
      formula =
        "#{tla_name} == \\A si, sj \\in Sessions : " <>
          "(si /= sj) => (#{track}[si] = #{empty} \\/ #{track}[si] /= #{track}[sj])"

      %Property{
        name: tla_name,
        kind: :invariant,
        formula: formula,
        comment: "distinct: #{prop_name} (no two sessions share a #{track})"
      }
    else
      %Property{
        name: tla_name,
        kind: :auxiliary,
        formula:
          "\\* distinct: no two sessions share a non-empty #{track} — " <>
            "requires multi-session checking (sessions >= 2)",
        comment: "distinct: #{prop_name}"
      }
    end
  end

  defp build_property(prop_name, %{kind: :reachable} = check, _ctx) do
    tla_name = camelize(prop_name)
    target = Atom.to_string(check.spec.target)

    # Reachability is checked at compile time by graph analysis
    # (ValidateReachability); nothing in the .cfg asserts it, so the
    # comment must not claim TLC verification.
    %Property{
      name: tla_name,
      kind: :auxiliary,
      formula:
        "\\* reachable: #{target} — checked at compile time by graph " <>
          "reachability; not asserted by TLC",
      comment: "reachable: #{prop_name}"
    }
  end

  # Pass through unknown kinds.
  defp build_property(_prop_name, _check, _ctx), do: nil

  defp render_empty(nil), do: "NULL"
  defp render_empty(n) when is_integer(n), do: Integer.to_string(n)
  defp render_empty(a) when is_atom(a), do: ~s("#{a}")
  defp render_empty(s) when is_binary(s), do: ~s("#{s}")

  defp runtime_only(tla_name, description) do
    %Property{
      name: tla_name,
      kind: :runtime_only,
      formula: "\\* runtime-only: #{description}",
      comment: nil
    }
  end

  # Compiles the check's expression AST, or returns the fallback when the
  # check carries no expression.
  defp compile_check_expr(check, context, ctx, fallback, bindings \\ %{}) do
    case check.spec do
      %{ast: ast} when not is_nil(ast) ->
        Expr.compile(ast, bindings,
          ir: ctx.ir,
          code: "E041",
          context: context,
          track_names: ctx.track_names,
          span: check.span,
          render_field: Sessions.render_field(ctx.sessions)
        )

      _ ->
        {:ok, fallback}
    end
  end

  defp pred_to_tla({:in_state, state}, sessions) do
    ~s(#{Sessions.read(sessions, "state")} = "#{state}")
  end

  defp pred_to_tla(other, _sessions), do: inspect(other)

  # Extracts bindings for action property fn params.
  # Maps the "old" param to :current and the "new" param to :primed.
  defp extract_action_bindings({:fn, _, [{:->, _, [[old_var, new_var], _body]}]}) do
    old_name = extract_var_name(old_var)
    new_name = extract_var_name(new_var)

    bindings = %{}
    bindings = if old_name, do: Map.put(bindings, old_name, :current), else: bindings
    bindings = if new_name, do: Map.put(bindings, new_name, :primed), else: bindings
    bindings
  end

  defp extract_action_bindings(_), do: %{}

  defp extract_var_name({name, _meta, ctx}) when is_atom(name) and is_atom(ctx), do: name
  defp extract_var_name(_), do: nil

  defp camelize(name) when is_atom(name) do
    name
    |> Atom.to_string()
    |> String.split("_")
    |> Enum.map(&String.capitalize/1)
    |> Enum.join()
  end
end
