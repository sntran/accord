defmodule Accord.Pass.TLA.Emit do
  @moduledoc """
  TLA+ pass: StateSpace + Actions + Properties → String.

  Pure string generation. Renders a complete `.tla` module and `.cfg`
  file from the compiled TLA+ intermediate representation.
  """

  alias Accord.TLA.{Action, Property, Sessions, StateSpace}

  @spec run(StateSpace.t(), [Action.t()], [Property.t()]) ::
          {:ok, %{tla: String.t(), cfg: String.t()}}
  def run(%StateSpace{} = ss, actions, properties) do
    tla = render_tla(ss, actions, properties)
    cfg = render_cfg(ss, properties)
    {:ok, %{tla: tla, cfg: cfg}}
  end

  # -- TLA+ Module --

  defp render_tla(ss, actions, properties) do
    var_names = Enum.map(ss.variables, & &1.name)
    vars_decl = Enum.join(var_names, ", ")

    # The Sessions set is a constant in the module; its value is bound in
    # the cfg. Model values (including session values) live in ss.constants.
    constant_names =
      ss.constants ++ if(Sessions.multi?(ss.sessions), do: ["Sessions"], else: [])

    constants_decl =
      case constant_names do
        [] -> []
        names -> ["CONSTANTS #{Enum.join(names, ", ")}", ""]
      end

    sections =
      [
        "---- MODULE #{ss.module_name} ----",
        "EXTENDS Integers, Sequences, TLC",
        ""
      ] ++
        constants_decl ++
        [
          "VARIABLES #{vars_decl}",
          "",
          "vars == <<#{vars_decl}>>",
          "",
          render_tla_symmetry(ss, properties),
          render_tla_section("Type invariant", ss.type_invariant),
          render_tla_section("Init predicate", ss.init),
          render_tla_actions(actions),
          render_tla_next(ss, actions),
          render_tla_spec(),
          render_tla_properties(actions, properties),
          render_tla_state_constraint(ss),
          "===="
        ]

    Enum.join(sections, "\n") <> "\n"
  end

  defp render_tla_section(comment, body) do
    """
    \\* #{comment}
    #{body}
    """
  end

  defp render_tla_actions(actions) do
    actions
    |> Enum.map(&render_tla_action/1)
    |> Enum.join("\n")
  end

  defp render_tla_action(%Action{} = action) do
    comment = if action.comment, do: ["\\* #{action.comment}"], else: []

    # Build the action body declaratively.
    preconditions = Enum.map(action.preconditions, &"/\\ #{&1}")

    primed =
      action.primed
      |> Enum.sort_by(fn {k, _} -> k end)
      |> Enum.map(fn {var, expr} -> "/\\ #{var}' = #{expr}" end)

    unchanged =
      case action.unchanged do
        [] -> []
        [single] -> ["/\\ UNCHANGED #{single}"]
        multiple -> ["/\\ UNCHANGED <<#{Enum.join(multiple, ", ")}>>"]
      end

    body_parts = preconditions ++ primed ++ unchanged
    body = Enum.map_join(body_parts, "\n    ", & &1)

    action_def =
      case action.existential_vars do
        [] ->
          "#{action.name} ==\n    #{body}"

        evars ->
          quantifiers =
            Enum.map_join(evars, ", ", fn {var, domain} ->
              "#{var} \\in #{domain}"
            end)

          "#{action.name} ==\n  \\E #{quantifiers} :\n    #{body}"
      end

    lines = comment ++ [action_def]
    Enum.join(lines, "\n") <> "\n"
  end

  # Terminal states have no outgoing actions, so without an explicit
  # self-stutter disjunct every run reaching one would be reported as a
  # deadlock — which is why deadlock checking used to be disabled
  # entirely. Terminating changes no variables (a stuttering step,
  # invisible to <<Next>>_vars), so liveness semantics are unaffected
  # while real deadlocks — stuck non-terminal states, guard exhaustion —
  # become detectable.
  defp render_tla_next(ss, actions) do
    terminating =
      case ss.terminal_states do
        [] ->
          nil

        terminals ->
          set = Enum.map_join(terminals, ", ", &~s("#{&1}"))

          membership =
            if Sessions.multi?(ss.sessions) do
              # Only when every session has finished is the whole system
              # allowed to stutter; otherwise remaining sessions act.
              "\\A #{ss.sessions.var} \\in Sessions : " <>
                "state[#{ss.sessions.var}] \\in {#{set}}"
            else
              "state \\in {#{set}}"
            end

          "\\* Terminal states self-stutter so they are not deadlocks\n" <>
            "Terminating ==\n    /\\ #{membership}\n    /\\ UNCHANGED vars\n"
      end

    disjunct_names =
      Enum.map(actions, & &1.name) ++ if(terminating, do: ["Terminating"], else: [])

    next =
      if disjunct_names == [] do
        "Next == FALSE\n"
      else
        disjuncts = Enum.join(disjunct_names, "\n    \\/ ")

        """
        \\* Next state relation
        Next ==
            \\/ #{disjuncts}
        """
      end

    case terminating do
      nil -> next
      block -> block <> "\n" <> next
    end
  end

  defp render_tla_spec do
    """
    \\* Specification
    Spec == Init /\\ [][Next]_vars
    """
  end

  # Fairness for a single liveness property, scoped to that property.
  #
  # Each liveness formula is emitted as `fairness => (P ~> Q)` and checked
  # against the plain `Spec` (no global fairness), so a property is judged
  # only under the assumptions it declares — never under a sibling's. A
  # property with `assuming:` tags gets per-action WF_vars (SF_vars under
  # `fairness: :strong`) for every action of those tags, plus WF_vars for
  # the internal state-timeout actions (physical timers fire regardless of
  # which property is being checked). Without `assuming:` it falls back to
  # blanket WF_vars(Next), which only rules out infinite stuttering (W005).
  defp property_fairness(prop, actions) do
    if liveness?(prop) do
      # State timeouts are physical timers that fire regardless of which
      # property is being checked, so their weak fairness is a global fact
      # added to every liveness antecedent — not a borrowed `assuming:`.
      internal =
        actions
        |> Enum.filter(& &1.internal)
        |> Enum.map(&"WF_vars(#{&1.name})")

      Enum.uniq(declared_fairness(prop, actions) ++ internal)
    else
      []
    end
  end

  defp declared_fairness(%{fairness_tags: nil}, _actions), do: ["WF_vars(Next)"]

  defp declared_fairness(prop, actions) do
    operator = if prop.fairness_strength == :strong, do: "SF_vars", else: "WF_vars"

    actions
    |> Enum.filter(&(&1.message_tag in prop.fairness_tags))
    |> Enum.map(&"#{operator}(#{&1.name})")
  end

  # Wraps a liveness property's formula with its own fairness assumption
  # as an implication. Non-liveness properties are unchanged.
  defp property_formula(prop, actions) do
    case property_fairness(prop, actions) do
      [] ->
        prop.formula

      conjuncts ->
        [name, body] = String.split(prop.formula, "==", parts: 2)
        antecedent = Enum.join(conjuncts, " /\\ ")
        "#{String.trim_trailing(name)} == (#{antecedent}) => (#{String.trim(body)})"
    end
  end

  defp liveness?(prop) do
    prop.kind == :temporal and String.contains?(prop.formula, "~>")
  end

  defp render_tla_properties(actions, properties) do
    {runtime_only, checked} = Enum.split_with(properties, &(&1.kind == :runtime_only))

    checked_section =
      if checked == [] do
        ""
      else
        props =
          checked
          |> Enum.map(fn prop ->
            comment = if prop.comment, do: "\\* #{prop.comment}\n", else: ""
            "#{comment}#{property_formula(prop, actions)}\n"
          end)
          |> Enum.join("\n")

        "\\* Properties\n#{props}"
      end

    runtime_only_section =
      if runtime_only == [] do
        ""
      else
        lines = Enum.map_join(runtime_only, "\n", & &1.formula)

        "\n\\* Checks enforced by the runtime monitor only — NOT model checked:\n#{lines}\n"
      end

    checked_section <> runtime_only_section
  end

  defp render_tla_state_constraint(%StateSpace{state_constraint: nil}), do: ""

  defp render_tla_state_constraint(%StateSpace{state_constraint: constraint}) do
    "\\* State constraint for bounded model checking\nStateConstraint == #{constraint}\n"
  end

  defp render_tla_symmetry(ss, properties) do
    case active_symmetry(ss, properties) do
      [] ->
        ""

      exprs ->
        "\\* Symmetry reduction over interchangeable model values\n" <>
          "Symmetry == #{Enum.join(exprs, " \\union ")}\n"
    end
  end

  # TLC's symmetry reduction is unsound for liveness checking (it can
  # merge states on a fair cycle), so symmetry is suppressed whenever a
  # ~> property is present.
  defp active_symmetry(%StateSpace{symmetry_exprs: exprs}, properties) do
    if Enum.any?(properties, &liveness?/1) do
      []
    else
      exprs
    end
  end

  # -- CFG File --

  defp render_cfg(ss, properties) do
    # Fairness now lives inside each liveness property as an implication,
    # so every property is checked against the plain Spec.
    sections = [
      "SPECIFICATION Spec",
      "",
      "INVARIANT TypeInvariant"
    ]

    # Add invariant properties.
    invariants =
      properties
      |> Enum.filter(&(&1.kind == :invariant))
      |> Enum.map(&"INVARIANT #{&1.name}")

    # Add temporal properties.
    temporals =
      properties
      |> Enum.filter(&(&1.kind == :temporal))
      |> Enum.map(&"PROPERTY #{&1.name}")

    # Add state constraint for bounded model checking.
    constraint =
      if ss.state_constraint do
        ["", "CONSTRAINT StateConstraint"]
      else
        []
      end

    # Symmetry reduction over model-value sets (suppressed under
    # liveness — unsound with TLC's symmetry reduction).
    symmetry =
      if active_symmetry(ss, properties) == [] do
        []
      else
        ["", "SYMMETRY Symmetry"]
      end

    # Add constant declarations for model values and NULL.
    constants =
      case ss.constants do
        [] -> []
        names -> ["" | Enum.map(names, &"CONSTANT #{&1} = #{&1}")]
      end

    # The Sessions set constant (multi-session only).
    session_set =
      if Sessions.multi?(ss.sessions) do
        values = Enum.join(Sessions.values(ss.sessions), ", ")
        ["CONSTANT Sessions = {#{values}}"]
      else
        []
      end

    all_sections =
      sections ++ invariants ++ temporals ++ constraint ++ symmetry ++ constants ++ session_set

    Enum.join(all_sections, "\n") <> "\n"
  end
end
