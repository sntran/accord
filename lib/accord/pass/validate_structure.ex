defmodule Accord.Pass.ValidateStructure do
  @moduledoc """
  Validates the structural well-formedness of the IR.

  Checks:
  - Initial state exists in the state map.
  - All `goto` targets reference declared states (branches and event
    targets alike).
  - Terminal states have no transitions.
  - Events declare no branches (E004) — they are one-way pushes.
  - No duplicate state names (enforced by map, but checked for clarity).
  """

  alias Accord.IR
  alias Pentiment.Report

  import Accord.Pass.Helpers

  @spec run(IR.t()) :: {:ok, IR.t()} | {:error, [Report.t()]}
  def run(%IR{} = ir) do
    errors =
      []
      |> check_initial_exists(ir)
      |> check_goto_targets(ir)
      |> check_terminal_no_transitions(ir)
      |> check_events_branchless(ir)
      |> check_state_timeouts(ir)

    case errors do
      [] -> {:ok, ir}
      errors -> {:error, Enum.reverse(errors)}
    end
  end

  defp check_initial_exists(errors, %IR{initial: initial, states: states} = ir) do
    if Map.has_key?(states, initial) do
      errors
    else
      report =
        Report.error("initial state :#{initial} is not defined")
        |> Report.with_code("E001")
        |> maybe_add_source(ir.source_file)
        |> Report.with_help(
          "defined states are: #{states |> Map.keys() |> Enum.map_join(", ", &":#{&1}")}"
        )

      [report | errors]
    end
  end

  defp check_goto_targets(errors, %IR{states: states} = ir) do
    state_names = Map.keys(states)

    all_transitions =
      Enum.flat_map(states, fn {_name, state} -> state.transitions end) ++ ir.anystate

    Enum.reduce(all_transitions, errors, fn transition, acc ->
      acc = check_to_target(acc, transition, state_names, ir)

      Enum.reduce(transition.branches, acc, fn branch, inner_acc ->
        target = branch.next_state

        if target == :__same__ or target in state_names do
          inner_acc
        else
          span = branch.next_state_span || transition.span

          report =
            Report.error("undefined state reference :#{target}")
            |> Report.with_code("E002")
            |> maybe_add_source(ir.source_file)
            |> maybe_add_span_label(span, "goto target :#{target} is not defined")
            |> Report.with_help(
              "defined states are: #{Enum.map_join(state_names, ", ", &":#{&1}")}"
            )

          [report | inner_acc]
        end
      end)
    end)
  end

  # Events and state-changing casts both carry a `to` goto target.
  defp check_to_target(errors, %{kind: kind, to: target} = transition, state_names, ir)
       when kind in [:event, :cast] and target != nil do
    if target == :__same__ or target in state_names do
      errors
    else
      label = if kind == :cast, do: "cast", else: "event"

      report =
        Report.error("undefined state reference :#{target}")
        |> Report.with_code("E002")
        |> maybe_add_source(ir.source_file)
        |> maybe_add_span_label(transition.span, "#{label} goto target :#{target} is not defined")
        |> Report.with_help("defined states are: #{Enum.map_join(state_names, ", ", &":#{&1}")}")

      [report | errors]
    end
  end

  defp check_to_target(errors, _transition, _state_names, _ir), do: errors

  defp check_terminal_no_transitions(errors, %IR{states: states} = ir) do
    Enum.reduce(states, errors, fn {_name, state}, acc ->
      if state.terminal and state.transitions != [] do
        report =
          Report.error("terminal state :#{state.name} has transitions")
          |> Report.with_code("E003")
          |> maybe_add_source(ir.source_file)
          |> maybe_add_span_label(state.span, "declared as terminal here")
          |> Report.with_help("terminal states cannot have transitions")

        [report | acc]
      else
        acc
      end
    end)
  end

  # State timeouts: the target must exist (E002), differ from the state
  # itself (firing into the same state would neither cancel nor re-arm
  # the timer), and terminal states arm no timers (E005).
  defp check_state_timeouts(errors, %IR{states: states} = ir) do
    state_names = Map.keys(states)

    Enum.reduce(states, errors, fn
      {_name, %{state_timeout: nil}}, acc ->
        acc

      {name, %{state_timeout: {_ms, target}} = state}, acc ->
        cond do
          state.terminal ->
            report =
              Report.error("terminal state :#{name} cannot arm a state_timeout")
              |> Report.with_code("E005")
              |> maybe_add_source(ir.source_file)
              |> maybe_add_span_label(state.span, "declared as terminal here")

            [report | acc]

          target == name ->
            report =
              Report.error("state_timeout in :#{name} must target a different state")
              |> Report.with_code("E005")
              |> Report.with_help(
                "a timeout firing into the same state would neither cancel nor re-arm"
              )
              |> maybe_add_source(ir.source_file)
              |> maybe_add_span_label(state.span, "state defined here")

            [report | acc]

          target not in state_names ->
            report =
              Report.error("undefined state reference :#{target}")
              |> Report.with_code("E002")
              |> maybe_add_source(ir.source_file)
              |> maybe_add_span_label(
                state.span,
                "state_timeout target :#{target} is not defined"
              )
              |> Report.with_help(
                "defined states are: #{Enum.map_join(state_names, ", ", &":#{&1}")}"
              )

            [report | acc]

          true ->
            acc
        end
    end)
  end

  # The DSL already rejects this at macro time; the pass check covers
  # hand-built IRs.
  defp check_events_branchless(errors, %IR{states: states} = ir) do
    all_transitions =
      Enum.flat_map(states, fn {_name, state} -> state.transitions end) ++ ir.anystate

    Enum.reduce(all_transitions, errors, fn transition, acc ->
      if transition.kind == :event and transition.branches != [] do
        report =
          Report.error("event transitions cannot declare replies or branches")
          |> Report.with_code("E004")
          |> maybe_add_source(ir.source_file)
          |> maybe_add_span_label(transition.span, "declared here")
          |> Report.with_help("events are one-way pushes; use goto: for the target state")

        [report | acc]
      else
        acc
      end
    end)
  end
end
