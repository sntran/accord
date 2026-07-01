defmodule Accord.Pass.ValidateProperties do
  @moduledoc """
  Validates that property check specs reference valid protocol elements.

  Checks:
  - `:bounded` checks reference a track that exists in `ir.tracks`.
  - `:correspondence` checks reference an open event that appears in some
    transition's `message_pattern`.
  - `:local_invariant` checks reference a state that exists in `ir.states`.
  - `:reachable` checks reference a target state that exists in `ir.states`.
  - `:precedence` checks reference target and required states that both
    exist in `ir.states`.
  """

  alias Accord.IR
  alias Pentiment.Report

  import Accord.Pass.Helpers

  @spec run(IR.t()) :: {:ok, IR.t()} | {:error, [Report.t()]}
  def run(%IR{} = ir) do
    track_names = Enum.map(ir.tracks, & &1.name)
    state_names = Map.keys(ir.states)
    message_tags = collect_message_tags(ir)

    errors =
      Enum.reduce(ir.properties, [], fn property, acc ->
        Enum.reduce(property.checks, acc, fn check, inner_acc ->
          validate_check(check, ir, track_names, state_names, message_tags, inner_acc)
        end)
      end)

    case errors do
      [] -> {:ok, ir}
      errors -> {:error, Enum.reverse(errors)}
    end
  end

  defp validate_check(%IR.Check{kind: :bounded} = check, ir, track_names, _states, _tags, errors) do
    track = check.spec[:track]

    if track in track_names do
      errors
    else
      span = derive_arg_span(check.span, ":#{track}")

      report =
        Report.error("bounded check references undefined track :#{track}")
        |> Report.with_code("E030")
        |> maybe_add_source(ir.source_file)
        |> maybe_add_span_label(span, "track :#{track} is not defined")
        |> Report.with_help("defined tracks are: #{Enum.map_join(track_names, ", ", &":#{&1}")}")

      [report | errors]
    end
  end

  defp validate_check(
         %IR.Check{kind: :correspondence} = check,
         ir,
         _tracks,
         _states,
         tags,
         errors
       ) do
    open_event = check.spec[:open]

    if open_event in tags do
      errors
    else
      span = derive_arg_span(check.span, ":#{open_event}")

      report =
        Report.error("correspondence check references undefined open event :#{open_event}")
        |> Report.with_code("E031")
        |> maybe_add_source(ir.source_file)
        |> maybe_add_span_label(
          span,
          "event :#{open_event} does not appear in any transition"
        )
        |> Report.with_help(
          "defined message tags are: #{Enum.map_join(Enum.sort(tags), ", ", &":#{&1}")}"
        )

      [report | errors]
    end
  end

  defp validate_check(
         %IR.Check{kind: :local_invariant} = check,
         ir,
         _tracks,
         state_names,
         _tags,
         errors
       ) do
    state = check.spec[:state]

    if state in state_names do
      errors
    else
      span = derive_arg_span(check.span, ":#{state}")

      report =
        Report.error("local_invariant check references undefined state :#{state}")
        |> Report.with_code("E032")
        |> maybe_add_source(ir.source_file)
        |> maybe_add_span_label(span, "state :#{state} is not defined")
        |> Report.with_help("defined states are: #{Enum.map_join(state_names, ", ", &":#{&1}")}")

      [report | errors]
    end
  end

  defp validate_check(
         %IR.Check{kind: :reachable} = check,
         ir,
         _tracks,
         state_names,
         _tags,
         errors
       ) do
    target = check.spec[:target]

    if target in state_names do
      errors
    else
      span = derive_arg_span(check.span, ":#{target}")

      report =
        Report.error("reachable check references undefined state :#{target}")
        |> Report.with_code("E033")
        |> maybe_add_source(ir.source_file)
        |> maybe_add_span_label(span, "state :#{target} is not defined")
        |> Report.with_help("defined states are: #{Enum.map_join(state_names, ", ", &":#{&1}")}")

      [report | errors]
    end
  end

  defp validate_check(
         %IR.Check{kind: :precedence} = check,
         ir,
         _tracks,
         state_names,
         _tags,
         errors
       ) do
    target = check.spec[:target]
    required = check.spec[:required]

    errors
    |> validate_precedence_state(target, "target", check, ir, state_names)
    |> validate_precedence_state(required, "required", check, ir, state_names)
  end

  defp validate_check(
         %IR.Check{kind: :exclusive} = check,
         ir,
         _tracks,
         state_names,
         _tags,
         errors
       ) do
    state = check.spec[:state]

    if state in state_names do
      errors
    else
      span = derive_arg_span(check.span, ":#{state}")

      report =
        Report.error("exclusive check references undefined state :#{state}")
        |> Report.with_code("E060")
        |> maybe_add_source(ir.source_file)
        |> maybe_add_span_label(span, "state :#{state} is not defined")
        |> Report.with_help("defined states are: #{Enum.map_join(state_names, ", ", &":#{&1}")}")

      [report | errors]
    end
  end

  defp validate_check(
         %IR.Check{kind: :liveness} = check,
         ir,
         _tracks,
         _states,
         message_tags,
         errors
       ) do
    case Map.get(check.spec, :assuming) do
      nil ->
        errors

      tags ->
        Enum.reduce(tags, errors, fn tag, acc ->
          if MapSet.member?(message_tags, tag) do
            acc
          else
            span = derive_arg_span(check.span, ":#{tag}")

            report =
              Report.error("liveness assuming: references unknown message tag :#{tag}")
              |> Report.with_code("E037")
              |> maybe_add_source(ir.source_file)
              |> maybe_add_span_label(span, "no transition handles :#{tag}")
              |> Report.with_help(
                "known tags: #{Enum.map_join(Enum.sort(message_tags), ", ", &":#{&1}")}"
              )

            [report | acc]
          end
        end)
    end
  end

  defp validate_check(_check, _ir, _tracks, _states, _tags, errors), do: errors

  @doc """
  Non-blocking warnings for property checks, surfaced via `IO.warn`.

  W005: a liveness check without `assuming:` is verified under blanket
  `WF_vars(Next)`, which asserts only "the system does not stutter
  forever". Under that assumption `P ~> Q` holds iff Q is inevitable
  from every reachable P-state — any client loop (ping, retry) or
  terminal state reachable from the trigger fails it.
  """
  @spec warnings(IR.t()) :: [Report.t()]
  def warnings(%IR{} = ir) do
    for property <- ir.properties,
        %IR.Check{kind: :liveness} = check <- property.checks,
        Map.get(check.spec, :assuming) == nil,
        not timeout_discharges?(ir, check.spec.trigger) do
      Report.warning(
        "liveness :#{property.name} has no assuming: — it is checked under blanket " <>
          "weak fairness, where any client loop or reachable terminal state fails it"
      )
      |> Report.with_code("W005")
      |> maybe_add_source(ir.source_file)
      |> maybe_add_span_label(check.span, "declared here")
      |> Report.with_help(
        "name the message tags that drive progress, e.g. " <>
          "liveness in_state(:locked), leads_to: in_state(:unlocked), assuming: [:release]"
      )
    end
  end

  # A state timeout on the trigger state discharges the fairness caveat:
  # the timeout's automatic weak fairness forces the state to be left.
  defp timeout_discharges?(ir, {:in_state, state}) do
    match?(%{state_timeout: {_ms, _target}}, Map.get(ir.states, state))
  end

  defp timeout_discharges?(_ir, _trigger), do: false

  defp validate_precedence_state(errors, state, role, check, ir, state_names) do
    if state in state_names do
      errors
    else
      span = derive_arg_span(check.span, ":#{state}")

      report =
        Report.error("precedence check references undefined #{role} state :#{state}")
        |> Report.with_code("E034")
        |> maybe_add_source(ir.source_file)
        |> maybe_add_span_label(span, "#{role} state :#{state} is not defined")
        |> Report.with_help("defined states are: #{Enum.map_join(state_names, ", ", &":#{&1}")}")

      [report | errors]
    end
  end

  # Collects all message tags from transitions across all states and anystate.
  defp collect_message_tags(%IR{states: states, anystate: anystate}) do
    all_transitions =
      Enum.flat_map(states, fn {_name, state} -> state.transitions end) ++ anystate

    all_transitions
    |> Enum.map(&message_tag/1)
    |> MapSet.new()
  end
end
