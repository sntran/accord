defmodule Accord.Test.ExerciserFailure do
  @moduledoc """
  Exception raised when the protocol exerciser detects a mismatch
  between expected and actual outcomes.

  The message is a single pentiment diagnostic: the generated session
  leading up to the failure is rendered as notes ahead of the violation's
  own notes and help, with source spans when a compiled protocol is
  available.
  """

  alias Accord.Violation

  defexception [:steps, :property_violations, :compiled]

  @type outcome :: :ok | {:violation, atom(), atom()} | :session_ended | :skipped
  @type step :: %{
          command: term(),
          state: atom(),
          tracks: map(),
          transition: term(),
          message: term(),
          expected: outcome(),
          actual: term(),
          passed: boolean()
        }

  @type t :: %__MODULE__{
          steps: [step()],
          property_violations: [Violation.t()],
          compiled: Accord.Monitor.Compiled.t() | nil
        }

  @impl true
  def message(%__MODULE__{} = e) do
    failing = Enum.find(e.steps, &(not &1.passed))
    session = session_notes(e)
    prop_detail = format_property_violations(e.property_violations, e.compiled)
    format_failing_step(failing, e.compiled, session) <> prop_detail
  end

  # -- The session, as notes --
  #
  # One note per applied step, preceded by the protocol under test, so the
  # diagnostic below carries everything the reader needs: what was sent, in
  # which state, what came back, and where it stopped matching the contract.

  defp session_notes(%__MODULE__{steps: steps, compiled: compiled}) do
    header =
      case compiled do
        %{ir: %{name: name}} -> ["exerciser session against #{inspect(name)}"]
        _ -> ["exerciser session"]
      end

    lines =
      steps
      |> Enum.with_index(1)
      |> Enum.map(fn {step, idx} ->
        outcome = format_outcome(step.expected)
        mark = if step.passed, do: "", else: " ✗"
        "step #{idx} · :#{step.state} #{inspect(step.message, limit: 5)} → #{outcome}#{mark}"
      end)

    header ++ lines
  end

  # -- Failing step diagnostic --

  defp format_failing_step(nil, _compiled, session) do
    Enum.join(session, "\n")
  end

  defp format_failing_step(
         %{actual: {:accord_violation, %Violation{} = v}} = step,
         %{} = compiled,
         session
       ) do
    Violation.Report.format(v, compiled, strict: true, session: session, tracks: step.tracks)
  end

  defp format_failing_step(
         %{actual: {:accord_violation, %Violation{} = v}} = step,
         _compiled,
         session
       ) do
    Violation.Report.format(v, session: session, tracks: step.tracks)
  end

  defp format_failing_step(%{actual: actual, expected: expected}, _compiled, session) do
    Enum.join(session, "\n") <>
      "\nexpected: #{format_outcome(expected)}\n     got: #{inspect(actual, pretty: true, limit: 10)}"
  end

  # -- Property violation formatting --

  defp format_property_violations([], _compiled), do: ""

  defp format_property_violations(violations, %{} = compiled) do
    formatted =
      Enum.map_join(violations, "\n\n", fn v ->
        Violation.Report.format(v, compiled, strict: true)
      end)

    "\n\nProperty violations detected during run:\n" <> formatted
  end

  defp format_property_violations(violations, _compiled) do
    formatted =
      Enum.map_join(violations, "\n\n", fn v ->
        Violation.Report.format(v)
      end)

    "\n\nProperty violations detected during run:\n" <> formatted
  end

  # -- Outcome labels --

  defp format_outcome(:ok), do: "ok"
  defp format_outcome(:session_ended), do: "session_ended"
  defp format_outcome(:skipped), do: "skipped"
  defp format_outcome(:ok_or_violation), do: "ok (or violation)"
  defp format_outcome({:violation, blame, kind}), do: "#{blame}:#{kind}"
  defp format_outcome(other), do: inspect(other)
end
