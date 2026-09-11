defmodule Accord.Violation.ReportSessionTest do
  use ExUnit.Case, async: true

  alias Accord.Violation
  alias Accord.Violation.Report

  describe "format/2 with a session" do
    setup do
      violation = %Violation{
        blame: :client,
        kind: :guard_failed,
        state: :authorized,
        message: {:capture, 3},
        context: %{tracks: %{authorized: 4, captured: 3}}
      }

      %{violation: violation}
    end

    test "renders the session as notes ahead of the violation's own notes", %{violation: v} do
      out =
        Report.format(v,
          session: [
            "step 1 · :created {:authorize, 4} → :approved",
            "step 2 · :authorized {:capture, 3} → rejected"
          ]
        )

      notes = out |> String.split("\n") |> Enum.filter(&String.contains?(&1, "note:"))

      assert Enum.at(notes, 0) =~ "step 1 · :created"
      assert Enum.at(notes, 1) =~ "step 2 · :authorized"
      assert Enum.at(notes, 2) =~ "guard rejected {:capture, 3}"
      assert Enum.at(notes, 3) =~ "tracks when the message arrived: authorized = 4, captured = 3"
    end

    test "does not add a second tracks note when the violation already carries one", %{
      violation: v
    } do
      out = Report.format(v, tracks: %{authorized: 9})
      assert length(String.split(out, "tracks when the message arrived")) == 2
      refute out =~ "authorized = 9"
    end

    test "adds the tracks note for violations that do not record tracks themselves" do
      v = %Violation{
        blame: :server,
        kind: :invalid_reply,
        state: :authorized,
        message: {:capture, 1},
        reply: {:ok, 1}
      }

      out = Report.format(v, tracks: %{authorized: 1, captured: 0})
      assert out =~ "tracks when the message arrived: authorized = 1, captured = 0"
    end

    test "format/1 and format/2 with an empty option list agree", %{violation: v} do
      assert Report.format(v) == Report.format(v, [])
    end
  end
end
