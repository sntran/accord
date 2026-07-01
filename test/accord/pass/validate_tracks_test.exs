defmodule Accord.Pass.ValidateTracksTest do
  use ExUnit.Case, async: true

  alias Accord.IR
  alias Accord.IR.{State, Track}
  alias Accord.Pass.ValidateTracks
  alias Pentiment.Span.Search

  defp base_ir(tracks) do
    %IR{
      name: Test.Protocol,
      initial: :ready,
      tracks: tracks,
      states: %{ready: %State{name: :ready, terminal: true}}
    }
  end

  defp track(name, line) do
    %Track{
      name: name,
      type: :non_neg_integer,
      default: 0,
      span: Search.new(line: line, pattern: "track")
    }
  end

  test "accepts IR with unique track names" do
    ir = base_ir([track(:counter, 5), track(:balance, 6)])

    assert {:ok, ^ir} = ValidateTracks.run(ir)
  end

  test "accepts IR with no tracks" do
    ir = base_ir([])

    assert {:ok, ^ir} = ValidateTracks.run(ir)
  end

  test "rejects IR with two tracks sharing a name" do
    ir = base_ir([track(:counter, 5), track(:counter, 6)])

    assert {:error, [report]} = ValidateTracks.run(ir)
    assert report.code == "E040"
    assert report.message =~ "duplicate track name :counter"
    assert length(report.labels) >= 2

    label_messages = Enum.map(report.labels, & &1.message)
    assert "first defined here" in label_messages
    assert "duplicate declaration" in label_messages
  end

  test "rejects three tracks where two are duplicates with exactly one report" do
    ir = base_ir([track(:counter, 5), track(:fine, 6), track(:counter, 7)])

    assert {:error, [report]} = ValidateTracks.run(ir)
    assert report.code == "E040"
    assert report.message =~ ":counter"
  end

  test "reports each duplicated name separately" do
    ir =
      base_ir([
        track(:counter, 5),
        track(:counter, 6),
        track(:balance, 7),
        track(:balance, 8)
      ])

    assert {:error, reports} = ValidateTracks.run(ir)
    assert length(reports) == 2
    assert Enum.all?(reports, &(&1.code == "E040"))
  end
end
