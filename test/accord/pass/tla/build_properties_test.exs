defmodule Accord.Pass.TLA.BuildPropertiesTest do
  use ExUnit.Case, async: true

  alias Accord.IR
  alias Accord.IR.{Check, Property, State, Track}
  alias Accord.Pass.TLA.BuildProperties

  defp base_ir(properties) do
    %IR{
      name: Test.Protocol,
      initial: :ready,
      states: %{ready: %State{name: :ready}},
      tracks: [%Track{name: :counter, type: :integer, default: 0}],
      properties: properties
    }
  end

  describe "invariant" do
    test "global invariant becomes TLA+ invariant" do
      ir =
        base_ir([
          %Property{
            name: :counter_positive,
            checks: [
              %Check{
                kind: :invariant,
                spec: %{
                  fun: fn tracks -> tracks.counter >= 0 end,
                  ast: quote(do: fn tracks -> tracks.counter >= 0 end)
                }
              }
            ]
          }
        ])

      {:ok, props} = BuildProperties.run(ir)
      [prop] = props

      assert prop.name == "CounterPositive"
      assert prop.kind == :invariant
      assert prop.formula =~ "counter >= 0"
    end

    test "invariant without AST produces TRUE" do
      ir =
        base_ir([
          %Property{
            name: :always_true,
            checks: [
              %Check{kind: :invariant, spec: %{fun: fn _ -> true end, ast: nil}}
            ]
          }
        ])

      {:ok, props} = BuildProperties.run(ir)
      [prop] = props

      assert prop.formula =~ "TRUE"
    end
  end

  describe "local_invariant" do
    test "produces state-conditioned invariant" do
      ir =
        base_ir([
          %Property{
            name: :ready_check,
            checks: [
              %Check{
                kind: :local_invariant,
                spec: %{
                  state: :ready,
                  fun: fn _, tracks -> tracks.counter >= 0 end,
                  ast: quote(do: fn _msg, tracks -> tracks.counter >= 0 end)
                }
              }
            ]
          }
        ])

      {:ok, props} = BuildProperties.run(ir)
      [prop] = props

      assert prop.name == "ReadyCheckReady"
      assert prop.kind == :invariant
      assert prop.formula =~ ~s(state = "ready")
      assert prop.formula =~ "=>"
    end
  end

  describe "action_property" do
    test "produces temporal action property" do
      ir =
        base_ir([
          %Property{
            name: :monotonic,
            checks: [
              %Check{
                kind: :action,
                spec: %{
                  fun: fn old, new -> new.counter >= old.counter end,
                  ast: quote(do: fn old, new -> new.counter >= old.counter end)
                }
              }
            ]
          }
        ])

      {:ok, props} = BuildProperties.run(ir)
      [prop] = props

      assert prop.name == "Monotonic"
      assert prop.kind == :temporal
      assert prop.formula =~ "counter' >= counter"
      assert prop.formula =~ "[]"
    end
  end

  describe "liveness" do
    test "produces leads-to formula" do
      ir =
        base_ir([
          %Property{
            name: :progress,
            checks: [
              %Check{
                kind: :liveness,
                spec: %{
                  trigger: {:in_state, :waiting},
                  target: {:in_state, :done},
                  fairness: :weak
                }
              }
            ]
          }
        ])

      {:ok, props} = BuildProperties.run(ir)
      [prop] = props

      assert prop.name == "Progress"
      assert prop.kind == :temporal
      assert prop.formula =~ "~>"
      assert prop.formula =~ ~s(state = "waiting")
      assert prop.formula =~ ~s(state = "done")
    end
  end

  describe "bounded" do
    test "produces bounded invariant" do
      ir =
        base_ir([
          %Property{
            name: :counter_bounded,
            checks: [%Check{kind: :bounded, spec: %{track: :counter, max: 50}}]
          }
        ])

      {:ok, props} = BuildProperties.run(ir)
      [prop] = props

      assert prop.name == "CounterBounded"
      assert prop.kind == :invariant
      assert prop.formula =~ "counter =< 50"
    end
  end

  describe "correspondence" do
    test "produces counter invariant" do
      ir =
        base_ir([
          %Property{
            name: :open_close,
            checks: [
              %Check{kind: :correspondence, spec: %{open: :open, close: [:close]}}
            ]
          }
        ])

      {:ok, props} = BuildProperties.run(ir)
      [prop] = props

      assert prop.name == "OpenClose"
      assert prop.kind == :invariant
      assert prop.formula =~ "open_pending >= 0"
    end
  end

  describe "forbidden" do
    test "produces negated invariant" do
      ir =
        base_ir([
          %Property{
            name: :no_negative,
            checks: [
              %Check{
                kind: :forbidden,
                spec: %{
                  fun: fn tracks -> tracks.counter < 0 end,
                  ast: quote(do: fn tracks -> tracks.counter < 0 end)
                }
              }
            ]
          }
        ])

      {:ok, props} = BuildProperties.run(ir)
      [prop] = props

      assert prop.name == "NoNegative"
      assert prop.kind == :invariant
      assert prop.formula =~ "~("
    end
  end

  describe "reachable" do
    test "produces auxiliary property" do
      ir =
        base_ir([
          %Property{
            name: :target_reachable,
            checks: [%Check{kind: :reachable, spec: %{target: :done}}]
          }
        ])

      {:ok, props} = BuildProperties.run(ir)
      [prop] = props

      assert prop.name == "TargetReachable"
      assert prop.kind == :auxiliary
      assert prop.formula =~ "reachable"
    end
  end

  describe "multiple checks in one property" do
    test "each check produces a separate TLA+ property" do
      ir =
        base_ir([
          %Property{
            name: :multi,
            checks: [
              %Check{kind: :bounded, spec: %{track: :counter, max: 100}},
              %Check{
                kind: :invariant,
                spec: %{
                  fun: fn tracks -> tracks.counter >= 0 end,
                  ast: quote(do: fn tracks -> tracks.counter >= 0 end)
                }
              }
            ]
          }
        ])

      {:ok, props} = BuildProperties.run(ir)

      assert length(props) == 2
      kinds = Enum.map(props, & &1.kind)
      assert :invariant in kinds
    end
  end

  describe "runtime-only checks" do
    test "ordered produces a runtime_only property, never a silent drop" do
      ir =
        base_ir([
          %Property{
            name: :acks_ordered,
            checks: [%Check{kind: :ordered, spec: %{event: :ack, by: :token}}]
          }
        ])

      {:ok, [prop]} = BuildProperties.run(ir)

      assert prop.kind == :runtime_only
      assert prop.formula =~ "runtime-only"
      assert prop.formula =~ "ordered"
      assert prop.formula =~ "token"
    end

    test "precedence produces a runtime_only property" do
      ir =
        base_ir([
          %Property{
            name: :must_authorize,
            checks: [%Check{kind: :precedence, spec: %{target: :captured, required: :authorized}}]
          }
        ])

      {:ok, [prop]} = BuildProperties.run(ir)

      assert prop.kind == :runtime_only
      assert prop.formula =~ "precedence"
    end

    test "keyed correspondence produces a runtime_only property" do
      ir =
        base_ir([
          %Property{
            name: :per_job,
            checks: [
              %Check{kind: :correspondence, spec: %{open: :checkout, close: [:ack], by: :job_id}}
            ]
          }
        ])

      {:ok, [prop]} = BuildProperties.run(ir)

      assert prop.kind == :runtime_only
      assert prop.formula =~ "by :job_id"
    end

    test "unkeyed correspondence still produces a counter invariant" do
      ir =
        base_ir([
          %Property{
            name: :open_close,
            checks: [
              %Check{kind: :correspondence, spec: %{open: :open, close: [:close], by: nil}}
            ]
          }
        ])

      {:ok, [prop]} = BuildProperties.run(ir)

      assert prop.kind == :invariant
      assert prop.formula =~ "open_pending >= 0"
    end

    test "reachable does not claim TLC verification" do
      ir =
        base_ir([
          %Property{
            name: :target_reachable,
            checks: [%Check{kind: :reachable, spec: %{target: :done}}]
          }
        ])

      {:ok, [prop]} = BuildProperties.run(ir)

      assert prop.formula =~ "not asserted by TLC"
      refute prop.formula =~ "verified by TLC"
    end
  end

  describe "fidelity errors" do
    test "untranslatable invariant expression reports E041" do
      ir =
        base_ir([
          %Property{
            name: :counter_valid,
            checks: [
              %Check{
                kind: :invariant,
                spec: %{
                  fun: fn tracks -> rem(tracks.counter, 2) == 0 end,
                  ast: quote(do: fn tracks -> Integer.mod(tracks.counter, 2) == 0 end)
                }
              }
            ]
          }
        ])

      assert {:error, [report]} = BuildProperties.run(ir)
      assert report.code == "E041"
      assert report.message =~ "cannot compile invariant to TLA+"
    end

    test "invariant referencing an unknown track reports E043" do
      ir =
        base_ir([
          %Property{
            name: :counter_valid,
            checks: [
              %Check{
                kind: :invariant,
                spec: %{
                  fun: fn tracks -> tracks.counter >= 0 end,
                  ast: quote(do: fn tracks -> tracks.countr >= 0 end)
                }
              }
            ]
          }
        ])

      assert {:error, [report]} = BuildProperties.run(ir)
      assert report.code == "E043"
      assert report.message =~ "unknown track `countr`"
    end

    test "local invariant conditioning on the message reports E043" do
      # The msg param cannot be modeled: the spec has no per-state message
      # variable, so conditioning on it would silently check something else.
      ir =
        base_ir([
          %Property{
            name: :msg_conditioned,
            checks: [
              %Check{
                kind: :local_invariant,
                spec: %{
                  state: :ready,
                  fun: fn msg, tracks -> msg != nil and tracks.counter >= 0 end,
                  ast: quote(do: fn msg, tracks -> msg != nil and tracks.counter >= 0 end)
                }
              }
            ]
          }
        ])

      assert {:error, [report]} = BuildProperties.run(ir)
      assert report.code == "E043"
      assert report.message =~ "`msg`"
    end

    test "whole-tracks comparison in action property reports E041" do
      ir =
        base_ir([
          %Property{
            name: :anything_changed,
            checks: [
              %Check{
                kind: :action,
                spec: %{
                  fun: fn old, new -> old != new end,
                  ast: quote(do: fn old, new -> old != new end)
                }
              }
            ]
          }
        ])

      assert {:error, [report]} = BuildProperties.run(ir)
      assert report.code == "E041"
    end
  end
end
