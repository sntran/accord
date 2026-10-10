defmodule Accord.ExploreTest do
  use ExUnit.Case, async: true

  alias Accord.Explore
  alias Accord.Explore.Model

  # The expected counts come from TLC runs on the same protocols. The
  # cross-check tests (tag :tlc) compare all of them with TLC again.

  describe "state space" do
    test "job queue: 11 states, depth 4, no violation" do
      result = Explore.run(Accord.Examples.JobQueue.Protocol)

      assert result.distinct == 11
      assert result.depth == 4
      assert result.violations == %{}
      assert result.complete
      assert {"AcksOrdered", "ordered is runtime-only"} in result.skipped
      assert "TypeInvariant" in result.checked
      assert "Deadlock" in result.checked
    end

    test "two sessions: the full model and the symmetry-reduced model" do
      assert %{distinct: 58, depth: 5, violations: %{}} =
               Explore.run(Accord.Test.DistributedLock.Protocol)

      assert %{distinct: 36, depth: 5} =
               Explore.run(Accord.Test.DistributedLock.Protocol, symmetry: true)
    end

    test "collect_states gives each distinct state one time" do
      result = Explore.run(Accord.Test.Counter.Protocol, collect_states: true)

      assert length(result.states) == result.distinct
      assert length(Enum.uniq(result.states)) == result.distinct
    end

    test "a model larger than max_states is not complete" do
      result = Explore.run(Accord.Examples.Demand.ProtocolUnbounded, max_states: 500)

      refute result.complete
      refute Explore.Result.ok?(result)
    end
  end

  describe "violations" do
    test "the leaky lease: the shortest counterexample has three states" do
      result = Explore.run(Accord.Examples.JobQueue.ProtocolLeakyLease)

      assert %{kind: :invariant, trace: [init, checkout, expiry]} =
               result.violations["LeaseIffWorkingIdle"]

      assert init.label == nil
      assert %{kind: :call, message: :checkout, reply: {:job, 1}, to: :working} = checkout.label
      assert %{kind: :event, message: {:lease_expired, 1}, to: :idle} = expiry.label
      assert {{{:idle, %{fence: 1, holding: 1}, %{}}}, %{}} = expiry.state
    end

    test "two sessions both hold the unguarded lock" do
      result = Explore.run(Accord.Test.DistributedLockUnguarded.Protocol)

      assert %{trace: [_init, first, second]} = result.violations["MutualExclusionExclusive"]
      assert first.label.session == 1
      assert second.label.session == 2
    end

    test "an action property is checked on each step that changes a track" do
      result = Explore.run(Accord.Test.ActionFail.Protocol)

      assert %{kind: :action, trace: trace} = result.violations["MonotonicLevel"]
      assert length(trace) == 3
    end

    test "deadlock: a state with no successor" do
      result = Explore.run(Accord.Test.DeadlockFail.Protocol)

      assert %{kind: :deadlock, trace: trace} = result.violations["Deadlock"]
      assert length(trace) == 4
      assert {{{:counting, %{fuel: 0}, %{}}}, %{}} = List.last(trace).state
    end

    test "deadlock: false turns off the deadlock check" do
      result = Explore.run(Accord.Test.DeadlockFail.Protocol, deadlock: false)

      assert result.violations == %{}
      refute "Deadlock" in result.checked
    end

    test "a violation outside an infinite model is still found" do
      result = Explore.run(Accord.Examples.Demand.ProtocolUnbounded, max_states: 500)

      assert %{trace: [_, _]} = result.violations["DemandNeverNegative"]
    end

    test "stop: :first stops at the first violation" do
      result = Explore.run(Accord.Test.FeedUnguarded.Protocol, stop: :first)
      assert map_size(result.violations) == 1
    end
  end

  describe "evaluation errors" do
    defmodule Raising do
      use Accord.Protocol, tla: :off

      initial :ready

      track :x, :integer, default: 1, domain: 0..1

      state :ready do
        on {:set, n :: non_neg_integer()} do
          guard fn {:set, n}, tracks -> div(10, tracks.x) > n end
          reply :ok
          goto :ready
          update fn {:set, n}, _reply, tracks -> %{tracks | x: n} end
        end
      end
    end

    test "a function that raises stops the search with an error" do
      result = Explore.run(Raising)

      assert %{kind: :error, message: message, trace: trace} = result.violations["Error"]
      assert message =~ "bad argument in arithmetic expression"
      assert %{message: {:set, _}} = List.last(trace).label
    end
  end

  describe "model" do
    test "a call reply goes to the first branch that accepts it" do
      model = Model.build(Accord.Test.Probe.OverlapBranches.Protocol)
      [init] = Model.init_states(model)

      targets =
        model
        |> Model.successors(init)
        |> Enum.map(fn {label, _} -> {label.reply, label.to} end)
        |> Enum.sort()

      assert targets == [{{:ok, 1}, :low}, {{:ok, 2}, :high}, {{:ok, 3}, :high}]
    end

    test "model values are atoms with the TLC name" do
      assert Model.domain_values({:model_values, 2}) == [:mv1, :mv2]
      assert Model.domain_values({:model_values, [:c1, :c2]}) == [:c1, :c2]
      assert Model.domain_values(0..2) == [0, 1, 2]
    end

    test "a state constraint must be a conjunction of track comparisons" do
      ir = Accord.Test.BoundedFail.Protocol.__ir__()
      config = Model.model_config(Accord.Test.BoundedFail.Protocol)
      [track | _] = ir.tracks

      ok = %{config | state_constraint: "#{track.name} =< 2 /\\ #{track.name} >= 0"}
      assert %Model{constraint: [_, _]} = Model.build(ir, ok)

      bad = %{config | state_constraint: "Len(#{track.name}) < 2"}
      assert_raise Model.UnsupportedFailure, fn -> Model.build(ir, bad) end
    end
  end
end
