defmodule Accord.TLA.CheckTest do
  use ExUnit.Case, async: true

  import Accord.Test.TLACheck

  @moduletag :tlc
  @moduletag :tmp_dir

  describe "passing protocols" do
    test "counter passes model checking", %{tmp_dir: tmp_dir} do
      assert_passes(Accord.Test.Counter.Protocol, tmp_dir: tmp_dir)
    end

    test "lock passes model checking", %{tmp_dir: tmp_dir} do
      assert_passes(Accord.Test.Lock.Protocol, tmp_dir: tmp_dir)
    end

    test "blackjack passes model checking", %{tmp_dir: tmp_dir} do
      assert_passes(Accord.Test.Blackjack.Protocol,
        tmp_dir: tmp_dir,
        model_config_path: "test/support/protocols/blackjack_model.exs"
      )
    end

    test "an atom-typed track with an enumerated domain checks cleanly (H4)",
         %{tmp_dir: tmp_dir} do
      # Atoms compared and assigned by name render as concrete strings
      # consistently across domain, default, guards, updates, and the
      # invariant — so TLC no longer reports a spurious TypeInvariant
      # violation on this correct protocol.
      assert_passes(Accord.Test.EnumeratedMode.Protocol, tmp_dir: tmp_dir)
    end

    test "an abstract: :monotonic id track does not spuriously deadlock",
         %{tmp_dir: tmp_dir} do
      # Deadlock checking is on. Without abstract: :monotonic a session
      # starves once the tiny id domain is exhausted (a false deadlock);
      # the modifier lets exploration stop at the bound instead, and the
      # distinct property is proven.
      assert_passes(Accord.Test.MonotonicId.Protocol, tmp_dir: tmp_dir)
    end
  end

  describe "invariant violations" do
    test "global invariant detects count exceeding limit", %{tmp_dir: tmp_dir} do
      assert_fails(Accord.Test.InvariantFail.Protocol, :invariant, tmp_dir: tmp_dir)
    end

    test "local invariant detects missing track setup", %{tmp_dir: tmp_dir} do
      assert_fails(Accord.Test.LocalInvariantFail.Protocol, :invariant, tmp_dir: tmp_dir)
    end

    test "bounded check detects count exceeding bound", %{tmp_dir: tmp_dir} do
      assert_fails(Accord.Test.BoundedFail.Protocol, :invariant, tmp_dir: tmp_dir)
    end

    test "forbidden check detects reachable forbidden state", %{tmp_dir: tmp_dir} do
      assert_fails(Accord.Test.ForbiddenFail.Protocol, :invariant, tmp_dir: tmp_dir)
    end

    test "correspondence detects unmatched close", %{tmp_dir: tmp_dir} do
      assert_fails(Accord.Test.CorrespondenceFail.Protocol, :invariant, tmp_dir: tmp_dir)
    end
  end

  describe "temporal violations" do
    test "liveness detects unreachable target state", %{tmp_dir: tmp_dir} do
      assert_fails(Accord.Test.LivenessFail.Protocol, :temporal, tmp_dir: tmp_dir)
    end

    test "liveness with assuming: passes under per-action fairness", %{tmp_dir: tmp_dir} do
      assert_passes(Accord.Test.LivenessFair.Protocol, tmp_dir: tmp_dir)
    end

    test "same protocol without assuming: fails via the retry-loop counterexample",
         %{tmp_dir: tmp_dir} do
      assert_fails(Accord.Test.LivenessUnfair.Protocol, :temporal, tmp_dir: tmp_dir)
    end

    test "a liveness property cannot borrow a sibling's fairness assumption (H3)",
         %{tmp_dir: tmp_dir} do
      # finishes_when_retry_is_fair is unprovable under its own :retry
      # fairness; it only passed when the old shared FairSpec pooled in
      # :finish's fairness. With per-property fairness the protocol fails.
      assert_fails(Accord.Test.FairnessLeak.Protocol, :temporal, tmp_dir: tmp_dir)
    end
  end

  describe "action property violations" do
    test "action property detects non-monotonic track", %{tmp_dir: tmp_dir} do
      assert_fails(Accord.Test.ActionFail.Protocol, :action_property, tmp_dir: tmp_dir)
    end
  end

  describe "multi-session model checking" do
    test "TLC proves mutual exclusion for the guarded distributed lock", %{tmp_dir: tmp_dir} do
      assert_passes(Accord.Test.DistributedLock.Protocol,
        tmp_dir: tmp_dir,
        model_config_path: "test/support/protocols/distributed_lock_model.exs"
      )
    end

    test "dropping the holder guard yields the two-sessions-both-locked counterexample",
         %{tmp_dir: tmp_dir} do
      # Fence tokens stay monotonic in the counterexample — fencing alone
      # is not a lock. This interleaving is unrepresentable at sessions: 1.
      assert_fails(Accord.Test.DistributedLockUnguarded.Protocol, :invariant,
        tmp_dir: tmp_dir,
        model_config_path: "test/support/protocols/distributed_lock_model.exs"
      )
    end
  end

  describe "distinct leases across sessions" do
    test "the fencing constraint makes leases unique — TLC proves distinct",
         %{tmp_dir: tmp_dir} do
      assert_passes(Accord.Test.DistributedQueue.Protocol, tmp_dir: tmp_dir)
    end

    test "without fencing, both workers get token 1", %{tmp_dir: tmp_dir} do
      assert_fails(Accord.Test.DistributedQueueUnguarded.Protocol, :invariant, tmp_dir: tmp_dir)
    end
  end

  describe "server-push events" do
    test "TLC interleaves pushes with calls and proves the demand invariant",
         %{tmp_dir: tmp_dir} do
      assert_passes(Accord.Test.Feed.Protocol, tmp_dir: tmp_dir)
    end

    test "removing the event guard lets TLC find the over-delivery interleaving",
         %{tmp_dir: tmp_dir} do
      assert_fails(Accord.Test.FeedUnguarded.Protocol, :invariant, tmp_dir: tmp_dir)
    end
  end

  describe "deadlock" do
    test "deadlock detects stuck non-terminal state by default", %{tmp_dir: tmp_dir} do
      # No check_deadlock flag needed — deadlock checking is the default.
      assert_fails(Accord.Test.DeadlockFail.Protocol, :deadlock, tmp_dir: tmp_dir)
    end

    test "terminal states are not deadlocks (Terminating self-stutter)", %{tmp_dir: tmp_dir} do
      # Counter runs end in :stopped; with deadlock checking on this
      # passes only because Terminating gives terminals a self-loop.
      assert_passes(Accord.Test.Counter.Protocol, tmp_dir: tmp_dir)
    end

    test "--no-deadlock escape hatch still works", %{tmp_dir: tmp_dir} do
      assert_passes(Accord.Test.DeadlockFail.Protocol,
        tmp_dir: tmp_dir,
        check_deadlock: false
      )
    end
  end
end
