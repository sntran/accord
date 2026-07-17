defmodule Accord.Examples.JobQueue.Protocol do
  @moduledoc """
  Worker/queue lease protocol with fence tokens.

  The queue issues a strictly increasing fence token with every lease, so
  a worker holding an expired lease can be told apart from the one holding
  the current lease. The worker presents its token on heartbeat/ack/nack,
  and the queue pushes `{:lease_expired, token}` through the monitor when
  a lease times out — a server event, validated and forwarded like any
  other message.

  This is a single-worker contract. The cross-worker rule — no two workers
  hold the same lease — is checked separately in the
  `Accord.Test.DistributedQueue` fixture with `sessions: 2`.

  See `protocol_leaky_lease.ex` for a version with a seeded
  double-processing bug that model checking catches in three steps.
  """
  use Accord.Protocol

  initial :idle

  # Highest token ever observed, and the token currently held (0 = none).
  track :fence, :non_neg_integer, default: 0, domain: 0..3
  track :holding, :non_neg_integer, default: 0, domain: 0..3

  state :idle do
    on :checkout do
      branch({:job, token :: pos_integer()},
        goto: :working,
        where: fn {:job, token}, tracks -> token > tracks.fence end
      )

      branch :empty, goto: :idle

      update fn _msg, reply, tracks ->
        case reply do
          {:job, token} -> %{tracks | fence: token, holding: token}
          :empty -> tracks
        end
      end
    end

    on :stop, reply: :stopped, goto: :stopped
  end

  state :working do
    on {:heartbeat, token :: pos_integer()} do
      guard fn {:heartbeat, token}, tracks -> token == tracks.holding end
      reply :extended
      goto :working
    end

    on {:ack, token :: pos_integer()} do
      guard fn {:ack, token}, tracks -> token == tracks.holding end

      branch :done, goto: :idle
      # The queue may have fenced this worker off (lease lost without an
      # expiry push, e.g. a partition); the ack is answered but stale.
      branch {:stale, pos_integer()}, goto: :idle

      update fn _msg, _reply, tracks -> %{tracks | holding: 0} end
    end

    on {:nack, token :: pos_integer()} do
      guard fn {:nack, token}, tracks -> token == tracks.holding end
      reply :requeued
      goto :idle
      update fn _msg, _reply, tracks -> %{tracks | holding: 0} end
    end

    # The visibility timeout arrives — it is not fetched. The guard makes
    # a mismatched expiry (for a token this worker no longer holds) a
    # server violation.
    event {:lease_expired, token :: pos_integer()} do
      guard fn {:lease_expired, token}, tracks -> token == tracks.holding end
      goto :idle
      update fn {:lease_expired, _token}, tracks -> %{tracks | holding: 0} end
    end
  end

  state :stopped, terminal: true

  property :fence_monotonic do
    action fn old, new -> new.fence >= old.fence end
  end

  property :lease_iff_working do
    invariant :working, fn _msg, tracks -> tracks.holding > 0 end
    invariant :idle, fn _msg, tracks -> tracks.holding == 0 end
  end

  property :hold_within_fence do
    forbidden fn tracks -> tracks.holding > tracks.fence end
  end

  property :acks_ordered do
    ordered :ack, by: :token
  end

  property :every_checkout_settles do
    correspondence :checkout, [:ack, :nack, :lease_expired]
  end

  # A liveness property (working ~> idle, assuming: [:ack]) would be true
  # here, but correspondence emits its counter bound as a TLA+ CONSTRAINT,
  # and TLC checks liveness only over states satisfying active constraints
  # (its §14.3.5 caveat) — so the verdict would be *bounded* and
  # mix accord.check would flag it with ⚠. Liveness is shown where it is
  # cleanly discharged instead: the circuit_breaker example, whose
  # state_timeout gives the recovery action weak fairness with no
  # constraint in play.
end
