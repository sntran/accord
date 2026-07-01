defmodule Accord.Examples.JobQueue.Protocol do
  @moduledoc """
  Worker ↔ queue lease protocol with fencing tokens.

  The queue issues a strictly increasing fence token with every lease
  (Kleppmann's fencing-token critique of distributed locks, made
  executable). The worker presents its token on heartbeat/ack/nack, and
  the queue pushes `{:lease_expired, token}` through the monitor when a
  visibility timeout fires — a server event, validated and forwarded
  like any other message.

  The single-session contract here answers "is THIS worker's session
  legal"; the cross-worker mutual-exclusion story is the
  `Accord.Test.DistributedLock` fixture (`sessions: 2`, shared tracks,
  `exclusive`).

  See `protocol_leaky_lease.ex` for the double-processing bug TLC finds
  in three actions.
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

  property :worker_finishes do
    liveness in_state(:working), leads_to: in_state(:idle), assuming: [:ack]
  end
end
