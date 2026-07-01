defmodule Accord.Examples.CircuitBreaker.Protocol do
  @moduledoc """
  A circuit breaker with a trip threshold of 3 consecutive failures.

  The protocol governs the breaker itself: `:closed` passes requests
  through and counts failures, `:open` rejects them, `:half_open` probes
  with a single request. The reply shape discloses which side of the
  threshold the breaker is on — an honest contract obligation, and what
  lets the monitor pick the right branch at runtime.

  The `where:` constraints and the local invariant state the same
  threshold rule twice on purpose: the constraints are enforced per
  reply (server blame when the breaker mislabels a failure), and the
  invariant is the safety net TLC checks over every reachable state.

  Run `mix accord.check Accord.Examples.CircuitBreaker.Protocol` to
  model-check it, and see `protocol_stuck_counter.ex` for the seeded
  design bug TLC catches.
  """
  use Accord.Protocol

  initial :closed

  # The trip threshold (3) appears in the constraints, the updates, and
  # the invariant below — protocol constants are future work.
  track :failures, :non_neg_integer, default: 0, domain: 0..4

  state :closed do
    on :request do
      branch :ok, goto: :closed

      branch(:error,
        goto: :closed,
        where: fn _reply, tracks -> tracks.failures < 2 end
      )

      branch(:tripped,
        goto: :open,
        where: fn _reply, tracks -> tracks.failures == 2 end
      )

      update fn _msg, reply, tracks ->
        case reply do
          :ok -> %{tracks | failures: 0}
          :error -> %{tracks | failures: tracks.failures + 1}
          :tripped -> %{tracks | failures: tracks.failures + 1}
        end
      end
    end

    on :shutdown, reply: :down, goto: :down
  end

  state :open do
    # A cooldown timer in a real breaker; a client poll until accord has
    # state timeouts. The liveness property's assuming: encodes exactly
    # this "someone keeps polling" obligation.
    on :attempt_reset, reply: :probing, goto: :half_open

    on :request, reply: {:rejected, :circuit_open}, goto: :open
  end

  state :half_open do
    on :request do
      branch :ok, goto: :closed
      branch :error, goto: :open

      update fn _msg, reply, tracks ->
        case reply do
          :ok -> %{tracks | failures: 0}
          :error -> tracks
        end
      end
    end
  end

  state :down, terminal: true

  property :threshold_respected do
    invariant :closed, fn _msg, tracks -> tracks.failures < 3 end
  end

  property :counter_sane do
    forbidden fn tracks -> tracks.failures > 3 end
  end

  property :probe_only_after_trip do
    precedence :half_open, :open
  end

  property :breaker_recovers do
    liveness in_state(:open), leads_to: in_state(:half_open), assuming: [:attempt_reset]
  end

  property :probe_reachable do
    reachable :half_open
  end
end
