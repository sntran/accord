defmodule Accord.Examples.CircuitBreaker.Protocol do
  @moduledoc """
  A circuit breaker that trips after 3 consecutive failures.

  States: `:closed` passes requests through and counts failures, `:open`
  rejects them, `:half_open` lets a single probe through. The reply
  (`:ok` / `:error` / `:tripped`) tells the monitor which state the
  breaker moved to.

  The `where:` constraints on the failure counter decide which reply is
  valid at each count, and the local invariant restates the threshold
  rule so model checking verifies it over every reachable state.

  Run `mix accord.check Accord.Examples.CircuitBreaker.Protocol` to
  model-check it; `protocol_stuck_counter.ex` is a version with a seeded
  bug that model checking catches.
  """
  use Accord.Protocol

  initial :closed

  # The trip threshold appears in the constraints and the invariant —
  # declared once, substituted everywhere at compile time.
  const :threshold, 3

  track :failures, :non_neg_integer, default: 0, domain: 0..4

  state :closed do
    on :request do
      branch :ok, goto: :closed

      branch(:error,
        goto: :closed,
        where: fn _reply, tracks -> tracks.failures < const(:threshold) - 1 end
      )

      branch(:tripped,
        goto: :open,
        where: fn _reply, tracks -> tracks.failures == const(:threshold) - 1 end
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
    # The cooldown: after 30s in :open the breaker probes on its own —
    # no client poll required. The timeout's automatic weak fairness is
    # what discharges the breaker_recovers liveness property.
    state_timeout 30_000, goto: :half_open

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
    invariant :closed, fn _msg, tracks -> tracks.failures < const(:threshold) end
  end

  property :counter_sane do
    forbidden fn tracks -> tracks.failures > const(:threshold) end
  end

  property :probe_only_after_trip do
    precedence :half_open, :open
  end

  property :breaker_recovers do
    liveness in_state(:open), leads_to: in_state(:half_open)
  end

  property :probe_reachable do
    reachable :half_open
  end
end
