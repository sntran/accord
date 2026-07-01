defmodule Accord.Examples.CircuitBreaker.ProtocolStuckCounter do
  @moduledoc """
  Seeded design bug: recovery forgets to reset the failure counter.

  The `:half_open` success branch returns `tracks` unchanged instead of
  `%{tracks | failures: 0}`. TLC finds the "flapping breaker" in a few
  states: trip (failures 0 → 3), probe, recover — and the breaker is
  `:closed` with `failures = 3`, violating `threshold_respected`. In
  production this is the breaker that instantly re-trips on the first
  post-recovery error.

  Verified by `test/examples/circuit_breaker_test.exs` against real TLC.
  """
  # tla: :off — deliberately broken; not part of the project's verified
  # surface. The TLC test compiles the spec from the IR directly and
  # asserts the counterexample, so `mix accord.check` skips it instead
  # of failing on a demo.
  use Accord.Protocol, tla: :off

  initial :closed

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
    on :attempt_reset, reply: :probing, goto: :half_open
    on :request, reply: {:rejected, :circuit_open}, goto: :open
  end

  state :half_open do
    on :request do
      branch :ok, goto: :closed
      branch :error, goto: :open

      # BUG: the success arm forgets `failures: 0`.
      update fn _msg, reply, tracks ->
        case reply do
          :ok -> tracks
          :error -> tracks
        end
      end
    end
  end

  state :down, terminal: true

  property :threshold_respected do
    invariant :closed, fn _msg, tracks -> tracks.failures < 3 end
  end
end
