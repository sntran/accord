defmodule Accord.Examples.Payment.ProtocolPercallGuard do
  @moduledoc """
  Seeded design bug: the capture guard checks per call, not cumulatively.

  `amount <= tracks.authorized` allows each individual capture to fit
  the authorization while their sum exceeds it. TLC's counterexample is
  the classic partial-capture double-spend: authorize(4), capture(3),
  capture(3) — captured = 6 > authorized = 4, `never_overcapture`
  violated. The guard IS the model; a wrong guard is a wrong state
  space, which is exactly what model checking is for.

  Verified by `test/examples/payment_test.exs` against real TLC.
  """
  # tla: :off — deliberately broken; not part of the project's verified
  # surface. The TLC test compiles the spec from the IR directly and
  # asserts the counterexample, so `mix accord.check` skips it instead
  # of failing on a demo.
  use Accord.Protocol, tla: :off

  initial :created

  track :authorized, :non_neg_integer, default: 0, domain: 0..4
  track :captured, :non_neg_integer, default: 0, domain: 0..8
  track :refunded, :non_neg_integer, default: 0, domain: 0..8

  model do
    domain :amount, 1..4
  end

  state :created do
    on {:authorize, amount :: pos_integer()} do
      branch :approved, goto: :authorized
      branch :declined, goto: :declined

      update fn {:authorize, amount}, reply, tracks ->
        case reply do
          :approved -> %{tracks | authorized: amount}
          :declined -> tracks
        end
      end
    end
  end

  state :authorized do
    on {:capture, amount :: pos_integer()} do
      # BUG: per-call check — partial captures can sum past the
      # authorization.
      guard fn {:capture, amount}, tracks -> amount <= tracks.authorized end

      reply :ok
      goto :authorized

      update fn {:capture, amount}, _reply, tracks ->
        %{tracks | captured: tracks.captured + amount}
      end
    end

    on :finalize do
      guard fn :finalize, tracks -> tracks.captured > 0 end
      reply :finalized
      goto :captured
    end
  end

  state :captured do
    on :close, reply: :closed, goto: :closed
  end

  state :declined, terminal: true
  state :closed, terminal: true

  property :never_overcapture do
    invariant fn tracks -> tracks.captured <= tracks.authorized end
  end
end
