defmodule Accord.Examples.Payment.Protocol do
  @moduledoc """
  Card payment lifecycle: authorize, partial captures, void, refunds.

  Recognizable to anyone who has integrated a payment service provider.
  The guards carry the money rules — cumulative captures never exceed
  the authorization, refunds never exceed captures — and the global
  invariants restate them so TLC checks every reachable interleaving of
  partial captures and refunds.

  This example needs no extensions: it is the property-algebra showcase
  that works end to end today. See `protocol_percall_guard.ex` for the
  classic double-capture bug TLC catches.
  """
  use Accord.Protocol

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
      # Cumulative, not per-call: the sum of partial captures stays
      # within the authorization.
      guard fn {:capture, amount}, tracks ->
        tracks.captured + amount <= tracks.authorized
      end

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

    on :void do
      guard fn :void, tracks -> tracks.captured == 0 end
      reply :voided
      goto :voided
    end
  end

  state :captured do
    on {:refund, amount :: pos_integer()} do
      guard fn {:refund, amount}, tracks ->
        tracks.refunded + amount <= tracks.captured
      end

      reply :ok
      goto :captured

      update fn {:refund, amount}, _reply, tracks ->
        %{tracks | refunded: tracks.refunded + amount}
      end
    end

    on :close, reply: :closed, goto: :closed
  end

  state :declined, terminal: true
  state :voided, terminal: true
  state :closed, terminal: true

  property :never_overcapture do
    invariant fn tracks -> tracks.captured <= tracks.authorized end
  end

  property :never_overrefund do
    invariant fn tracks -> tracks.refunded <= tracks.captured end
  end

  property :money_flows_forward do
    action fn old, new ->
      new.captured >= old.captured and new.refunded >= old.refunded
    end
  end

  property :authorize_before_capture do
    precedence :captured, :authorized
  end

  property :void_means_no_money_moved do
    invariant :voided, fn _msg, tracks -> tracks.captured == 0 end
  end

  property :all_outcomes_reachable do
    reachable :captured
    reachable :voided
    reachable :declined
  end
end
