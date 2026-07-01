defmodule Accord.Examples.Demand.ProtocolUnbounded do
  @moduledoc """
  Seeded design bug: the events push has no demand guard.

  TLC's counterexample is three actions: ask(1), push events(2) — or
  push with zero demand at all — and `demand` goes negative. That trace
  is the GenStage documentation rule ("never emit more events than
  demanded"), mechanically derived from its absence.
  """
  use Accord.Protocol

  initial :subscribed

  track :demand, :non_neg_integer, default: 0, domain: -3..6

  model do
    domain :n, 1..3
  end

  state :subscribed do
    on {:ask, n :: pos_integer()} do
      guard fn {:ask, n}, tracks -> tracks.demand + n <= 6 end
      reply :ok
      goto :subscribed
      update fn {:ask, n}, _reply, tracks -> %{tracks | demand: tracks.demand + n} end
    end

    # BUG: no guard — the producer may push regardless of demand.
    event {:events, n :: pos_integer()} do
      goto :subscribed
      update fn {:events, n}, tracks -> %{tracks | demand: tracks.demand - n} end
    end

    on :cancel, reply: :cancelled, goto: :done
  end

  state :done, terminal: true

  property :demand_never_negative do
    invariant fn tracks -> tracks.demand >= 0 end
  end
end
