defmodule Accord.Test.FeedUnguarded.Protocol do
  @moduledoc """
  Failure fixture: the Feed protocol without the demand guard on the
  data event.

  A producer may now push events with zero outstanding demand — TLC
  finds the interleaving where `demand` goes negative, violating the
  invariant. This is the documented GenStage contract rule ("never emit
  more events than demanded") mechanically derived.
  """
  use Accord.Protocol

  initial :subscribed

  track :demand, :non_neg_integer, default: 0

  state :subscribed do
    on {:ask, n :: pos_integer()} do
      guard fn {:ask, n}, tracks -> tracks.demand + n <= 3 end
      reply :ok
      goto :subscribed
      update fn {:ask, n}, _reply, tracks -> %{tracks | demand: tracks.demand + n} end
    end

    event {:data, item :: term()} do
      goto :subscribed
      update fn {:data, _item}, tracks -> %{tracks | demand: tracks.demand - 1} end
    end

    on :cancel, reply: :cancelled, goto: :done
  end

  state :done, terminal: true

  property :demand_never_negative do
    invariant fn tracks -> tracks.demand >= 0 end
  end
end
