defmodule Accord.Test.Feed.Protocol do
  @moduledoc """
  Demand-driven feed protocol exercising server-push events.

  The consumer asks for demand (call); the producer pushes `{:data, _}`
  events through the monitor, each consuming one unit of demand. The
  event guard enforces the documented contract: never push more events
  than were demanded. TLC interleaves asks and pushes and proves demand
  never goes negative.
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
      guard fn {:data, _item}, tracks -> tracks.demand > 0 end
      goto :subscribed
      update fn {:data, _item}, tracks -> %{tracks | demand: tracks.demand - 1} end
    end

    event :halted, goto: :done

    on :cancel, reply: :cancelled, goto: :done
  end

  state :done, terminal: true

  anystate do
    event :server_notice
  end

  property :demand_never_negative do
    invariant fn tracks -> tracks.demand >= 0 end
  end
end
