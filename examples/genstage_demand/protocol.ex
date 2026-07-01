defmodule Accord.Examples.Demand.Protocol do
  @moduledoc """
  The GenStage demand contract: never emit more events than demanded.

  The rule every GenStage/Broadway user knows from the documentation —
  and that nothing enforces at runtime — as a contract. The consumer
  asks for demand (a call); the producer pushes `{:events, n}` through
  the monitor (a server event) whose guard IS the documented rule.
  Over-delivery is immediate server blame; TLC interleaves asks and
  pushes and proves demand never goes negative.

  The shortest example with the largest argument: this contract was
  inexpressible before server-push events existed.
  """
  use Accord.Protocol

  initial :subscribed

  track :demand, :non_neg_integer, default: 0, domain: 0..6

  model do
    domain :n, 1..3
  end

  state :subscribed do
    on {:ask, n :: pos_integer()} do
      # max_demand: outstanding demand stays bounded.
      guard fn {:ask, n}, tracks -> tracks.demand + n <= 6 end
      reply :ok
      goto :subscribed
      update fn {:ask, n}, _reply, tracks -> %{tracks | demand: tracks.demand + n} end
    end

    event {:events, n :: pos_integer()} do
      # The documented contract: never emit more than demanded.
      guard fn {:events, n}, tracks -> n <= tracks.demand end
      goto :subscribed
      update fn {:events, n}, tracks -> %{tracks | demand: tracks.demand - n} end
    end

    event :producer_done, goto: :done

    on :cancel, reply: :cancelled, goto: :done
  end

  state :done, terminal: true

  property :demand_never_negative do
    invariant fn tracks -> tracks.demand >= 0 end
  end

  property :demand_bounded do
    bounded :demand, max: 6
  end
end
