defmodule Accord.Test.MonotonicId.Protocol do
  @moduledoc """
  An `abstract: :monotonic` showcase: each session claims an id strictly
  greater than the highest issued, like an HTTP/2 stream id or a fence
  token.

  Without the modifier this deadlocks in a small model — one session
  grabs the maximum id and the next starves, an artifact of the tiny
  domain that never happens in a real, effectively-unbounded id space.
  `abstract: :monotonic` extends `last_id`'s type by one and bounds it
  with a state constraint, so exploration stops at the bound rather than
  reporting a spurious deadlock. The `distinct` property is proven with
  deadlock checking on.
  """
  use Accord.Protocol

  initial :idle

  track :last_id, :non_neg_integer, default: 0, shared: true, domain: 0..3, abstract: :monotonic
  track :my_id, :non_neg_integer, default: 0, domain: 0..4

  model do
    sessions 2
    domain :id, 1..4
  end

  state :idle do
    on :claim do
      branch({:issued, id :: pos_integer()},
        goto: :holding,
        where: fn {:issued, id}, tracks -> id > tracks.last_id end
      )

      update fn _msg, {:issued, id}, tracks -> %{tracks | last_id: id, my_id: id} end
    end
  end

  state :holding do
    on :release do
      reply :released
      goto :done
      update fn _msg, _reply, tracks -> %{tracks | my_id: 0} end
    end
  end

  state :done, terminal: true

  property :ids_distinct do
    distinct :my_id, empty: 0
  end
end
