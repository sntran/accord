defmodule Accord.Examples.Http2.StreamId.Protocol do
  @moduledoc """
  HTTP/2 stream-identifier monotonicity (RFC 9113 §5.1.1), from the Bandit case
  study. A newly opened stream's ID MUST be numerically greater than every stream
  the peer has already opened — a fence over the shared connection.

  Two concurrent streams are modeled as `sessions: 2` sharing the connection's
  `last_id`. Each session claims an ID strictly greater than `last_id` (the guard)
  and records its own `my_id`; `distinct :my_id` asserts no two streams share an
  ID. `last_id` is `abstract: :monotonic` so the tiny model domain does not
  produce a spurious deadlock once the id space is "exhausted" — exploration stops
  at the bound instead (the real id space is effectively unbounded).

  This is the conformant spec; TLC proves the fence holds. Bandit enforces the
  greater-than rule for new IDs (`StreamCollection.get_pid` classifies
  `id > last_id` as `:new`), but silently drops a HEADERS on a *lower* id where
  §5.1.1 requires a PROTOCOL_ERROR — case study round 1.
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
    on :open_stream do
      branch({:opened, id :: pos_integer()},
        goto: :active,
        where: fn {:opened, id}, tracks -> id > tracks.last_id end
      )

      update fn _msg, {:opened, id}, tracks -> %{tracks | last_id: id, my_id: id} end
    end
  end

  state :active do
    on :close do
      reply :ok
      goto :closed
      update fn _msg, _reply, tracks -> %{tracks | my_id: 0} end
    end
  end

  state :closed, terminal: true

  property :ids_distinct do
    distinct :my_id, empty: 0
  end
end
