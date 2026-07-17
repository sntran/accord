defmodule Accord.Examples.Http2.Connection.Protocol do
  @moduledoc """
  HTTP/2 connection GOAWAY gating streams (RFC 9113 §6.8), from the Bandit case
  study — connection/stream composition without a dedicated two-level construct.

  A connection-level state gates per-session streams: once the connection is going
  away, no new stream may open. It is expressed with the three primitives that
  compose into layered state — a `shared:` connection track, a state-changing
  `cast :goaway` that flips it, and an `abstract: :monotonic` id keeping the
  open-guard finite. Each session (a stream) reads the shared `conn_state` in its
  open guard. TLC proves no stream opens once GOAWAY has been sent (`sessions: 2`).
  """
  use Accord.Protocol

  initial :idle

  track :conn_state, :atom, default: :active, shared: true, domain: [:active, :going_away]
  track :last_id, :non_neg_integer, default: 0, shared: true, domain: 0..3, abstract: :monotonic
  track :open_seen_goaway, :boolean, default: false, shared: true
  track :my_id, :non_neg_integer, default: 0, domain: 0..4

  model do
    sessions 2
    domain :id, 1..4
  end

  state :idle do
    on :open do
      # A stream opens only while the connection is active and with a fresh id.
      branch({:opened, id :: pos_integer()},
        goto: :active,
        where: fn {:opened, id}, tracks ->
          id > tracks.last_id and tracks.conn_state == :active
        end
      )

      update fn _msg, {:opened, id}, tracks ->
        %{tracks | last_id: id, my_id: id, open_seen_goaway: tracks.conn_state == :going_away}
      end
    end
  end

  state :active do
    on :close do
      reply :ok
      goto :done
      update fn _msg, _reply, tracks -> %{tracks | my_id: 0} end
    end
  end

  state :done, terminal: true

  anystate do
    # The connection goes away — a one-way client cast flipping shared state.
    cast :goaway do
      update fn _msg, tracks -> %{tracks | conn_state: :going_away} end
    end
  end

  property :no_open_after_goaway do
    forbidden fn tracks -> tracks.open_seen_goaway end
  end
end
