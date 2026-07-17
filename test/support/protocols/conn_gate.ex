defmodule Accord.Test.ConnGate.Protocol do
  @moduledoc """
  Connection/stream composition: a connection-level state (`conn_state`)
  gates per-session streams — modeled with `sessions`, `shared:` tracks,
  a state-changing `cast`, and an `abstract: :monotonic` id, no dedicated
  two-level construct.

  This is the shape of an HTTP/2 connection that goes away: once
  `conn_state` is `:going_away`, no new stream may open. The guard on the
  open branch enforces it; `ConnGateUnguarded` drops the guard and TLC
  finds a stream opening after the connection went away.
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
    cast :goaway do
      update fn _msg, tracks -> %{tracks | conn_state: :going_away} end
    end
  end

  property :no_open_after_goaway do
    forbidden fn tracks -> tracks.open_seen_goaway end
  end
end

defmodule Accord.Test.ConnGateUnguarded.Protocol do
  @moduledoc """
  Failure fixture: the connection gate without the `conn_state == :active`
  check on the open branch. TLC finds a stream opening after GOAWAY.
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
      branch({:opened, id :: pos_integer()},
        goto: :active,
        where: fn {:opened, id}, tracks -> id > tracks.last_id end
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
    cast :goaway do
      update fn _msg, tracks -> %{tracks | conn_state: :going_away} end
    end
  end

  property :no_open_after_goaway do
    forbidden fn tracks -> tracks.open_seen_goaway end
  end
end
