defmodule Accord.Examples.Http2.StreamIdMonitor.Protocol do
  @moduledoc """
  Connection-level runtime monitor for HTTP/2 stream-id monotonicity (RFC 9113
  §5.1.1). This is the runtime companion to `Http2.StreamId.Protocol` (which
  proves, via TLC with `sessions: 2`, that two concurrent streams cannot share an
  id). Here a single connection-level monitor watches the sequence of stream
  opens and the server's obligation when the rule is broken.

  A new stream's id must exceed every id already opened. A branching `cast`
  (see `where:`-guarded cast branches) routes each open: an id above the
  high-water mark stays `:active`; an id at or below it is a §5.1.1 protocol
  error and routes to `:goaway_expected`, where the server MUST send a connection
  GOAWAY. Any other server frame there — the connection carrying on — is a
  server-blame violation.

  Wired live by `Http2.TapProxy`, this catches Bandit's real §5.1.1 divergence:
  Bandit silently drops a HEADERS on a lower id and keeps the connection alive
  instead of sending GOAWAY. Because that mishandling is *inaction*, a passive
  monitor cannot see it directly — the client must provoke the server (a PING);
  Bandit's PING ACK arriving in `:goaway_expected` (rather than a GOAWAY) is the
  server-blame violation. See the case study for the silent-drop-needs-provocation
  discussion.
  """
  use Accord.Protocol

  initial :active

  track :last_id, :non_neg_integer, default: 0, domain: 0..3, abstract: :monotonic

  model do
    domain :pos_integer, 1..4
  end

  state :active do
    cast {:open_stream, id :: pos_integer()} do
      branch goto: :active, where: fn {:open_stream, id}, tracks -> id > tracks.last_id end

      branch goto: :goaway_expected,
             where: fn {:open_stream, id}, tracks -> id <= tracks.last_id end

      update fn {:open_stream, id}, tracks -> %{tracks | last_id: id} end
    end

    # Normal connection liveness: the server ACKs PINGs and may eventually close.
    event :ping_ack, goto: :active
    event :goaway, goto: :closed
  end

  # A §5.1.1 protocol error has occurred. The server MUST send a connection
  # GOAWAY. Any other server frame — e.g. a PING ACK, meaning the connection is
  # still serving — is a server-blame violation (the server failed to go away).
  state :goaway_expected do
    event :goaway, goto: :closed
  end

  state :closed, terminal: true
end
