defmodule Accord.Examples.PhoenixChannels.Channel.Protocol do
  @moduledoc """
  The Phoenix Channels protocol, per `(socket, topic)`, as an accord contract.

  Phoenix multiplexes many channels over one socket, keyed by topic (and
  disambiguated by `join_ref`). Each channel is an independent lifecycle:
  `not_joined → joining → joined → leaving → closed`. Messages are one-way in
  both directions — the client's frames are `cast`s, the server's frames are
  server-push `event`s — with `phx_reply` correlating a server reply to a client
  request via its `ref`.

  This spec is **conformant** (the correct protocol, no seeded bug). It is used
  two ways: model-checked by TLC to prove the lifecycle is sound, and run as a
  live monitor via a wrapping serializer (`Accord.Examples.PhoenixChannels.
  Serializer`) that taps every channel message on a real Phoenix endpoint and
  assigns blame.

  ## The reply obligation (where the value is)

  Phoenix does not itself enforce that a channel replies exactly once per
  request — a `handle_in` that replies twice, or emits a reply for a `ref` no
  client sent, violates the protocol and the framework does not stop it. The
  `pending` track counts replies the server still owes: a client message
  carrying a `ref` (a join or a `push`) increments it, a `phx_reply` decrements
  it. The guard on `phx_reply` (`pending > 0`) is the obligation — at runtime a
  reply when nothing is outstanding fails it and is blamed on the **server**; in
  TLC it is the enabling condition that models a conformant server. `pending`'s
  domain has one value of head room above the `state_constraint` bound so the
  counter is representable at the boundary (bounded model checking); the runtime
  counter is unbounded, so pipelined requests never cause a false positive.

  A reply carries a status (`ok`/`error`); the tap maps it to `:phx_reply_ok` or
  `:phx_reply_error`. In `:joining` the status decides the outcome (a join can be
  rejected → `:closed`); once `:joined`, either status is a normal push reply.
  """
  use Accord.Protocol

  initial :not_joined

  track :pending, :non_neg_integer, default: 0, domain: 0..4

  model do
    # Bound the reply backlog for model checking (one below the domain's head
    # room). Runtime is unbounded — this only shapes TLC's exploration.
    state_constraint "pending <= 3"
  end

  state :not_joined do
    # A client must join a topic before sending anything else on it. The join
    # expects a reply, so it increments the backlog.
    cast :phx_join do
      goto :joining
      update fn _msg, tracks -> %{tracks | pending: tracks.pending + 1} end
    end

    # The server's error reply to a premature client message (a push before
    # join) — Phoenix answers "unmatched topic". Benign here; no reply is owed.
    event :phx_reply_error, goto: :not_joined
  end

  state :joining do
    # The join was accepted.
    event :phx_reply_ok do
      goto :joined
      guard fn _msg, tracks -> tracks.pending > 0 end
      update fn _msg, tracks -> %{tracks | pending: tracks.pending - 1} end
    end

    # The join was rejected — the channel never opens.
    event :phx_reply_error do
      goto :closed
      guard fn _msg, tracks -> tracks.pending > 0 end
      update fn _msg, tracks -> %{tracks | pending: tracks.pending - 1} end
    end

    # The channel process can still crash while joining.
    event :phx_error, goto: :closed
  end

  state :joined do
    # A client push that expects a reply (carries a ref).
    cast :push do
      goto :joined
      update fn _msg, tracks -> %{tracks | pending: tracks.pending + 1} end
    end

    # A fire-and-forget client push (no ref) — no reply owed.
    cast :push_noreply, goto: :joined

    # The server's reply to a push. Either status is fine; it must correspond to
    # an outstanding request — a reply with nothing pending is an excess reply
    # (server blame).
    event :phx_reply_ok do
      goto :joined
      guard fn _msg, tracks -> tracks.pending > 0 end
      update fn _msg, tracks -> %{tracks | pending: tracks.pending - 1} end
    end

    event :phx_reply_error do
      goto :joined
      guard fn _msg, tracks -> tracks.pending > 0 end
      update fn _msg, tracks -> %{tracks | pending: tracks.pending - 1} end
    end

    # A server-initiated push (broadcast or `push/3`), carries no client ref.
    event :s_push, goto: :joined

    # The client leaves the channel. A leave carries a ref and is acknowledged
    # with a reply before the close, so it too owes a reply.
    cast :phx_leave do
      goto :leaving
      update fn _msg, tracks -> %{tracks | pending: tracks.pending + 1} end
    end

    # The channel closed: gracefully (phx_close) or by crashing (phx_error).
    event :phx_close, goto: :closed
    event :phx_error, goto: :closed
  end

  state :leaving do
    # A reply for an in-flight request may still arrive before the close.
    event :phx_reply_ok do
      goto :leaving
      guard fn _msg, tracks -> tracks.pending > 0 end
      update fn _msg, tracks -> %{tracks | pending: tracks.pending - 1} end
    end

    event :phx_reply_error do
      goto :leaving
      guard fn _msg, tracks -> tracks.pending > 0 end
      update fn _msg, tracks -> %{tracks | pending: tracks.pending - 1} end
    end

    event :phx_close, goto: :closed
    event :phx_error, goto: :closed
  end

  state :closed, terminal: true
end
