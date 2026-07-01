defmodule Accord.Test.DistributedLock.Protocol do
  @moduledoc """
  Multi-session fencing-token lock: the concurrency flagship.

  `holder` and `fence_token` are shared tracks — they live on the lock
  server and are observed by every session. At `sessions: 2`, TLC
  interleaves two clients contending for the lock and proves mutual
  exclusion: the acquire constraint requires the lock to be free
  (`holder == nil`) and the token fresh (`token > fence_token`).

  Drop the `holder == nil` conjunct (DistributedLockUnguarded) and TLC
  produces the two-sessions-both-locked counterexample — the concurrency
  bug a single-session model structurally cannot represent.

  Note the deliberate ABSENCE of the single-session Lock's
  `unlocked => holder == nil` invariant: with shared tracks it would
  quantify over all sessions, and one session being unlocked while
  another holds the lock is exactly the intended behavior.
  """
  use Accord.Protocol, model: "test/support/protocols/distributed_lock_model.exs"

  initial :unlocked

  track :holder, :term, default: nil, shared: true
  track :fence_token, :non_neg_integer, default: 0, shared: true

  state :unlocked do
    on {:acquire, client_id :: term()} do
      branch({:ok, token :: pos_integer()},
        goto: :locked,
        where: fn {:ok, token}, tracks ->
          tracks.holder == nil and token > tracks.fence_token
        end
      )

      branch {:error, :already_held}, goto: :unlocked

      update fn {:acquire, client_id}, reply, tracks ->
        case reply do
          {:ok, token} -> %{tracks | holder: client_id, fence_token: token}
          _ -> tracks
        end
      end
    end

    on :stop, reply: :stopped, goto: :stopped
  end

  state :locked do
    on {:release, token :: pos_integer()} do
      branch :ok, goto: :unlocked
      branch {:error, :invalid_token}, goto: :locked

      update fn _msg, reply, tracks ->
        case reply do
          :ok -> %{tracks | holder: nil}
          _ -> tracks
        end
      end
    end

    on :stop, reply: :stopped, goto: :stopped
  end

  state :stopped, terminal: true

  property :mutual_exclusion do
    exclusive :locked
  end

  property :monotonic_tokens do
    action fn old, new -> new.fence_token >= old.fence_token end
  end

  property :locked_holder do
    invariant :locked, fn _msg, tracks -> tracks.holder != nil end
  end
end
