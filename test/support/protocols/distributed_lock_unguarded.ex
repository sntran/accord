defmodule Accord.Test.DistributedLockUnguarded.Protocol do
  @moduledoc """
  Failure fixture: DistributedLock without the `holder == nil` acquire
  conjunct.

  The fencing token is still monotonic, but nothing stops a second
  session from acquiring while the first holds the lock — TLC finds the
  two-sessions-both-locked interleaving and the mutual-exclusion
  invariant fails. This is the fencing-tokens-alone-are-not-a-lock bug,
  found exhaustively at design time.
  """
  use Accord.Protocol, model: "test/support/protocols/distributed_lock_model.exs"

  initial :unlocked

  track :holder, :term, default: nil, shared: true
  track :fence_token, :non_neg_integer, default: 0, shared: true

  state :unlocked do
    on {:acquire, client_id :: term()} do
      branch({:ok, token :: pos_integer()},
        goto: :locked,
        where: fn {:ok, token}, tracks -> token > tracks.fence_token end
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
end
