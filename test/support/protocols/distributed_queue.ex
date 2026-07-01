defmodule Accord.Test.DistributedQueue.Protocol do
  @moduledoc """
  Multi-worker job queue: the `distinct` showcase.

  The fence counter is shared (it lives on the queue); each worker's
  `holding` is per-session. The fencing constraint — every issued token
  must exceed the shared fence — is what makes leases unique across
  workers: TLC proves `distinct :holding` at `sessions: 2`.

  Drop the constraint (DistributedQueueUnguarded) and TLC hands both
  workers token 1 in two steps. This is the job-queue flagship's
  cross-worker claim — "no two workers hold the same lease" — made
  checkable.
  """
  use Accord.Protocol

  initial :idle

  track :fence, :non_neg_integer, default: 0, shared: true, domain: 0..3
  track :holding, :non_neg_integer, default: 0, domain: 0..3

  model do
    sessions 2
  end

  state :idle do
    on :checkout do
      branch({:job, token :: pos_integer()},
        goto: :working,
        where: fn {:job, token}, tracks -> token > tracks.fence end
      )

      branch :empty, goto: :idle

      update fn _msg, reply, tracks ->
        case reply do
          {:job, token} -> %{tracks | fence: token, holding: token}
          :empty -> tracks
        end
      end
    end

    on :stop, reply: :stopped, goto: :stopped
  end

  state :working do
    on {:ack, token :: pos_integer()} do
      guard fn {:ack, token}, tracks -> token == tracks.holding end
      branch :done, goto: :idle
      update fn _msg, _reply, tracks -> %{tracks | holding: 0} end
    end
  end

  state :stopped, terminal: true

  property :no_shared_lease do
    distinct :holding, empty: 0
  end
end
