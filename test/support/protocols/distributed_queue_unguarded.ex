defmodule Accord.Test.DistributedQueueUnguarded.Protocol do
  @moduledoc """
  Failure fixture: the multi-worker queue without the fencing constraint.

  Nothing forces issued tokens past the shared fence, so the queue may
  hand token 1 to both workers — TLC finds two sessions holding the
  same lease in two steps, violating `distinct :holding`.
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
      branch {:job, token :: pos_integer()}, goto: :working
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
