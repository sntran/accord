defmodule Accord.Examples.JobQueue.ProtocolLeakyLease do
  @moduledoc """
  Seeded design bug: the expiry event forgets to release the lease.

  The `{:lease_expired, _}` update returns `tracks` with `holding`
  untouched. TLC's counterexample takes three actions: checkout →
  `{:job, 1}` (fence = holding = 1), the expiry event fires — and the
  worker is `:idle` with `holding = 1`, violating `lease_iff_working`.

  Production meaning: the lease expired, the queue will hand the job to
  another worker, but this worker still believes it owns it — double
  processing, the exact interleaving fencing tokens exist to prevent,
  found exhaustively before any code ran.
  """
  use Accord.Protocol

  initial :idle

  track :fence, :non_neg_integer, default: 0, domain: 0..3
  track :holding, :non_neg_integer, default: 0, domain: 0..3

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

    # BUG: the update forgets `holding: 0`.
    event {:lease_expired, token :: pos_integer()} do
      guard fn {:lease_expired, token}, tracks -> token == tracks.holding end
      goto :idle
      update fn {:lease_expired, _token}, tracks -> tracks end
    end
  end

  state :stopped, terminal: true

  property :lease_iff_working do
    invariant :working, fn _msg, tracks -> tracks.holding > 0 end
    invariant :idle, fn _msg, tracks -> tracks.holding == 0 end
  end
end
