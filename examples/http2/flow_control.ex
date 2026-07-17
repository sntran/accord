defmodule Accord.Examples.Http2.FlowControl.Protocol do
  @moduledoc """
  HTTP/2 send-window flow control (RFC 9113 §6.9 / §6.9.1), from the Bandit case
  study round 2.

  The server's per-stream send window is the octet budget the peer has granted us
  to send. The peer's WINDOW_UPDATE — a one-way `cast` — increments it; the
  server's DATA — a one-way server-push `event` — decrements it. §6.9.1 requires
  that a WINDOW_UPDATE not push the window past 2^31-1; the `const :max` ceiling
  stands in for that bound, with a bounded head-room domain so an overflow is
  representable. TLC proves the window never overflows.
  """
  use Accord.Protocol

  initial :open

  const :max, 3

  track :send_window, :non_neg_integer, default: 1, domain: 0..6

  model do
    domain :pos_integer, 1..3
  end

  state :open do
    # Peer grants quota. §6.9.1: the increment must not push us past the ceiling.
    cast {:window_update, inc :: pos_integer()} do
      guard fn {:window_update, inc}, tracks -> tracks.send_window + inc <= const(:max) end

      update fn {:window_update, inc}, tracks ->
        %{tracks | send_window: tracks.send_window + inc}
      end
    end

    # Server pushes DATA, never more than the window allows.
    event {:send_data, n :: pos_integer()} do
      goto :open
      guard fn {:send_data, n}, tracks -> n <= tracks.send_window end
      update fn {:send_data, n}, tracks -> %{tracks | send_window: tracks.send_window - n} end
    end
  end

  property :window_never_overflows do
    invariant fn tracks -> tracks.send_window <= const(:max) end
  end
end
