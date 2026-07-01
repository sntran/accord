defmodule Accord.Test.LivenessFair.Protocol do
  @moduledoc """
  Pass fixture: liveness under per-action fairness.

  The server may keep replying `:continue` (flipping a track so the loop
  is a real variable-changing cycle, not a stutter), but
  `assuming: [:spin]` asserts weak fairness on every spin action —
  including the `:finished` branch — so TLC verifies `spinning ~> done`.

  Without the `assuming:`, blanket `WF_vars(Next)` would accept the
  infinite flip cycle as a counterexample (see LivenessUnfair).
  """
  use Accord.Protocol

  initial :spinning

  track :flips, :non_neg_integer, default: 0

  state :spinning do
    on :spin do
      branch :continue, goto: :spinning
      branch :finished, goto: :done

      update fn _msg, reply, tracks ->
        case reply do
          :continue -> %{tracks | flips: rem(tracks.flips + 1, 2)}
          :finished -> tracks
        end
      end
    end
  end

  state :done, terminal: true

  property :eventually_done do
    liveness in_state(:spinning), leads_to: in_state(:done), assuming: [:spin]
  end
end
