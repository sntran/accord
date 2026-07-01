defmodule Accord.Test.LivenessUnfair.Protocol do
  @moduledoc """
  Failure fixture: liveness without `assuming:` under blanket fairness.

  Identical to LivenessFair except the liveness check names no fair
  actions. `WF_vars(Next)` only rules out infinite stuttering; the
  infinite `:continue` flip cycle is a real variable-changing loop, so
  TLC produces the loop counterexample — exactly the failure mode W005
  warns about.
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
    liveness in_state(:spinning), leads_to: in_state(:done)
  end
end
