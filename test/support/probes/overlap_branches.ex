defmodule Accord.Test.Probe.OverlapBranches.Protocol do
  @moduledoc """
  Probe: two call branches that accept the same reply.

  The monitor gives a reply to the first branch whose type matches and
  whose `where:` holds. So `{:ok, 2}` and `{:ok, 3}` go to `:high`, never
  to `:low`.
  """
  use Accord.Protocol

  initial :ready

  track :last, :non_neg_integer, default: 0, domain: 0..3

  model do
    domain :n, 1..3
  end

  state :ready do
    on :read do
      branch({:ok, n :: pos_integer()},
        goto: :high,
        where: fn {:ok, n}, _tracks -> n > 1 end
      )

      branch({:ok, n :: pos_integer()}, goto: :low)

      update fn :read, {:ok, n}, tracks -> %{tracks | last: n} end
    end
  end

  state :high do
    on :reset, reply: :ok, goto: :ready
  end

  state :low do
    on :reset, reply: :ok, goto: :ready
  end
end
