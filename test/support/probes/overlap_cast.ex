defmodule Accord.Test.Probe.OverlapCast.Protocol do
  @moduledoc """
  Probe: two cast branches whose `where:` predicates overlap.

  The monitor takes the first branch whose `where:` holds. So an id above
  1 goes to `:big`, never to `:any`.
  """
  use Accord.Protocol

  initial :ready

  track :last, :non_neg_integer, default: 0, domain: 0..3

  model do
    domain :id, 1..3
  end

  state :ready do
    cast {:open, id :: pos_integer()} do
      branch goto: :big, where: fn {:open, id}, _tracks -> id > 1 end
      branch goto: :any, where: fn {:open, _id}, _tracks -> true end
      update fn {:open, id}, tracks -> %{tracks | last: id} end
    end
  end

  state :big, terminal: true
  state :any, terminal: true
end
