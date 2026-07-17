defmodule Accord.Test.BranchingCast.Protocol do
  @moduledoc """
  Exercises `where:`-guarded branches on a one-way `cast`: a stream id above the
  high-water mark stays open; one at or below it routes to a protocol-error state.
  The two branches compile to one TLA+ action each, guarded by the branch
  predicate — so TLC explores both. Used to pin the cast-branch feature.
  """
  use Accord.Protocol

  initial :active

  track :last_id, :non_neg_integer, default: 0, domain: 0..3, abstract: :monotonic

  model do
    domain :pos_integer, 1..4
  end

  state :active do
    cast {:open_stream, id :: pos_integer()} do
      branch goto: :active, where: fn {:open_stream, id}, tracks -> id > tracks.last_id end
      branch goto: :rejected, where: fn {:open_stream, id}, tracks -> id <= tracks.last_id end
      update fn {:open_stream, id}, tracks -> %{tracks | last_id: id} end
    end
  end

  state :rejected, terminal: true
end
