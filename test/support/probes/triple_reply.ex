defmodule Accord.Test.Probe.TripleReply.Protocol do
  @moduledoc """
  Probe: an update that reads a reply with two values, `{:ok, a, b}`.
  """
  use Accord.Protocol

  initial :ready

  track :x, :non_neg_integer, default: 0, domain: 0..3

  model do
    domain :a, 1..2
    domain :b, 0..1
  end

  state :ready do
    on :get do
      branch {:ok, a :: non_neg_integer(), b :: non_neg_integer()}, goto: :ready
      branch :empty, goto: :ready

      update fn :get, reply, tracks ->
        case reply do
          {:ok, a, _b} -> %{tracks | x: a}
          _ -> tracks
        end
      end
    end
  end
end
