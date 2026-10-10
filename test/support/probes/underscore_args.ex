defmodule Accord.Test.Probe.UnderscoreArgs.Protocol do
  @moduledoc """
  Probe: an update that ignores the first message argument.

  The update reads `b`, the second argument. The model must bind `b` to
  the second argument, also when the first argument has an underscore
  name.
  """
  use Accord.Protocol

  initial :ready

  track :x, :non_neg_integer, default: 0, domain: 0..3
  track :y, :non_neg_integer, default: 0, domain: 0..3

  model do
    domain :a, 0..1
    domain :b, 2..3
  end

  state :ready do
    on {:put, a :: non_neg_integer(), b :: non_neg_integer()} do
      reply :ok
      goto :ready
      update fn {:put, _a, b}, _reply, tracks -> %{tracks | x: b} end
    end

    event {:push, a :: non_neg_integer(), b :: non_neg_integer()} do
      goto :ready
      update fn {:push, _a, b}, tracks -> %{tracks | y: b} end
    end
  end
end
