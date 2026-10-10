defmodule Accord.Test.Probe.DivRem.Protocol do
  @moduledoc """
  Probe: `div/2` and `rem/2` on negative numbers.

  Elixir truncates toward zero: `div(-1, 2) == 0` and `rem(-1, 2) == -1`.
  The TLA+ operators `\\div` and `%` round toward negative infinity:
  `-1 \\div 2 = -1` and `-1 % 2 = 1`.
  """
  use Accord.Protocol

  initial :ready

  track :x, :integer, default: 0, domain: -2..2
  track :y, :integer, default: 0, domain: -2..2

  state :ready do
    on {:pick, n :: integer()} do
      guard fn {:pick, n}, _tracks -> div(n, 2) == 0 end
      reply :ok
      goto :ready
      update fn {:pick, n}, _reply, tracks -> %{tracks | x: n} end
    end

    on {:odd, n :: integer()} do
      guard fn {:odd, n}, _tracks -> rem(n, 2) == 1 end
      reply :ok
      goto :ready
      update fn {:odd, n}, _reply, tracks -> %{tracks | y: n} end
    end
  end
end
