defmodule Accord.Test.Probe.StrongFairness.Protocol do
  @moduledoc """
  Probe: weak and strong fairness give different verdicts.

  `:finish` is enabled only when `ready` is true, and `:tick` flips
  `ready`. A behavior that ticks forever enables `:finish` infinitely
  often, but not continuously:

  - With weak fairness, `:finish` need not run, so `:working` need not
    lead to `:done`.
  - With strong fairness, `:finish` must run, so `:working` leads to
    `:done`.
  """
  use Accord.Protocol

  initial :working

  track :ready, :boolean, default: false

  state :working do
    on :tick do
      reply :ok
      goto :working
      update fn :tick, _reply, tracks -> %{tracks | ready: not tracks.ready} end
    end

    on :finish do
      guard fn :finish, tracks -> tracks.ready end
      reply :done
      goto :done
    end
  end

  state :done, terminal: true

  property :weak_finish do
    liveness in_state(:working), leads_to: in_state(:done), assuming: [:finish, :tick]
  end

  property :strong_finish do
    liveness in_state(:working),
      leads_to: in_state(:done),
      assuming: [:finish, :tick],
      fairness: :strong
  end
end
