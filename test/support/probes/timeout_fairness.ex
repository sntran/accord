defmodule Accord.Test.Probe.TimeoutFairness.Protocol do
  @moduledoc """
  Probe: a state timeout is always weakly fair.

  The client can poll forever in `:waiting`. The timeout of `:waiting`
  is enabled all the time, and a real timer always fires, so `:waiting`
  leads to `:expired`, also with no fair message (`assuming: []`).
  Without the timeout, `:open` can stay forever.
  """
  use Accord.Protocol

  initial :open

  state :open do
    on :wait, reply: :ok, goto: :waiting
    on :poll, reply: :ok, goto: :open
  end

  state :waiting do
    state_timeout 100, goto: :expired
    on :poll, reply: :ok, goto: :waiting
  end

  state :expired do
    on :reset, reply: :ok, goto: :open
  end

  property :timer_fires do
    liveness in_state(:waiting), leads_to: in_state(:expired), assuming: []
  end

  property :open_ends do
    liveness in_state(:open), leads_to: in_state(:waiting), assuming: []
  end
end
