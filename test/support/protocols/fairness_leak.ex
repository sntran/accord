defmodule Accord.Test.FairnessLeak.Protocol do
  @moduledoc """
  Two liveness properties with different `assuming:` tags — the fixture
  that pins the H3 fix.

  `finishes_when_finish_is_fair` is provable under its own assumption:
  `:finish` stays enabled in `:working`, so weak fairness on it forces
  progress to `:done`.

  `finishes_when_retry_is_fair` is *not* provable under its own
  assumption: `:retry` can flip the flag forever without ever finishing.
  It only ever "passed" because the old shared `FairSpec` pooled every
  property's fairness together, so this property silently borrowed
  `:finish`'s weak fairness. With per-property fairness it fails, which is
  why `check_test.exs` asserts this protocol's temporal check fails.
  """
  use Accord.Protocol

  initial :working

  track :flag, :boolean, default: false

  state :working do
    on :retry do
      reply :retried
      goto :working
      update fn _msg, _reply, tracks -> %{tracks | flag: not tracks.flag} end
    end

    on :finish, reply: :finished, goto: :done
  end

  state :done, terminal: true

  property :finishes_when_finish_is_fair do
    liveness in_state(:working), leads_to: in_state(:done), assuming: [:finish]
  end

  property :finishes_when_retry_is_fair do
    liveness in_state(:working), leads_to: in_state(:done), assuming: [:retry]
  end
end
