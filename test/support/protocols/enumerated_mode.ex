defmodule Accord.Test.EnumeratedMode.Protocol do
  @moduledoc """
  An atom-typed track compared and assigned by name — the fixture that
  exercises H4's consistent atom rendering.

  `mode` is atom-typed with an explicit enumerated `domain:`, so every
  site renders it the same concrete way: the domain as `{"normal",
  "degraded"}`, the default as `"normal"`, guards as `mode = "normal"`,
  updates as `mode' = "degraded"`, and the invariant over it likewise.
  Nothing else in the suite compares atoms in a formula, so without this
  the atom-rendering path is never model-checked.
  """
  use Accord.Protocol

  initial :running

  track :mode, :atom, default: :normal, domain: [:normal, :degraded]

  state :running do
    on :degrade do
      guard fn _msg, tracks -> tracks.mode == :normal end
      reply :ok
      goto :running
      update fn _msg, _reply, tracks -> %{tracks | mode: :degraded} end
    end

    on :recover do
      guard fn _msg, tracks -> tracks.mode == :degraded end
      reply :ok
      goto :running
      update fn _msg, _reply, tracks -> %{tracks | mode: :normal} end
    end

    on :stop, reply: :stopped, goto: :stopped
  end

  state :stopped, terminal: true

  property :mode_is_known do
    invariant :running, fn _msg, tracks ->
      tracks.mode == :normal or tracks.mode == :degraded
    end
  end
end
