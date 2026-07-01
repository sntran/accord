defmodule Accord.Test.Monotonic.Protocol do
  @moduledoc """
  Minimal protocol whose action property can be violated at runtime.

  Unlike Lock, the `set` transition carries no `where:` constraint, so a
  misbehaving server (or client-driven value) can decrease the counter
  and trip the action property — used to test action-violation spans and
  blame without the constraint intercepting first.
  """
  use Accord.Protocol

  initial :ready

  track :counter, :non_neg_integer, default: 0

  state :ready do
    on {:set, value :: non_neg_integer()} do
      reply :ok
      goto :ready

      update fn {:set, value}, _reply, tracks ->
        %{tracks | counter: value}
      end
    end

    on :stop, reply: :stopped, goto: :stopped
  end

  state :stopped, terminal: true

  property :monotonic_counter do
    action fn old, new -> new.counter >= old.counter end
  end
end
