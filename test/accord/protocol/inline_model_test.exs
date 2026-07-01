defmodule Accord.Protocol.InlineModelTest do
  @moduledoc """
  Inline model configuration: track-level `domain:`/`model_init:` and
  the `model do ... end` block.
  """
  use ExUnit.Case, async: true

  alias Accord.TLA.{Files, ModelConfig}

  defmodule InlineProtocol do
    use Accord.Protocol

    initial :ready

    track :balance, :non_neg_integer, default: 1000, domain: 0..10, model_init: 5
    track :attempts, :non_neg_integer, default: 0

    model do
      domain :attempts, 0..2
      domain :amount, 1..4
      max_list_length 4
      state_constraint "balance >= 0"
    end

    state :ready do
      on {:spend, amount :: pos_integer()} do
        guard fn {:spend, amount}, tracks -> amount <= tracks.balance end
        reply :ok
        goto :ready

        update fn {:spend, amount}, _reply, tracks ->
          %{tracks | balance: tracks.balance - amount}
        end
      end

      on :stop, reply: :stopped, goto: :stopped
    end

    state :stopped, terminal: true
  end

  test "track-level domain and model_init reach the spec" do
    {tla_path, _} = Files.paths(InlineProtocol)
    tla = File.read!(tla_path)

    # Domain 0..10 instead of the 0..3 builtin (which default: 1000 would
    # have violated — the model_init: 5 keeps Init inside the domain).
    assert tla =~ "balance \\in 0..10"
    assert tla =~ "balance = 5"
  end

  test "model block domains, constraint, and message domains apply" do
    {tla_path, cfg_path} = Files.paths(InlineProtocol)
    tla = File.read!(tla_path)
    cfg = File.read!(cfg_path)

    assert tla =~ "attempts \\in 0..2"
    assert tla =~ "msg_amount \\in 1..4"
    assert tla =~ "StateConstraint == balance >= 0"
    assert cfg =~ "CONSTRAINT StateConstraint"
  end

  test "apply_inline gives inline sources the highest precedence" do
    ir = InlineProtocol.__ir__()

    config =
      ModelConfig.apply_inline(
        %ModelConfig{domains: %{balance: 0..99, other: 1..2}, sessions: 1},
        ir
      )

    # Inline wins over the file-provided domain; unrelated entries survive.
    assert config.domains.balance == 0..10
    assert config.domains.other == 1..2
    assert config.domains.attempts == 0..2
    assert config.init.balance == 5
    assert config.max_list_length == 4
    assert config.state_constraint == "balance >= 0"
  end

  test "sessions can be set inline" do
    ir = %{InlineProtocol.__ir__() | model: [{:sessions, 2}]}
    config = ModelConfig.apply_inline(%ModelConfig{}, ir)

    assert config.sessions == 2
  end
end
