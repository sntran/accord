defmodule Accord.TLA.SessionsTest do
  @moduledoc """
  Multi-session TLA+ emission.

  `sessions: 1` must leave emission unchanged (single-session output is
  the compatibility contract); `sessions: N` array-ifies per-session
  variables, quantifies actions over the acting session, and unlocks
  cross-session invariants like `exclusive`.
  """
  use ExUnit.Case, async: true

  alias Accord.TLA.{Compiler, ModelConfig}

  defp lock_config(sessions) do
    %ModelConfig{
      sessions: sessions,
      domains: %{
        client_id: {:model_values, 2},
        holder: {:model_values, 2},
        fence_token: 0..3,
        pos_integer: 1..3
      }
    }
  end

  defp compile(sessions) do
    ir = Accord.Test.DistributedLock.Protocol.__ir__()
    {:ok, result} = Compiler.compile(ir, lock_config(sessions))
    result
  end

  describe "single-session compatibility" do
    test "sessions: 1 emits no Sessions machinery" do
      result = compile(1)

      refute result.tla =~ "Sessions"
      refute result.cfg =~ "Sessions"
      # Scalar state variable, scalar preconditions.
      assert result.tla =~ ~s(state \\in {"locked", "stopped", "unlocked"})
      assert result.tla =~ ~s(/\\ state = "unlocked")
    end
  end

  describe "multi-session emission" do
    test "per-session variables become functions over Sessions" do
      result = compile(2)

      assert result.tla =~ "state \\in [Sessions -> {\"locked\", \"stopped\", \"unlocked\"}]"
      assert result.tla =~ "state = [s \\in Sessions |-> \"unlocked\"]"
      # Shared tracks stay scalar.
      assert result.tla =~ "fence_token \\in 0..3"
      assert result.tla =~ "fence_token = 0"
      refute result.tla =~ "fence_token \\in [Sessions"
    end

    test "actions existentially quantify the acting session" do
      result = compile(2)

      assert result.tla =~ "\\E s \\in Sessions, msg_client_id"
      assert result.tla =~ "state[s] = \"unlocked\""
      assert result.tla =~ "state' = [state EXCEPT ![s] = \"locked\"]"
    end

    test "shared track updates stay scalar assignments" do
      result = compile(2)

      assert result.tla =~ "fence_token' = reply_token"
      assert result.tla =~ "holder' = msg_client_id"
    end

    test "where: constraints read shared tracks as scalars" do
      result = compile(2)

      assert result.tla =~ "(holder = NULL /\\ reply_token > fence_token)"
    end

    test "exclusive becomes a cross-session invariant" do
      result = compile(2)

      assert result.tla =~
               "MutualExclusionExclusive == \\A si, sj \\in Sessions : " <>
                 "(state[si] = \"locked\" /\\ state[sj] = \"locked\") => si = sj"

      assert result.cfg =~ "INVARIANT MutualExclusionExclusive"
    end

    test "local invariants quantify over sessions" do
      result = compile(2)

      assert result.tla =~
               "\\A s \\in Sessions : ((state[s] = \"locked\") => (holder /= NULL))"
    end

    test "Sessions constant and symmetry reach the cfg" do
      result = compile(2)

      assert result.tla =~ "CONSTANTS NULL, mv1, mv2, mv3, s1, s2, Sessions"
      assert result.cfg =~ "CONSTANT Sessions = {s1, s2}"
      assert result.cfg =~ "CONSTANT s1 = s1"
      assert result.tla =~ "Symmetry == Permutations(Sessions)"
      assert result.cfg =~ "SYMMETRY Symmetry"
    end

    test "Terminating requires every session to be terminal" do
      result = compile(2)

      assert result.tla =~ "\\A s \\in Sessions : state[s] \\in {\"stopped\"}"
    end
  end

  describe "distinct" do
    test "distinct becomes a cross-session uniqueness invariant" do
      ir = Accord.Test.DistributedQueue.Protocol.__ir__()
      config = Accord.TLA.ModelConfig.apply_inline(%ModelConfig{}, ir)
      {:ok, result} = Compiler.compile(ir, config)

      assert result.tla =~
               "NoSharedLeaseDistinct == \\A si, sj \\in Sessions : " <>
                 "(si /= sj) => (holding[si] = 0 \\/ holding[si] /= holding[sj])"

      assert result.cfg =~ "INVARIANT NoSharedLeaseDistinct"
    end

    test "sessions: 1 annotates distinct instead of asserting it" do
      ir = %{Accord.Test.DistributedQueue.Protocol.__ir__() | model: []}
      {:ok, result} = Compiler.compile(ir, %ModelConfig{domains: %{pos_integer: 1..3}})

      assert result.tla =~ "requires multi-session checking"
      refute result.cfg =~ "NoSharedLeaseDistinct"
    end

    test "distinct over a shared track is E061" do
      error =
        assert_raise CompileError, fn ->
          defmodule BadDistinct do
            use Accord.Protocol, tla: :off

            initial :ready

            track :fence, :non_neg_integer, default: 0, shared: true

            state :ready do
              on :stop, reply: :stopped, goto: :done
            end

            state :done, terminal: true

            property :nonsense do
              distinct :fence, empty: 0
            end
          end
        end

      assert error.description =~ "E061"
      assert error.description =~ "shared track"
    end

    test "distinct over an undefined track is E061" do
      error =
        assert_raise CompileError, fn ->
          defmodule MissingDistinct do
            use Accord.Protocol, tla: :off

            initial :ready
            state :ready, terminal: true

            property :nonsense do
              distinct :ghost, empty: 0
            end
          end
        end

      assert error.description =~ "E061"
      assert error.description =~ ":ghost"
    end
  end

  describe "exclusive without multi-session" do
    test "sessions: 1 annotates exclusive instead of asserting it" do
      result = compile(1)

      assert result.tla =~ "requires multi-session checking"
      refute result.cfg =~ "MutualExclusionExclusive"
    end
  end
end
