defmodule Accord.CrossCheckTest do
  use ExUnit.Case, async: true

  @moduletag :tmp_dir
  # Each test starts several TLC processes, each with JVM startup.
  @moduletag timeout: 600_000

  alias Accord.CrossCheck
  alias Accord.CrossCheck.{Mutant, RandomProtocol, Report, TLAValue, TLC}
  alias Accord.Explore
  alias Accord.Explore.Model
  alias Accord.TLA.Compiler

  defp run(protocol, tmp_dir, opts \\ []) do
    CrossCheck.run(protocol, Keyword.merge([dir: tmp_dir, timeout: 60], opts))
  end

  defp outcome(report, check), do: Enum.find(report.outcomes, &(&1.check == check))

  describe "agreement with TLC" do
    test "a correct protocol: all checks match", %{tmp_dir: tmp_dir} do
      report = run(Accord.Examples.JobQueue.Protocol, tmp_dir)

      assert Report.ok?(report), Report.format(report)

      assert %{status: :match, detail: "11 states, 24 steps, depth 4" <> _} =
               outcome(report, "state space")

      assert %{status: :match, detail: "holds"} = outcome(report, "FenceMonotonic")
      assert %{status: :skipped} = outcome(report, "AcksOrdered")
    end

    test "a seeded bug: the same verdict, and each trace replays in the other checker",
         %{tmp_dir: tmp_dir} do
      report = run(Accord.Examples.JobQueue.ProtocolLeakyLease, tmp_dir)

      assert Report.ok?(report), Report.format(report)

      assert %{status: :match, detail: "violated in 3 states, both traces replay"} =
               outcome(report, "LeaseIffWorkingIdle")
    end

    test "two sessions: the state set and the symmetry-reduced count", %{tmp_dir: tmp_dir} do
      report = run(Accord.Test.DistributedLockUnguarded.Protocol, tmp_dir)

      assert Report.ok?(report), Report.format(report)
      assert %{status: :match} = outcome(report, "symmetry")
      assert %{status: :match} = outcome(report, "MutualExclusionExclusive")
    end

    test "deadlock and action property counterexamples", %{tmp_dir: tmp_dir} do
      deadlock = run(Accord.Test.DeadlockFail.Protocol, Path.join(tmp_dir, "deadlock"))
      action = run(Accord.Test.ActionFail.Protocol, Path.join(tmp_dir, "action"))

      assert Report.ok?(deadlock), Report.format(deadlock)
      assert Report.ok?(action), Report.format(action)

      assert %{status: :match, detail: "violated in 4 states" <> _} =
               outcome(deadlock, "Deadlock")

      assert %{status: :match, detail: "violated in 3 states" <> _} =
               outcome(action, "MonotonicLevel")
    end

    test "an infinite model: violations are compared, the state space is not",
         %{tmp_dir: tmp_dir} do
      report = run(Accord.Examples.Demand.ProtocolUnbounded, tmp_dir, max_states: 2_000)

      assert Report.ok?(report), Report.format(report)
      assert %{status: :inconclusive} = outcome(report, "state space")
      assert %{status: :match} = outcome(report, "DemandNeverNegative")
    end

    test "mutants of a protocol", %{tmp_dir: tmp_dir} do
      config = Model.model_config(Accord.Test.Lock.Protocol)

      for mutant <- Mutant.sample(Accord.Test.Lock.Protocol.__ir__(), 3, 1) do
        dir = Path.join(tmp_dir, inspect(mutant.ir.name))
        report = run(mutant.ir, dir, config: config, label: mutant.description)
        assert Report.ok?(report), Report.format(report)
      end
    end

    test "random protocols", %{tmp_dir: tmp_dir} do
      for seed <- 1..3 do
        {:ok, module, _source} = RandomProtocol.compile(seed)
        report = run(module, Path.join(tmp_dir, "p#{seed}"))
        assert Report.ok?(report), Report.format(report)
      end
    end
  end

  describe "liveness" do
    for {name, protocol} <- [
          {"each property with its own fairness", Accord.Test.FairnessLeak.Protocol},
          {"weak and strong fairness", Accord.Test.Probe.StrongFairness.Protocol},
          {"the fairness of a state timeout", Accord.Test.Probe.TimeoutFairness.Protocol},
          {"a lasso that stutters", Accord.Test.LivenessFail.Protocol}
        ] do
      @protocol protocol
      test name, %{tmp_dir: tmp_dir} do
        report = run(@protocol, tmp_dir)
        assert Report.ok?(report), Report.format(report)
      end
    end

    test "the replays reject a loop that is not fair", %{tmp_dir: tmp_dir} do
      protocol = Accord.Test.FairnessLeak.Protocol
      model = Model.build(protocol)
      {:ok, compiled} = Compiler.compile(protocol.__ir__(), model.config)
      module = compiled.state_space.module_name
      File.write!(Path.join(tmp_dir, module <> ".tla"), compiled.tla)

      ctx = %{
        model: model,
        compiled: compiled,
        module: module,
        dir: tmp_dir,
        tlc_opts: [jar: TLC.find_jar(), timeout: 60]
      }

      # The retry loop violates the property that assumes fair retries,
      # but under fair finishes the loop is not fair: :finish is always
      # enabled and never runs.
      lasso = Explore.run(model).violations["FinishesWhenRetryIsFair"]
      assert :ok = CrossCheck.replay_lasso_in_tlc(ctx, "FinishesWhenRetryIsFair", lasso)
      assert {:error, _} = CrossCheck.replay_lasso_in_tlc(ctx, "FinishesWhenFinishIsFair", lasso)

      tlc_trace =
        Enum.map(lasso.trace, &%{action: nil, vars: TLAValue.from_state(model, &1.state)})

      loop = {:back_to, lasso.loop.to}

      assert :ok =
               CrossCheck.replay_lasso_in_explorer(
                 ctx,
                 "FinishesWhenRetryIsFair",
                 tlc_trace,
                 loop
               )

      assert {:error, "the loop is not fair" <> _} =
               CrossCheck.replay_lasso_in_explorer(
                 ctx,
                 "FinishesWhenFinishIsFair",
                 tlc_trace,
                 loop
               )
    end
  end

  # Each probe uses a form where the TLA+ translation once differed from
  # the runtime monitor. The cross-check found each difference; the
  # translation now makes the same choices as the monitor.
  describe "probes for fixed translation defects" do
    for {name, protocol} <- [
          {"div/2 and rem/2 on negative numbers", Accord.Test.Probe.DivRem.Protocol},
          {"an update that ignores an earlier message argument",
           Accord.Test.Probe.UnderscoreArgs.Protocol},
          {"a reply with two values in an update case", Accord.Test.Probe.TripleReply.Protocol},
          {"two call branches that accept the same reply",
           Accord.Test.Probe.OverlapBranches.Protocol},
          {"two cast branches whose where: predicates overlap",
           Accord.Test.Probe.OverlapCast.Protocol}
        ] do
      @protocol protocol
      test name, %{tmp_dir: tmp_dir} do
        report = run(@protocol, tmp_dir)
        assert Report.ok?(report), Report.format(report)
        assert %{status: :match} = outcome(report, "state space")
      end
    end
  end

  # A replay that accepts every trace would make each "both traces
  # replay" result empty. These tests give a wrong trace to each replay.
  describe "replays reject a wrong trace" do
    setup %{tmp_dir: tmp_dir} do
      protocol = Accord.Examples.JobQueue.ProtocolLeakyLease
      config = Model.model_config(protocol)
      {:ok, compiled} = Compiler.compile(protocol.__ir__(), config)
      model = Model.build(protocol)
      module = compiled.state_space.module_name
      File.write!(Path.join(tmp_dir, module <> ".tla"), compiled.tla)

      ctx = %{
        model: model,
        compiled: compiled,
        module: module,
        dir: tmp_dir,
        tlc_opts: [jar: TLC.find_jar(), timeout: 60]
      }

      %{"LeaseIffWorkingIdle" => violation} = Explore.run(model).violations
      %{ctx: ctx, trace: violation.trace}
    end

    test "TLC rejects an explorer trace with a missing step", %{ctx: ctx, trace: trace} do
      assert :ok = CrossCheck.replay_in_tlc(ctx, "LeaseIffWorkingIdle", :invariant, trace)

      [first, _second, third] = trace

      assert {:error, _} =
               CrossCheck.replay_in_tlc(ctx, "LeaseIffWorkingIdle", :invariant, [first, third])
    end

    test "TLC rejects a trace whose last state does not violate the check",
         %{ctx: ctx, trace: trace} do
      assert {:error, _} =
               CrossCheck.replay_in_tlc(
                 ctx,
                 "LeaseIffWorkingIdle",
                 :invariant,
                 Enum.take(trace, 2)
               )
    end

    test "the explorer rejects a TLC trace with a changed value", %{ctx: ctx, trace: trace} do
      tlc_trace = Enum.map(trace, &%{action: nil, vars: TLAValue.from_state(ctx.model, &1.state)})

      assert :ok =
               CrossCheck.replay_in_explorer(ctx, "LeaseIffWorkingIdle", :invariant, tlc_trace)

      changed = List.update_at(tlc_trace, 1, &put_in(&1.vars["fence"], 2))

      assert {:error, "no explorer step makes state 2" <> _} =
               CrossCheck.replay_in_explorer(ctx, "LeaseIffWorkingIdle", :invariant, changed)
    end
  end
end
