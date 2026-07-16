defmodule Accord.CompatTest do
  @moduledoc """
  Protocol compatibility: can old clients talk to the new contract?
  """
  use ExUnit.Case, async: true

  alias Accord.Compat
  alias Accord.Compat.Snapshot

  defmodule V1 do
    use Accord.Protocol, tla: :off

    initial :idle

    track :fence, :non_neg_integer, default: 0

    state :idle do
      on {:checkout, worker :: atom()} do
        branch {:job, pos_integer()}, goto: :working
        branch :empty, goto: :idle

        update fn _msg, reply, tracks ->
          case reply do
            {:job, token} -> %{tracks | fence: token}
            :empty -> tracks
          end
        end
      end

      on :stop, reply: :stopped, goto: :stopped
    end

    state :working do
      on {:ack, token :: pos_integer()}, reply: :done, goto: :idle

      event {:lease_expired, token :: pos_integer()}, goto: :idle
    end

    state :stopped, terminal: true
  end

  # A compatible evolution: widened argument, narrowed reply, a brand-new
  # message and a brand-new state (old clients simply never use them).
  defmodule V2Compatible do
    use Accord.Protocol, tla: :off

    initial :idle

    track :fence, :non_neg_integer, default: 0

    state :idle do
      # Widened: atom() → term() (contravariant, fine).
      on {:checkout, worker :: term()} do
        branch {:job, pos_integer()}, goto: :working
        branch :empty, goto: :idle

        update fn _msg, reply, tracks ->
          case reply do
            {:job, token} -> %{tracks | fence: token}
            :empty -> tracks
          end
        end
      end

      # New message: old clients never send it.
      on :pause, reply: :paused, goto: :paused

      on :stop, reply: :stopped, goto: :stopped
    end

    state :working do
      on {:ack, token :: pos_integer()}, reply: :done, goto: :idle

      event {:lease_expired, token :: pos_integer()}, goto: :idle
    end

    # New state reachable only via the new message path.
    state :paused do
      on :resume, reply: :ok, goto: :idle
    end

    state :stopped, terminal: true
  end

  describe "compatible evolutions" do
    test "identity" do
      result = Compat.check(V1, V1)

      assert result.compatible?
      assert result.errors == []
      assert result.warnings == []
    end

    test "widened args, new messages, new states" do
      result = Compat.check(V1, V2Compatible)

      assert result.compatible?
      assert result.errors == []
    end

    test "the dual direction is a different question" do
      # New clients send :pause, which V1 does not accept; V1 also lacks
      # the :paused state entirely.
      result = Compat.check(V2Compatible, V1)

      refute result.compatible?
      assert Enum.any?(result.errors, &(&1.code == "C003" and &1.message =~ ":pause"))
      assert Enum.any?(result.errors, &(&1.code == "C001" and &1.message =~ ":paused"))
    end
  end

  describe "breaking changes" do
    defmodule RemovedMessage do
      use Accord.Protocol, tla: :off

      initial :idle

      state :idle do
        on {:checkout, worker :: atom()} do
          branch {:job, pos_integer()}, goto: :working
          branch :empty, goto: :idle
        end
      end

      state :working do
        on {:ack, token :: pos_integer()}, reply: :done, goto: :idle
        event {:lease_expired, token :: pos_integer()}, goto: :idle
      end
    end

    test "removing a message is C003" do
      result = Compat.check(V1, RemovedMessage)

      refute result.compatible?
      assert Enum.any?(result.errors, &(&1.code == "C003" and &1.message =~ ":stop"))
    end

    defmodule NarrowedArg do
      use Accord.Protocol, tla: :off

      initial :idle

      state :idle do
        # Narrowed: atom() → literal :w1 — old clients send other atoms.
        on {:checkout, worker :: :w1} do
          branch {:job, pos_integer()}, goto: :working
          branch :empty, goto: :idle
        end

        on :stop, reply: :stopped, goto: :stopped
      end

      state :working do
        on {:ack, token :: pos_integer()}, reply: :done, goto: :idle
        event {:lease_expired, token :: pos_integer()}, goto: :idle
      end

      state :stopped, terminal: true
    end

    test "narrowing an argument is C004" do
      result = Compat.check(V1, NarrowedArg)

      refute result.compatible?
      assert Enum.any?(result.errors, &(&1.code == "C004"))
    end

    defmodule WidenedReply do
      use Accord.Protocol, tla: :off

      initial :idle

      state :idle do
        on {:checkout, worker :: atom()} do
          branch {:job, pos_integer()}, goto: :working
          branch :empty, goto: :idle
          # New reply old clients do not understand.
          branch {:backoff, pos_integer()}, goto: :idle
        end

        on :stop, reply: :stopped, goto: :stopped
      end

      state :working do
        on {:ack, token :: pos_integer()}, reply: :done, goto: :idle
        event {:lease_expired, token :: pos_integer()}, goto: :idle
      end

      state :stopped, terminal: true
    end

    test "a new reply old clients cannot handle is C005" do
      result = Compat.check(V1, WidenedReply)

      refute result.compatible?
      assert Enum.any?(result.errors, &(&1.code == "C005" and &1.message =~ "backoff"))
    end

    defmodule RetargetedReply do
      use Accord.Protocol, tla: :off

      initial :idle

      state :idle do
        on {:checkout, worker :: atom()} do
          branch {:job, pos_integer()}, goto: :working
          # :empty now leads elsewhere.
          branch :empty, goto: :working
        end

        on :stop, reply: :stopped, goto: :stopped
      end

      state :working do
        on {:ack, token :: pos_integer()}, reply: :done, goto: :idle
        event {:lease_expired, token :: pos_integer()}, goto: :idle
      end

      state :stopped, terminal: true
    end

    test "a reply leading to a different state is C006" do
      result = Compat.check(V1, RetargetedReply)

      refute result.compatible?
      assert Enum.any?(result.errors, &(&1.code == "C006"))
    end

    defmodule NewEvent do
      use Accord.Protocol, tla: :off

      initial :idle

      state :idle do
        on {:checkout, worker :: atom()} do
          branch {:job, pos_integer()}, goto: :working
          branch :empty, goto: :idle
        end

        on :stop, reply: :stopped, goto: :stopped
      end

      state :working do
        on {:ack, token :: pos_integer()}, reply: :done, goto: :idle
        event {:lease_expired, token :: pos_integer()}, goto: :idle
        # Old clients do not handle this push.
        event :rebalance, goto: :idle
      end

      state :stopped, terminal: true
    end

    test "a new server push old clients do not handle is C007" do
      result = Compat.check(V1, NewEvent)

      refute result.compatible?
      assert Enum.any?(result.errors, &(&1.code == "C007" and &1.message =~ ":rebalance"))
    end

    defmodule AddedTimeout do
      use Accord.Protocol, tla: :off

      initial :idle

      state :idle do
        on {:checkout, worker :: atom()} do
          branch {:job, pos_integer()}, goto: :working
          branch :empty, goto: :idle
        end

        on :stop, reply: :stopped, goto: :stopped
      end

      state :working do
        state_timeout 5_000, goto: :idle

        on {:ack, token :: pos_integer()}, reply: :done, goto: :idle
        event {:lease_expired, token :: pos_integer()}, goto: :idle
      end

      state :stopped, terminal: true
    end

    test "changed autonomous movement is C009" do
      result = Compat.check(V1, AddedTimeout)

      refute result.compatible?
      assert Enum.any?(result.errors, &(&1.code == "C009"))
    end

    defmodule AddedGuard do
      use Accord.Protocol, tla: :off

      initial :idle

      track :fence, :non_neg_integer, default: 0

      state :idle do
        on {:checkout, worker :: atom()} do
          guard fn {:checkout, _w}, tracks -> tracks.fence < 100 end
          branch {:job, pos_integer()}, goto: :working
          branch :empty, goto: :idle
        end

        on :stop, reply: :stopped, goto: :stopped
      end

      state :working do
        on {:ack, token :: pos_integer()}, reply: :done, goto: :idle
        event {:lease_expired, token :: pos_integer()}, goto: :idle
      end

      state :stopped, terminal: true
    end

    test "an added guard is an advisory C010 warning, not an error" do
      result = Compat.check(V1, AddedGuard)

      assert result.compatible?
      assert Enum.any?(result.warnings, &(&1.code == "C010"))
    end
  end

  # Reply branches whose types overlap resolve by declaration order, so a
  # static first-supertype comparison is unsound — these lock the
  # order/value-aware behavior (finding C3).
  describe "overlapping reply branches" do
    defmodule OverlapV1 do
      use Accord.Protocol, tla: :off

      initial :idle

      state :idle do
        on :poll do
          branch {:ok, pos_integer()}, goto: :fast
          branch {:ok, integer()}, goto: :slow
        end

        on :stop, reply: :stopped, goto: :done
      end

      state :fast, do: on(:f, reply: :ok, goto: :idle)
      state :slow, do: on(:s, reply: :ok, goto: :idle)
      state :done, terminal: true
    end

    test "identical overlapping branches stay compatible" do
      result = Compat.check(OverlapV1, OverlapV1)

      assert result.compatible?
      assert result.errors == []
    end

    defmodule Reordered do
      use Accord.Protocol, tla: :off

      initial :idle

      state :idle do
        # Same branch set, reversed: {:ok, 5} first-matches integer → :slow
        # here, but pos_integer → :fast under OverlapV1.
        on :poll do
          branch {:ok, integer()}, goto: :slow
          branch {:ok, pos_integer()}, goto: :fast
        end

        on :stop, reply: :stopped, goto: :done
      end

      state :fast, do: on(:f, reply: :ok, goto: :idle)
      state :slow, do: on(:s, reply: :ok, goto: :idle)
      state :done, terminal: true
    end

    test "reordering overlapping branches is a C006 desync" do
      result = Compat.check(OverlapV1, Reordered)

      refute result.compatible?
      assert Enum.any?(result.errors, &(&1.code == "C006"))
    end

    defmodule NonNegOld do
      use Accord.Protocol, tla: :off

      initial :idle

      state :idle do
        on :poll do
          branch {:ok, non_neg_integer()}, goto: :a
          branch {:ok, integer()}, goto: :b
        end

        on :stop, reply: :stopped, goto: :done
      end

      state :a, do: on(:x, reply: :ok, goto: :idle)
      state :b, do: on(:y, reply: :ok, goto: :idle)
      state :done, terminal: true
    end

    defmodule PosNew do
      use Accord.Protocol, tla: :off

      initial :idle

      state :idle do
        # Narrowed the first branch non_neg → pos: {:ok, 0} now routes to
        # :b, but old clients route it to :a.
        on :poll do
          branch {:ok, pos_integer()}, goto: :a
          branch {:ok, integer()}, goto: :b
        end

        on :stop, reply: :stopped, goto: :done
      end

      state :a, do: on(:x, reply: :ok, goto: :idle)
      state :b, do: on(:y, reply: :ok, goto: :idle)
      state :done, terminal: true
    end

    test "narrowing an overlapping branch is a C006 desync" do
      result = Compat.check(NonNegOld, PosNew)

      refute result.compatible?
      assert Enum.any?(result.errors, &(&1.code == "C006"))
    end
  end

  # Track evolution feeds the where: refinements that route replies, so
  # update and default changes are advisories, not silent passes (C3).
  describe "track evolution" do
    defmodule FenceV1 do
      use Accord.Protocol, tla: :off

      initial :idle

      track :fence, :non_neg_integer, default: 0

      state :idle do
        on :checkout do
          branch {:job, pos_integer()}, goto: :working
          branch :empty, goto: :idle

          update fn _m, reply, tracks ->
            case reply do
              {:job, token} -> %{tracks | fence: token}
              :empty -> tracks
            end
          end
        end

        on :stop, reply: :stopped, goto: :done
      end

      state :working, do: on(:ack, reply: :done, goto: :idle)
      state :done, terminal: true
    end

    defmodule FenceNoWrite do
      use Accord.Protocol, tla: :off

      initial :idle

      track :fence, :non_neg_integer, default: 0

      state :idle do
        on :checkout do
          branch {:job, pos_integer()}, goto: :working
          branch :empty, goto: :idle

          # Dropped the fence write — the fencing idiom silently broken.
          update fn _m, _reply, tracks -> tracks end
        end

        on :stop, reply: :stopped, goto: :done
      end

      state :working, do: on(:ack, reply: :done, goto: :idle)
      state :done, terminal: true
    end

    test "a changed update is an advisory C010, not a silent pass" do
      result = Compat.check(FenceV1, FenceNoWrite)

      assert result.compatible?
      assert Enum.any?(result.warnings, &(&1.code == "C010" and &1.message =~ "update"))
    end

    defmodule FenceDefault5 do
      use Accord.Protocol, tla: :off

      initial :idle

      track :fence, :non_neg_integer, default: 5

      state :idle do
        on :checkout do
          branch {:job, pos_integer()}, goto: :working
          branch :empty, goto: :idle

          update fn _m, reply, tracks ->
            case reply do
              {:job, token} -> %{tracks | fence: token}
              :empty -> tracks
            end
          end
        end

        on :stop, reply: :stopped, goto: :done
      end

      state :working, do: on(:ack, reply: :done, goto: :idle)
      state :done, terminal: true
    end

    test "a changed track default is an advisory C010" do
      result = Compat.check(FenceV1, FenceDefault5)

      assert result.compatible?
      assert Enum.any?(result.warnings, &(&1.code == "C010" and &1.message =~ "default"))
    end

    test "adding a disjoint reply branch does not misfire a constraint C010" do
      # The added branch is a C005 (new reply old clients cannot handle),
      # never a spurious 'constraints changed' advisory.
      v2 = FenceV1

      defmodule FenceBackoff do
        use Accord.Protocol, tla: :off

        initial :idle

        track :fence, :non_neg_integer, default: 0

        state :idle do
          on :checkout do
            branch {:job, pos_integer()}, goto: :working
            branch :empty, goto: :idle
            branch :backoff, goto: :idle

            update fn _m, reply, tracks ->
              case reply do
                {:job, token} -> %{tracks | fence: token}
                :empty -> tracks
                :backoff -> tracks
              end
            end
          end

          on :stop, reply: :stopped, goto: :done
        end

        state :working, do: on(:ack, reply: :done, goto: :idle)
        state :done, terminal: true
      end

      result = Compat.check(v2, FenceBackoff)

      assert Enum.any?(result.errors, &(&1.code == "C005"))
      refute Enum.any?(result.warnings, &(&1.code == "C010" and &1.message =~ "constraint"))
    end
  end

  describe "snapshots" do
    @describetag :tmp_dir

    test "save/load round-trips the IR", %{tmp_dir: tmp_dir} do
      path = Path.join(tmp_dir, "v1.ir")
      :ok = Snapshot.save(V1, path)

      assert {:ok, ir} = Snapshot.load(path)
      assert ir.initial == :idle
      assert Map.has_key?(ir.states, :working)

      # A snapshot checks like the live module.
      assert Compat.check(ir, V2Compatible).compatible?
      refute Compat.check(V2Compatible, ir).compatible?
    end

    test "load rejects non-snapshots", %{tmp_dir: tmp_dir} do
      path = Path.join(tmp_dir, "garbage.ir")
      File.write!(path, "not a snapshot")

      assert {:error, :not_a_snapshot} = Snapshot.load(path)
    end
  end
end
