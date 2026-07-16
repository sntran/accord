defmodule Accord.TLA.FilesTest do
  @moduledoc """
  Artifact naming and collision detection.

  The TLA+ MODULE name is the concatenated module path, which is not
  injective and lands in a flat, case-insensitive-on-macOS directory.
  `name_collisions/1` is the guard that keeps a collision from silently
  verifying the wrong spec (finding H1).
  """
  use ExUnit.Case, async: true

  alias Accord.TLA.Files

  describe "tla_module_name/1" do
    test "concatenates the full module path" do
      assert Files.tla_module_name(Lock.Protocol) == "LockProtocol"

      assert Files.tla_module_name(Accord.Examples.JobQueue.Protocol) ==
               "AccordExamplesJobQueueProtocol"
    end
  end

  describe "name_collisions/1" do
    test "no collision among distinct concatenations" do
      assert Files.name_collisions([Lock.Protocol, Queue.Protocol]) == []
    end

    test "detects a module-boundary collision (A.BC vs AB.C)" do
      assert [{"ABC", mods}] = Files.name_collisions([A.BC, AB.C])
      assert mods == [A.BC, AB.C]
    end

    test "detects a case-only collision a case-insensitive filesystem cannot tell apart" do
      # Foo.Bar → "FooBar", Foo.BAR → "FooBAR": distinct TLA identifiers,
      # but the same file on macOS/Windows.
      assert [{_name, mods}] = Files.name_collisions([Foo.Bar, Foo.BAR])
      assert mods == [Foo.BAR, Foo.Bar]
    end

    test "reports each colliding group once, deduping repeats" do
      assert Files.name_collisions([A.BC, AB.C, A.BC]) == [{"ABC", [A.BC, AB.C]}]
    end

    test "no collision for a single module" do
      assert Files.name_collisions([Lock.Protocol]) == []
    end

    test "groups three-way collisions together" do
      # A.BC, AB.C, and the single-atom module all fold to "abc".
      assert [{_name, mods}] = Files.name_collisions([A.BC, AB.C, ABC])
      assert length(mods) == 3
    end
  end
end
