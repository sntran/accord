defmodule Accord.TLA.CheckerTest do
  use ExUnit.Case, async: true

  alias Accord.TLA.Checker

  @moduletag :tmp_dir

  # Writes a module and its config, and runs the checker.
  defp check(dir, name, tla, cfg, opts \\ []) do
    path = Path.join(dir, name <> ".tla")
    File.write!(path, "---- MODULE #{name} ----\n" <> tla <> "\n====\n")
    File.write!(Path.join(dir, name <> ".cfg"), cfg)
    Checker.run(path, opts)
  end

  @counter """
  EXTENDS Naturals
  VARIABLE x
  Init == x = 0
  Next == x < 3 /\\ x' = x + 1
  """

  describe "safety" do
    test "a model with no error", %{tmp_dir: dir} do
      r = check(dir, "Ok", @counter, "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n")
      assert r.status == :ok
      assert r.stats.distinct == 4
      assert r.stats.generated == 4
      assert r.stats.depth == 4
    end

    test "deadlock", %{tmp_dir: dir} do
      r = check(dir, "Dead", @counter, "INIT Init\nNEXT Next\n")
      assert r.kind == :deadlock
      assert length(r.trace) == 4
    end

    test "an invariant violation gives the shortest trace", %{tmp_dir: dir} do
      tla = @counter <> "Inv == x # 2\n"
      r = check(dir, "Inv", tla, "INIT Init\nNEXT Next\nINVARIANT Inv\n")
      assert r.kind == :invariant
      assert r.property == "Inv"
      assert Enum.map(r.trace, &elem(&1.state, 0)) == [0, 1, 2]

      assert {:error, %{kind: :invariant, trace: [_, %{action: "Next"}, _]},
              %{distinct_states: 3}} = Checker.to_tlc(r)
    end

    test "an action property", %{tmp_dir: dir} do
      tla = @counter <> "Grow == [][x' = x + 2]_x\n"
      r = check(dir, "Act", tla, "INIT Init\nNEXT Next\nPROPERTY Grow\nCHECK_DEADLOCK FALSE\n")
      assert r.kind == :action_property
    end

    test "a state constraint", %{tmp_dir: dir} do
      tla = @counter <> "Small == x < 2\n"
      r = check(dir, "Con", tla, "INIT Init\nNEXT Next\nCONSTRAINT Small\nCHECK_DEADLOCK FALSE\n")
      # The state x = 2 is not in the constraint: TLC does not count it.
      assert r.status == :ok
      assert r.stats.distinct == 2
      assert r.stats.generated == 3
    end

    test "a false assumption", %{tmp_dir: dir} do
      r = check(dir, "Asm", "EXTENDS Naturals\nCONSTANT N\nASSUME N > 3\n", "CONSTANT N = 2\n")
      assert r.kind == :assumption
    end

    test "a state that the action does not complete", %{tmp_dir: dir} do
      tla = "VARIABLES x, y\nInit == x = 0 /\\ y = 0\nNext == x' = 1\n"
      r = check(dir, "Partial", tla, "INIT Init\nNEXT Next\n")
      assert r.kind == :spec_eval
      assert r.message =~ "y"
    end
  end

  describe "generation counts as TLC does" do
    test "disjunctions inside a guard give more steps", %{tmp_dir: dir} do
      # At x = 0 the guard has two true disjuncts: TLC generates the step
      # twice (and once at x = 1). The numbers are those of TLC.
      tla = "EXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == (x = 0 \\/ x < 5) /\\ x' = 1\n"
      r = check(dir, "Twice", tla, "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n")
      assert r.stats.generated == 1 + 2 + 1
    end

    test "once all variables have a value, the rest is a condition", %{tmp_dir: dir} do
      tla = "EXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = 1 /\\ (x = 0 \\/ x < 5)\n"
      r = check(dir, "Once", tla, "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n")
      assert r.stats.generated == 1 + 1 + 1
    end
  end

  describe "symmetry" do
    test "the permutations of a set and of their compositions", %{tmp_dir: dir} do
      tla = """
      EXTENDS TLC
      CONSTANTS A, B
      VARIABLES a, b
      Init == a \\in A /\\ b \\in B
      Next == UNCHANGED <<a, b>>
      Sym == Permutations(A) \\cup Permutations(B)
      """

      cfg = "CONSTANTS A = {a1, a2}\n B = {b1, b2}\nINIT Init\nNEXT Next\nSYMMETRY Sym\n"
      assert check(dir, "Sym", tla, cfg).stats.distinct == 1
    end
  end

  describe "liveness" do
    @clock """
    EXTENDS Naturals
    VARIABLE x
    Init == x = 0
    Next == x' = (x + 1) % 3
    """

    test "a leads-to property with weak fairness", %{tmp_dir: dir} do
      tla = @clock <> "Spec == Init /\\ [][Next]_x /\\ WF_x(Next)\nLive == (x = 1) ~> (x = 2)\n"
      assert check(dir, "Fair", tla, "SPECIFICATION Spec\nPROPERTY Live\n").status == :ok
    end

    test "without fairness, the behavior can stutter", %{tmp_dir: dir} do
      tla = @clock <> "Spec == Init /\\ [][Next]_x\nLive == <>(x = 2)\n"
      r = check(dir, "Unfair", tla, "SPECIFICATION Spec\nPROPERTY Live\n")
      assert r.kind == :temporal
      assert r.loop == :stuttering
    end

    test "a cycle that never reaches the goal", %{tmp_dir: dir} do
      tla = @clock <> "Spec == Init /\\ [][Next]_x /\\ WF_x(Next)\nLive == <>[](x = 0)\n"
      r = check(dir, "Cycle", tla, "SPECIFICATION Spec\nPROPERTY Live\n")
      assert r.kind == :temporal
      assert {:back_to, _, _} = r.loop
    end

    test "a quantified property and an implication with fairness", %{tmp_dir: dir} do
      tla =
        @clock <>
          "Spec == Init /\\ [][Next]_x\nLive == WF_x(Next) => \\A n \\in 0..2 : []<>(x = n)\n"

      assert check(dir, "Quant", tla, "SPECIFICATION Spec\nPROPERTY Live\n").status == :ok
    end
  end

  describe "modules" do
    test "an instance inside LET", %{tmp_dir: dir} do
      File.write!(
        Path.join(dir, "Inner.tla"),
        "---- MODULE Inner ----\nEXTENDS Naturals\nCONSTANT K\nDouble == K + K\n====\n"
      )

      tla = """
      EXTENDS Naturals
      VARIABLE x
      Init == x = 0
      Next == LET I == INSTANCE Inner WITH K <- x IN x < 4 /\\ x' = I!Double + 1
      """

      r = check(dir, "Outer", tla, "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n")
      assert r.status == :ok
      # 0 -> 1 -> 3 -> 7
      assert r.stats.distinct == 4
    end

    test "a second module in the same file", %{tmp_dir: dir} do
      path = Path.join(dir, "Two.tla")

      File.write!(path, """
      ---- MODULE Two ----
      EXTENDS Helper
      VARIABLE x
      Init == x = One
      Next == UNCHANGED x
      ====
      ---- MODULE Helper ----
      One == 1
      ====
      """)

      File.write!(Path.join(dir, "Two.cfg"), "INIT Init\nNEXT Next\n")
      assert Checker.run(path).status == :ok
    end
  end
end
