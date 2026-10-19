defmodule Accord.TLA.Checker.SemanticTest do
  use ExUnit.Case, async: true

  alias Accord.TLA.Checker
  alias Accord.TLA.Checker.{Parser, Semantic}

  # The codes of the errors and warnings of a module text.
  defp codes(src) do
    src
    |> Parser.parse_module()
    |> Semantic.check()
    |> Enum.map(&{&1.level, &1.code})
  end

  defp mod(body), do: "---- MODULE M ----\n#{body}\n===="

  test "a correct module has no errors" do
    assert codes(mod("EXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1")) == []
  end

  describe "names" do
    test "an unknown operator" do
      assert {:error, 4200} in codes(mod("Op == Foo"))
    end

    test "an unknown compound name (SANY's TestSubexpressionSelectors)" do
      msg = fn body ->
        [e | _] = body |> mod() |> Parser.parse_module() |> Semantic.check()
        {e.code, e.message, e.pos}
      end

      assert msg.("use == module!op") == {4200, "Unknown operator: `module!op'.", {2, 8}}
      assert msg.("tree_nav == op!<<!>>") == {4200, "Unknown operator: `op'.", {2, 13}}

      assert msg.("tree_nav == op(a, b)!<<!>>!3!(x, y)!:!@") ==
               {4200, "Unknown operator: `op'.", {2, 13}}
    end

    test "a symbol defined two times" do
      assert {:error, 4201} in codes(mod("A == 1\nA == 2"))
    end

    test "a wrong number of arguments" do
      assert {:error, 4204} in codes(mod("F(a) == a\nG == F(1, 2)"))
    end
  end

  describe "levels" do
    test "a primed expression is primed again" do
      assert {:error, 4205} in codes(mod("VARIABLE v\nop == v''"))
    end

    test "an assumption is not constant" do
      assert {:error, 4206} in codes(mod("VARIABLE v\nASSUME v"))
    end

    test "[] of an action that is not [A]_v" do
      assert {:error, 4310} in codes(mod("VARIABLE v\nop == [](v')"))
    end

    test "an action and a temporal formula in a conjunction" do
      assert {:error, 4313} in codes(mod("VARIABLE v\nop == v' /\\ []v"))
    end

    test "a variable substituted with an action" do
      src = """
      ---- MODULE M ----
      ---- MODULE Inner ----
      VARIABLE v1
      ====
      VARIABLE v2
      INSTANCE Inner WITH v1 <- v2'
      ====
      """

      assert {:error, 4245} in codes(src)
    end

    test "a recursive operator primes its argument" do
      assert {:error, 4290} in codes(mod("RECURSIVE op(_)\nop(x) == x'"))
    end

    test "a subexpression has its own level" do
      assert codes(mod("Def == [12]_(23)\nASSUME Def!1 = 12")) == []
    end
  end

  # The cases of SANY's TestLevelChecking: `op == <expression>` in a
  # module with CONSTANT c and VARIABLE x; true if the levels are
  # correct.
  @level_cases [
    {"\\neg c", true},
    {"c.foo", true},
    {"([]c).foo", false},
    {"[]c", true},
    {"□c", true},
    {"<>c", true},
    {"◇c", true},
    {"[]x", true},
    {"□x", true},
    {"<>x", true},
    {"◇x", true},
    {"[](x')", false},
    {"□(x')", false},
    {"<>(x')", false},
    {"◇(x')", false},
    {"[][c]_x", true},
    {"□[c]_x", true},
    {"[]<<c>>_x", false},
    {"□⟨c⟩_x", false},
    {"<><<c>>_x", true},
    {"◇⟨c⟩_x", true},
    {"<>[c]_x", false},
    {"◇[c]_x", false},
    {"c ~> c", true},
    {"x' ~> c", false},
    {"c ~> x'", false},
    {"c ↝ c", true},
    {"x' ↝ c", false},
    {"c ↝ x'", false},
    {"c -+-> c", true},
    {"x' -+-> c", false},
    {"c -+-> x'", false},
    {"c ⇸ c", true},
    {"x' ⇸ c", false},
    {"c ⇸ x'", false},
    {"c /\\ c", true},
    {"c ∧ c", true},
    {"x /\\ c", true},
    {"x ∧ c", true},
    {"[]c /\\ c", true},
    {"□c ∧ c", true},
    {"c /\\ x'", true},
    {"c ∧ x'", true},
    {"[]c /\\ x'", false},
    {"□c ∧ x'", false},
    {"∀ v ∈ c  : v", true},
    {"∃ v ∈ x  : v", true},
    {"∀ v ∈ x' : v", true},
    {"∃ v ∈ x  : □v", true},
    {"∀ v ∈ x' : □v", false},
    {"∃ v ∈ □x : v", false}
  ]

  describe "the level cases of SANY" do
    for {expr, ok} <- @level_cases do
      test "#{expr}" do
        errs =
          codes("---- MODULE Test ----\nCONSTANT c\nVARIABLE x\nop == #{unquote(expr)}\n====")

        assert Enum.all?(errs, &(elem(&1, 0) == :warning)) == unquote(ok), inspect(errs)
      end
    end
  end

  describe "warnings" do
    test "a definition of an INSTANCE is ignored" do
      assert codes(mod("Nat == TRUE\nINSTANCE Naturals")) == [{:warning, 4801}]
    end
  end

  test "the checker stops on a semantic error" do
    dir = Path.join(System.tmp_dir!(), "accord_semantic_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "M.tla")
    File.write!(path, mod("VARIABLE x\nInit == x = Foo\nNext == x' = x"))
    File.write!(Path.join(dir, "M.cfg"), "INIT Init\nNEXT Next\n")

    try do
      result = Checker.run(path)
      assert result.status == :error
      assert result.kind == :parse
      assert result.message =~ "Unknown operator"
    after
      File.rm_rf!(dir)
    end
  end
end
