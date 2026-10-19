defmodule Accord.TLA.Checker.ParserTest do
  use ExUnit.Case, async: true

  alias Accord.TLA.Checker.Parser

  defp e(src), do: src |> Parser.parse_expression() |> strip()

  # Drops positions, so the tests can compare shapes.
  defp strip({:name, n, _}), do: {:name, n}
  defp strip({:app, op, args, _}), do: {:app, op, strip(args)}
  defp strip({:inst, path, n, args, _}), do: {:inst, strip(path), n, strip(args)}

  defp strip(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.map(&strip/1) |> List.to_tuple()

  defp strip(l) when is_list(l), do: Enum.map(l, &strip/1)
  defp strip(other), do: other

  defp n(x), do: {:name, x}
  defp app(op, args), do: {:app, op, args}

  describe "precedence" do
    test "arithmetic and comparison" do
      assert e("a + b * c = d") ==
               app("=", [app("+", [n("a"), app("*", [n("b"), n("c")])]), n("d")])

      assert e("1..n+1") == app("..", [{:num, 1}, app("+", [n("n"), {:num, 1}])])
      assert e("-x * y") == app("-.", [app("*", [n("x"), n("y")])])
      assert e("a - b - c") == app("-", [app("-", [n("a"), n("b")]), n("c")])
    end

    test "logic" do
      assert e("(a /\\ b) \\/ c") == {:or, [{:and, [n("a"), n("b")]}, n("c")]}
      assert e("~a /\\ b") == {:and, [{:not, n("a")}, n("b")]}
      assert e("a => (b => c)") == {:implies, n("a"), {:implies, n("b"), n("c")}}
      assert e("a => b /\\ c") == {:implies, n("a"), {:and, [n("b"), n("c")]}}
      assert e("x \\in S \\cup T") == app("\\in", [n("x"), app("\\cup", [n("S"), n("T")])])
    end

    test "n-ary cartesian product" do
      assert e("A \\X B \\X C") == {:times, [n("A"), n("B"), n("C")]}
      assert e("(A \\X B) \\X C") == {:times, [{:times, [n("A"), n("B")]}, n("C")]}
    end
  end

  describe "junction lists" do
    test "items end at the column of the bullet" do
      src = """
      /\\ x = 1
      /\\ \\/ y = 2
         \\/ y = 3
      /\\ z
      """

      assert e(src) ==
               {:and,
                [
                  app("=", [n("x"), {:num, 1}]),
                  {:or, [app("=", [n("y"), {:num, 2}]), app("=", [n("y"), {:num, 3}])]},
                  n("z")
                ]}
    end

    test "parentheses suspend the columns" do
      src = """
      /\\ x = (1 +
      2)
      /\\ y
      """

      assert e(src) == {:and, [app("=", [n("x"), app("+", [{:num, 1}, {:num, 2}])]), n("y")]}
    end

    test "an infix /\\\\ to the right of the column continues the item" do
      src = """
      /\\ a
           /\\ b
      /\\ c
      """

      assert e(src) == {:and, [{:and, [n("a"), n("b")]}, n("c")]}
    end
  end

  describe "forms" do
    test "sets" do
      assert e("{}") == {:set, []}
      assert e("{1, 2}") == {:set, [{:num, 1}, {:num, 2}]}

      assert e("{x \\in S : x > 1}") ==
               {:set_filter, {"x", n("S")}, app(">", [n("x"), {:num, 1}])}

      assert e("{x + 1 : x \\in S}") == {:set_map, app("+", [n("x"), {:num, 1}]), [{"x", n("S")}]}
    end

    test "functions and records" do
      assert e("[x \\in S |-> x]") == {:func, [{"x", n("S")}], n("x")}
      assert e("[x, y \\in S |-> x]") == {:func, [{"x", n("S")}, {"y", n("S")}], n("x")}
      assert e("[a |-> 1, b |-> 2]") == {:record, [{"a", {:num, 1}}, {"b", {:num, 2}}]}
      assert e("[a : S]") == {:record_set, [{"a", n("S")}]}
      assert e("[S -> T]") == {:fun_set, n("S"), n("T")}

      assert e("[f EXCEPT ![1] = @ + 1, !.a = 2]") ==
               {:except, n("f"),
                [
                  {[{:index, [{:num, 1}]}], app("+", [{:at}, {:num, 1}])},
                  {[{:field, "a"}], {:num, 2}}
                ]}

      assert e("f[x][y].z") == {:dot, {:apply, {:apply, n("f"), [n("x")]}, [n("y")]}, "z"}
    end

    test "quantifiers and CHOOSE" do
      assert e("\\A x, y \\in S, z \\in T : P") ==
               {:forall, [{"x", n("S")}, {"y", n("S")}, {"z", n("T")}], n("P")}

      assert e("\\E <<a, b>> \\in S : P") == {:exists, [{{:tuple, ["a", "b"]}, n("S")}], n("P")}
      assert e("CHOOSE x \\in S : P") == {:choose, {"x", n("S")}, n("P")}
    end

    test "IF, CASE, LET" do
      assert e("IF a THEN b ELSE c") == {:if, n("a"), n("b"), n("c")}

      assert e("CASE a -> 1 [] b -> 2 [] OTHER -> 3") ==
               {:case, [{n("a"), {:num, 1}}, {n("b"), {:num, 2}}], {:num, 3}}

      assert {:let, [%{name: "y"}], {:app, "+", [{:name, "y"}, {:num, 1}]}} =
               e("LET y == 2 IN y + 1")
    end

    test "temporal operators" do
      assert e("[][Next]_vars") == {:always, {:box_action, n("Next"), n("vars")}}
      assert e("WF_vars(A)") == {:wf, n("vars"), n("A")}
      assert e("SF_<<x, y>>(A)") == {:sf, {:tuple, [n("x"), n("y")]}, n("A")}
      assert e("P ~> Q") == {:leadsto, n("P"), n("Q")}
      assert e("[]<>P") == {:always, {:eventually, n("P")}}
    end

    test "primes, UNCHANGED, and instances" do
      assert e("x' = x + 1") == app("=", [{:prime, n("x")}, app("+", [n("x"), {:num, 1}])])
      assert e("UNCHANGED <<x, y>>") == {:unchanged, {:tuple, [n("x"), n("y")]}}
      assert e("M!Next") == {:inst, [{"M", []}], "Next", []}
      assert e("Inv!2") == {:inst, [{"Inv", []}], 2, []}
    end
  end

  test "a module with definitions, constants, variables, and a proof" do
    src = """
    text before the module
    ---- MODULE M ----
    EXTENDS Naturals
    CONSTANTS N, F(_)
    VARIABLES x
    Init == x = 0
    Inc(d) == x' = x + d
    f[i \\in 1..N] == IF i = 1 THEN 1 ELSE i * f[i - 1]
    a ++ b == a + b
    THEOREM T == ASSUME NEW y \\in Nat
                 PROVE y >= 0
    <1>1. QED BY DEF Init
    ASSUME N > 0
    Next == Inc(1)
    ====
    """

    mod = Parser.parse_module(src)
    assert mod.name == "M"
    assert mod.extends == ["Naturals"]
    assert mod.constants == [{"N", 0}, {"F", 1}]
    assert mod.variables == ["x"]
    assert Enum.map(mod.units, & &1.name) == ["Init", "Inc", "f", "++", "Next"]
    assert [{_, _, _}] = mod.assumes
  end

  # The results of SANY (TLC 2026.10.15) for each expression: true if
  # SANY parses it, false for a precedence conflict.
  @sany_cases [
    {"TRUE => FALSE => TRUE", false},
    {"{1} \\cup {2} \\cap {3} = {1}", false},
    {"1 < 2 < 3", false},
    {"1 = 1 = TRUE", false},
    {"2^3^2 = 64", false},
    {"1 .. 2 .. 3 = {}", false},
    {"1 \\div 2 * 3 = 0", false},
    {"7 \\div -2", false},
    {"a * -b", false},
    {"a + -b", true},
    {"a - -b", true},
    {"a ^ -b", false},
    {"- - a", true},
    {"~ ~ P", true},
    {"~ -a", true},
    {"[]x = 1", false},
    {"<>x = 1", false},
    {"ENABLED x' = x", false},
    {"UNCHANGED x /\\ P", true},
    {"UNCHANGED <<x>> = TRUE", false},
    {"[]P /\\ Q", true},
    {"[]<>P", true},
    {"~ [] P", true},
    {"SUBSET a \\cup b", true},
    {"SUBSET a \\X b", false},
    {"SUBSET a + b", false},
    {"-a * b", true},
    {"-a'", true},
    {"[]x'", false},
    {"a + b * c - d", true},
    {"a * b / c", false},
    {"a / b / c", false},
    {"a \\o b \\o c", true},
    {"(1 :> 2) @@ (2 :> 3) @@ (3 :> 4)", true},
    {"a :> b :> c", false},
    {"a \\in b \\in c", false},
    {"a | b || c", false},
    {"a \\cdot b \\cdot c", true},
    {"a \\cdot b = c", false},
    {"P => Q /\\ R", true},
    {"P \\/ Q /\\ R", false},
    {"P <=> Q <=> R", false},
    {"P ~> Q ~> R", false},
    {"P => Q <=> R", true},
    {"a \\X b \\X c", true},
    {"a \\X b \\cup c", true},
    {"a ++ b + c", false},
    {"a + b .. c", true},
    {"a \\ b \\cup c", false},
    {"~ a = b", true},
    {"-r.f", true},
    {"a ** b * c", false}
  ]

  describe "precedence conflicts (as SANY)" do
    for {src, ok} <- @sany_cases do
      test src do
        result =
          try do
            Parser.parse_expression(unquote(src))
            true
          rescue
            Parser.Error -> false
          end

        assert result == unquote(ok)
      end
    end

    test "the tree without a conflict" do
      assert e("a + b * c - d") ==
               app("+", [n("a"), app("-", [app("*", [n("b"), n("c")]), n("d")])])

      assert e("~ a = b") == {:not, app("=", [n("a"), n("b")])}
      assert e("SUBSET a \\cup b") == app("\\cup", [app("SUBSET", [n("a")]), n("b")])
    end
  end
end
