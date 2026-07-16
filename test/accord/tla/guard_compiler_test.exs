defmodule Accord.TLA.GuardCompilerTest do
  use ExUnit.Case, async: true

  alias Accord.TLA.GuardCompiler

  describe "literals" do
    test "integer" do
      assert {:ok, "42", _} = GuardCompiler.compile(42)
    end

    test "negative integer" do
      assert {:ok, "-1", _} = GuardCompiler.compile(-1)
    end

    test "boolean true" do
      assert {:ok, "TRUE", _} = GuardCompiler.compile(true)
    end

    test "boolean false" do
      assert {:ok, "FALSE", _} = GuardCompiler.compile(false)
    end

    test "nil" do
      assert {:ok, "NULL", _} = GuardCompiler.compile(nil)
    end

    test "string" do
      assert {:ok, ~s("hello"), _} = GuardCompiler.compile("hello")
    end

    test "atom renders as a TLA+ string and is recorded as an atom literal" do
      # Not `inspect/1` (`:fast` is not valid TLA+); matches how explicit
      # domains and defaults render atoms. The literal is reported so the
      # caller can require an enumerated domain (E047).
      assert {:ok, ~s("fast"), idents} = GuardCompiler.compile(:fast)
      assert {"fast", :atom_literal} in idents
    end
  end

  describe "variables" do
    test "bare variable" do
      ast = quote(do: x)
      assert {:ok, "x", _} = GuardCompiler.compile(ast)
    end

    test "variable with binding" do
      ast = quote(do: token)
      assert {:ok, "msg_token", _} = GuardCompiler.compile(ast, %{token: "msg_token"})
    end

    test "unbound variable uses atom name" do
      ast = quote(do: counter)
      assert {:ok, "counter", _} = GuardCompiler.compile(ast)
    end
  end

  describe "dot access" do
    test "tracks.field compiles to field name" do
      ast = quote(do: tracks.fence_token)
      assert {:ok, "fence_token", _} = GuardCompiler.compile(ast)
    end

    test "any_var.field compiles to field name" do
      ast = quote(do: state.balance)
      assert {:ok, "balance", _} = GuardCompiler.compile(ast)
    end
  end

  describe "comparison operators" do
    test "greater than" do
      ast = quote(do: x > 0)
      assert {:ok, "x > 0", _} = GuardCompiler.compile(ast)
    end

    test "greater than or equal" do
      ast = quote(do: x >= 0)
      assert {:ok, "x >= 0", _} = GuardCompiler.compile(ast)
    end

    test "less than" do
      ast = quote(do: x < 10)
      assert {:ok, "x < 10", _} = GuardCompiler.compile(ast)
    end

    test "less than or equal" do
      ast = quote(do: x <= 10)
      assert {:ok, "x =< 10", _} = GuardCompiler.compile(ast)
    end

    test "equal" do
      ast = quote(do: x == y)
      assert {:ok, "x = y", _} = GuardCompiler.compile(ast)
    end

    test "not equal" do
      ast = quote(do: x != y)
      assert {:ok, "x /= y", _} = GuardCompiler.compile(ast)
    end
  end

  describe "arithmetic operators" do
    test "addition" do
      ast = quote(do: x + 1)
      assert {:ok, "(x + 1)", _} = GuardCompiler.compile(ast)
    end

    test "subtraction" do
      ast = quote(do: x - 1)
      assert {:ok, "(x - 1)", _} = GuardCompiler.compile(ast)
    end

    test "multiplication" do
      ast = quote(do: x * 2)
      assert {:ok, "(x * 2)", _} = GuardCompiler.compile(ast)
    end

    test "integer division" do
      ast = quote(do: div(x, 2))
      assert {:ok, "(x \\div 2)", _} = GuardCompiler.compile(ast)
    end

    test "remainder" do
      ast = quote(do: rem(x, 3))
      assert {:ok, "(x % 3)", _} = GuardCompiler.compile(ast)
    end
  end

  describe "boolean operators" do
    test "and" do
      ast = quote(do: x > 0 and y > 0)
      assert {:ok, "(x > 0 /\\ y > 0)", _} = GuardCompiler.compile(ast)
    end

    test "or" do
      ast = quote(do: x > 0 or y > 0)
      assert {:ok, "(x > 0 \\/ y > 0)", _} = GuardCompiler.compile(ast)
    end

    test "not" do
      ast = quote(do: not x)
      assert {:ok, "~x", _} = GuardCompiler.compile(ast)
    end
  end

  describe "built-in functions" do
    test "length" do
      ast = quote(do: length(items))
      assert {:ok, "Len(items)", _} = GuardCompiler.compile(ast)
    end

    test "is_integer" do
      ast = quote(do: is_integer(x))
      assert {:ok, "x \\in Int", _} = GuardCompiler.compile(ast)
    end

    test "is_boolean" do
      ast = quote(do: is_boolean(x))
      assert {:ok, "x \\in BOOLEAN", _} = GuardCompiler.compile(ast)
    end

    test "abs" do
      ast = quote(do: abs(x))
      assert {:ok, "IF x >= 0 THEN x ELSE -(x)", _} = GuardCompiler.compile(ast)
    end
  end

  describe "nested expressions" do
    test "comparison with arithmetic" do
      ast = quote(do: x + 1 > y - 2)
      assert {:ok, "(x + 1) > (y - 2)", _} = GuardCompiler.compile(ast)
    end

    test "boolean with comparisons" do
      ast = quote(do: x > 0 and x < 100)
      assert {:ok, "(x > 0 /\\ x < 100)", _} = GuardCompiler.compile(ast)
    end

    test "complex nested expression" do
      ast = quote(do: (x > 0 and y > 0) or z == 0)
      assert {:ok, "((x > 0 /\\ y > 0) \\/ z = 0)", _} = GuardCompiler.compile(ast)
    end

    test "dot access in comparison" do
      ast = quote(do: tracks.fence_token >= 0)
      assert {:ok, "fence_token >= 0", _} = GuardCompiler.compile(ast)
    end
  end

  describe "bindings" do
    test "resolves bound variables" do
      ast = quote(do: token > tracks.fence_token)
      bindings = %{token: "msg_token"}
      assert {:ok, "msg_token > fence_token", _} = GuardCompiler.compile(ast, bindings)
    end

    test "multiple bindings" do
      ast = quote(do: client_id == tracks.holder and token > tracks.fence_token)
      bindings = %{client_id: "msg_client_id", token: "msg_token"}

      assert {:ok, "(msg_client_id = holder /\\ msg_token > fence_token)", _} =
               GuardCompiler.compile(ast, bindings)
    end
  end

  describe "fn expressions" do
    test "extracts body from single-clause fn" do
      ast = quote(do: fn tracks -> tracks.counter >= 0 end)
      assert {:ok, "counter >= 0", _} = GuardCompiler.compile(ast)
    end

    test "fn with pattern match args" do
      ast =
        quote(
          do: fn {:bet, chips}, tracks ->
            chips <= tracks.balance
          end
        )

      bindings = %{chips: "msg_chips"}

      assert {:ok, "msg_chips =< balance", _} =
               GuardCompiler.compile(ast, bindings)
    end
  end

  describe "unsupported forms" do
    test "function call returns an error" do
      ast = quote(do: String.length(x))

      assert {:error, [%{message: message}]} = GuardCompiler.compile(ast)
      assert message =~ "expression not compilable to TLA+"
      assert message =~ "String.length(x)"
    end

    test "case expression returns an error" do
      ast =
        quote(
          do:
            case x do
              1 -> true
              _ -> false
            end
        )

      assert {:error, [%{message: message}]} = GuardCompiler.compile(ast)
      assert message =~ "expression not compilable to TLA+"
    end

    test "unsupported sub-expression in valid context returns an error" do
      ast = quote(do: some_func(x) > 0)

      assert {:error, [%{message: message}]} = GuardCompiler.compile(ast)
      assert message =~ "some_func(x)"
    end

    test "pipe operator returns an error" do
      ast = quote(do: x |> String.length())

      assert {:error, [%{message: _}]} = GuardCompiler.compile(ast)
    end

    test "every unsupported sub-expression is reported, not just the first" do
      ast = quote(do: some_func(x) > 0 and other_func(y) < 1)

      assert {:error, unsupported} = GuardCompiler.compile(ast)
      messages = Enum.map(unsupported, & &1.message)
      assert Enum.any?(messages, &(&1 =~ "some_func"))
      assert Enum.any?(messages, &(&1 =~ "other_func"))
    end

    test "bare reference to an action-property tracks value returns an error" do
      ast = quote(do: old != new)

      assert {:error, [_, _]} =
               GuardCompiler.compile(ast, %{old: :current, new: :primed})
    end
  end

  describe "emitted identifiers" do
    test "bound variables emit no identifiers" do
      ast = quote(do: token > 0)

      assert {:ok, _, []} = GuardCompiler.compile(ast, %{token: "msg_token"})
    end

    test "unbound bare variables are reported as :bare" do
      ast = quote(do: counter > 0)

      assert {:ok, _, [{"counter", :bare}]} = GuardCompiler.compile(ast)
    end

    test "field accesses are reported as :field" do
      ast = quote(do: tracks.fence_token > 0)

      assert {:ok, _, [{"fence_token", :field}]} = GuardCompiler.compile(ast)
    end

    test "primed field accesses report the base field name" do
      ast = quote(do: new.fence_token > old.fence_token)

      assert {:ok, _, idents} =
               GuardCompiler.compile(ast, %{old: :current, new: :primed})

      assert {"fence_token", :field} in idents
    end
  end

  describe "real-world guard patterns" do
    test "comparison with bound variable" do
      ast = quote(do: token > tracks.fence_token)
      bindings = %{token: "msg_token"}
      assert {:ok, "msg_token > fence_token", _} = GuardCompiler.compile(ast, bindings)
    end

    test "compound boolean with bindings" do
      ast = quote(do: client_id == tracks.holder and token == tracks.fence_token)
      bindings = %{client_id: "msg_client_id", token: "msg_token"}

      assert {:ok, "(msg_client_id = holder /\\ msg_token = fence_token)", _} =
               GuardCompiler.compile(ast, bindings)
    end

    test "blackjack guard: bet within balance" do
      ast = quote(do: chips <= tracks.balance)
      bindings = %{chips: "msg_chips"}
      assert {:ok, "msg_chips =< balance", _} = GuardCompiler.compile(ast, bindings)
    end

    test "pipeline guard: demand limit" do
      ast = quote(do: tracks.total_demanded + demand <= 1000)
      bindings = %{demand: "msg_demand"}

      assert {:ok, "(total_demanded + msg_demand) =< 1000", _} =
               GuardCompiler.compile(ast, bindings)
    end

    test "invariant: counter non-negative" do
      ast = quote(do: fn tracks -> tracks.counter >= 0 end)
      assert {:ok, "counter >= 0", _} = GuardCompiler.compile(ast)
    end

    test "action: monotonic value" do
      ast = quote(do: fn old, new -> new.value >= old.value end)
      # Note: 'old' and 'new' are just variable names, they'll resolve to TLA+ primed vars
      # in the BuildActions pass. Here we just verify the AST compiles.
      assert {:ok, "value >= value", _} = GuardCompiler.compile(ast)
    end
  end
end
