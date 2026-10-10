defmodule Accord.CrossCheck.TLAValueTest do
  use ExUnit.Case, async: true

  alias Accord.CrossCheck.TLAValue
  alias Accord.Explore.Model

  describe "parse/1" do
    test "scalars" do
      assert TLAValue.parse!("42") == 42
      assert TLAValue.parse!("-1") == -1
      assert TLAValue.parse!("TRUE") == true
      assert TLAValue.parse!("FALSE") == false
      assert TLAValue.parse!(~s("idle")) == {:str, "idle"}
      assert TLAValue.parse!(~s("a \\"b\\" c")) == {:str, ~s(a "b" c)}
      assert TLAValue.parse!("mv1") == {:mv, "mv1"}
      assert TLAValue.parse!("NULL") == {:mv, "NULL"}
    end

    test "functions over sessions, in any key order" do
      expected = {:fun, [{{:mv, "s1"}, {:str, "a"}}, {{:mv, "s2"}, 0}]}

      assert TLAValue.parse!(~s{(s1 :> "a" @@ s2 :> 0)}) == expected
      assert TLAValue.parse!(~s{(s2 :> 0 @@ s1 :> "a")}) == expected
    end

    test "sequences, sets, and records" do
      assert TLAValue.parse!("<<1, 2>>") == {:seq, [1, 2]}
      assert TLAValue.parse!("<<>>") == {:seq, []}
      assert TLAValue.parse!("{3, 1}") == {:set, [1, 3]}
      assert TLAValue.parse!("[b |-> 2, a |-> 1]") == {:rec, [{"a", 1}, {"b", 2}]}
    end

    test "bad text" do
      assert {:error, _} = TLAValue.parse("(s1 :> 1")
      assert {:error, _} = TLAValue.parse("1 2")
    end
  end

  test "render/1 writes text that parse/1 reads back" do
    values = [
      7,
      -3,
      true,
      {:str, ~s(x "y")},
      {:mv, "mv2"},
      {:seq, [1, {:str, "a"}]},
      {:set, [1, 2]},
      {:rec, [{"a", 1}]},
      {:fun, [{{:mv, "s1"}, 1}, {{:mv, "s2"}, 2}]}
    ]

    for value <- values do
      assert TLAValue.parse!(TLAValue.render(value)) == value
    end
  end

  test "parse_assignments/1 reads values that continue on the next lines" do
    lines = [
      "/\\ state = (s1 :> \"idle\" @@",
      "   s2 :> \"busy\")",
      "/\\ holder = NULL"
    ]

    assert TLAValue.parse_assignments(lines) == %{
             "state" => {:fun, [{{:mv, "s1"}, {:str, "idle"}}, {{:mv, "s2"}, {:str, "busy"}}]},
             "holder" => {:mv, "NULL"}
           }

    assert TLAValue.parse_assignments(["x = 3"]) == %{"x" => 3}
  end

  test "from_state/2 names each variable as the spec does" do
    model = Model.build(Accord.Test.DistributedLock.Protocol)
    [init] = Model.init_states(model)

    assert TLAValue.from_state(model, init) == %{
             "state" =>
               {:fun, [{{:mv, "s1"}, {:str, "unlocked"}}, {{:mv, "s2"}, {:str, "unlocked"}}]},
             "holder" => {:mv, "NULL"},
             "fence_token" => 0
           }
  end
end
