defmodule Accord.IR.TypeSubtypeTest do
  use ExUnit.Case, async: true
  use ExUnitProperties

  alias Accord.IR.Type
  alias Accord.Type.Check

  describe "reflexivity and top" do
    test "every type is a subtype of itself and of term" do
      for t <- [
            :string,
            :integer,
            :pos_integer,
            :atom,
            {:list, :integer},
            {:tuple, [:atom, :integer]},
            {:literal, :ok},
            {:tagged, :ok, :pos_integer},
            {:union, [:atom, :integer]}
          ] do
        assert Type.subtype?(t, t)
        assert Type.subtype?(t, :term)
      end
    end
  end

  describe "literals" do
    test "integer literals respect sign constraints" do
      assert Type.subtype?({:literal, 5}, :pos_integer)
      assert Type.subtype?({:literal, 0}, :non_neg_integer)
      refute Type.subtype?({:literal, 0}, :pos_integer)
      refute Type.subtype?({:literal, -1}, :non_neg_integer)
      assert Type.subtype?({:literal, -1}, :integer)
    end

    test "atom, boolean, and string literals" do
      assert Type.subtype?({:literal, :ok}, :atom)
      assert Type.subtype?({:literal, true}, :boolean)
      assert Type.subtype?({:literal, true}, :atom)
      assert Type.subtype?({:literal, "x"}, :binary)
      refute Type.subtype?({:literal, :ok}, :integer)
    end
  end

  describe "hierarchy" do
    test "integer widening chain" do
      assert Type.subtype?(:pos_integer, :non_neg_integer)
      assert Type.subtype?(:pos_integer, :integer)
      assert Type.subtype?(:non_neg_integer, :integer)
      refute Type.subtype?(:integer, :pos_integer)
      refute Type.subtype?(:non_neg_integer, :pos_integer)
    end

    test "boolean is an atom" do
      assert Type.subtype?(:boolean, :atom)
      refute Type.subtype?(:atom, :boolean)
    end
  end

  describe "compound types" do
    test "lists and tuples are covariant" do
      assert Type.subtype?({:list, :pos_integer}, {:list, :integer})
      refute Type.subtype?({:list, :integer}, {:list, :pos_integer})
      assert Type.subtype?({:tuple, [:pos_integer]}, {:tuple, [:integer]})
      refute Type.subtype?({:tuple, [:atom]}, {:tuple, [:atom, :atom]})
    end

    test "tagged tuples require the same tag, covariant payload" do
      assert Type.subtype?({:tagged, :ok, :pos_integer}, {:tagged, :ok, :integer})
      refute Type.subtype?({:tagged, :ok, :integer}, {:tagged, :error, :integer})
      refute Type.subtype?({:tagged, :ok, :integer}, {:tagged, :ok, :pos_integer})
    end

    test "unions" do
      assert Type.subtype?(:pos_integer, {:union, [:atom, :integer]})
      assert Type.subtype?({:union, [:pos_integer, {:literal, 0}]}, :non_neg_integer)
      refute Type.subtype?({:union, [:pos_integer, :atom]}, :integer)
    end
  end

  describe "soundness against the runtime checker" do
    property "sub <: sup implies every checked value transfers" do
      pairs = [
        {{:literal, 3}, :pos_integer},
        {:pos_integer, :non_neg_integer},
        {:pos_integer, :integer},
        {:boolean, :atom},
        {{:list, :pos_integer}, {:list, :integer}},
        {{:tagged, :ok, :pos_integer}, {:tagged, :ok, :integer}}
      ]

      generators = %{
        {:literal, 3} => StreamData.constant(3),
        :pos_integer => StreamData.positive_integer(),
        :boolean => StreamData.boolean(),
        {:list, :pos_integer} => StreamData.list_of(StreamData.positive_integer()),
        {:tagged, :ok, :pos_integer} => StreamData.map(StreamData.positive_integer(), &{:ok, &1})
      }

      check all(
              {sub, sup} <- StreamData.member_of(pairs),
              value <- Map.fetch!(generators, sub)
            ) do
        assert Type.subtype?(sub, sup)
        assert Check.check(value, sub) == :ok
        # The defining property: values of the subtype pass the supertype.
        assert Check.check(value, sup) == :ok
      end
    end
  end
end
