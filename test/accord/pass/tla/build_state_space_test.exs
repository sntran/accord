defmodule Accord.Pass.TLA.BuildStateSpaceTest do
  use ExUnit.Case, async: true

  alias Accord.IR
  alias Accord.IR.{Branch, Check, Property, State, Track, Transition}
  alias Accord.Pass.TLA.BuildStateSpace
  alias Accord.TLA.ModelConfig

  defp minimal_ir do
    %IR{
      name: Test.Protocol,
      initial: :ready,
      states: %{
        ready: %State{
          name: :ready,
          transitions: [
            %Transition{
              message_pattern: :go,
              message_types: [],
              kind: :call,
              branches: [%Branch{reply_type: {:literal, :ok}, next_state: :done}]
            }
          ]
        },
        done: %State{name: :done, terminal: true}
      }
    }
  end

  defp default_config, do: %ModelConfig{}

  describe "variable collection" do
    test "always includes a state variable" do
      {:ok, ss} = BuildStateSpace.run(minimal_ir(), default_config())
      state_var = Enum.find(ss.variables, &(&1.name == "state"))

      assert state_var
      assert state_var.init == ~s("ready")
    end

    test "state type includes all declared states" do
      {:ok, ss} = BuildStateSpace.run(minimal_ir(), default_config())
      state_var = Enum.find(ss.variables, &(&1.name == "state"))

      assert state_var.type =~ "ready"
      assert state_var.type =~ "done"
    end

    test "includes one variable per track" do
      ir = %{
        minimal_ir()
        | tracks: [
            %Track{name: :counter, type: :integer, default: 0},
            %Track{name: :label, type: :atom, default: :none}
          ]
      }

      {:ok, ss} = BuildStateSpace.run(ir, default_config())
      var_names = Enum.map(ss.variables, & &1.name)

      assert "counter" in var_names
      assert "label" in var_names
    end

    test "track init uses default value" do
      ir = %{
        minimal_ir()
        | tracks: [
            %Track{name: :counter, type: :integer, default: 2}
          ]
      }

      {:ok, ss} = BuildStateSpace.run(ir, default_config())
      counter_var = Enum.find(ss.variables, &(&1.name == "counter"))

      assert counter_var.init == "2"
    end

    test "reports E044 when default is outside resolved domain" do
      ir = %{
        minimal_ir()
        | tracks: [
            %Track{name: :counter, type: :integer, default: 42}
          ]
      }

      assert {:error, [report]} = BuildStateSpace.run(ir, default_config())
      assert report.code == "E044"
      assert report.message =~ "track :counter default 42 is outside"
    end

    test "reports one E044 per offending track" do
      ir = %{
        minimal_ir()
        | tracks: [
            %Track{name: :counter, type: :integer, default: 42},
            %Track{name: :fine, type: :integer, default: 0},
            %Track{name: :other, type: :integer, default: -99}
          ]
      }

      assert {:error, reports} = BuildStateSpace.run(ir, default_config())
      assert length(reports) == 2
      assert Enum.all?(reports, &(&1.code == "E044"))
    end

    test "init override replaces protocol default" do
      ir = %{
        minimal_ir()
        | tracks: [
            %Track{name: :counter, type: :integer, default: 42}
          ]
      }

      config = %ModelConfig{init: %{counter: 1}}

      {:ok, ss} = BuildStateSpace.run(ir, config)
      counter_var = Enum.find(ss.variables, &(&1.name == "counter"))
      assert counter_var.init == "1"
    end
  end

  describe "NULL constants" do
    test "track with nil default includes NULL in type" do
      ir = %{
        minimal_ir()
        | tracks: [
            %Track{name: :holder, type: :term, default: nil}
          ]
      }

      {:ok, ss} = BuildStateSpace.run(ir, default_config())
      holder_var = Enum.find(ss.variables, &(&1.name == "holder"))

      assert holder_var.type =~ "NULL"
      assert holder_var.init == "NULL"
    end

    test "track with non-nil default does not include NULL" do
      ir = %{
        minimal_ir()
        | tracks: [
            %Track{name: :counter, type: :integer, default: 0}
          ]
      }

      {:ok, ss} = BuildStateSpace.run(ir, %ModelConfig{domains: %{counter: 0..5}})
      counter_var = Enum.find(ss.variables, &(&1.name == "counter"))

      refute counter_var.type =~ "NULL"
    end

    test "NULL appears in constants when tracks have nil defaults" do
      ir = %{
        minimal_ir()
        | tracks: [
            %Track{name: :holder, type: :term, default: nil}
          ]
      }

      {:ok, ss} = BuildStateSpace.run(ir, default_config())

      assert "NULL" in ss.constants
    end
  end

  describe "model value constants" do
    test "collects model value names from track domains" do
      ir = %{
        minimal_ir()
        | tracks: [
            %Track{name: :color, type: :atom, default: :red}
          ]
      }

      config = %ModelConfig{domains: %{color: {:model_values, [:red, :blue]}}}
      {:ok, ss} = BuildStateSpace.run(ir, config)

      assert "red" in ss.constants
      assert "blue" in ss.constants
    end

    test "collects numbered model values" do
      ir = %{
        minimal_ir()
        | tracks: [
            %Track{name: :item, type: :term, default: :x}
          ]
      }

      config = %ModelConfig{domains: %{item: {:model_values, 2}}}
      {:ok, ss} = BuildStateSpace.run(ir, config)

      assert "mv1" in ss.constants
      assert "mv2" in ss.constants
    end

    test "no constants for range domains" do
      ir = %{
        minimal_ir()
        | tracks: [
            %Track{name: :counter, type: :integer, default: 0}
          ]
      }

      config = %ModelConfig{domains: %{counter: 0..10}}
      {:ok, ss} = BuildStateSpace.run(ir, config)

      assert ss.constants == []
    end
  end

  describe "correspondence counters" do
    defp corr_ir(checks) do
      %{minimal_ir() | properties: [%Property{name: :open_close, checks: checks}]}
    end

    test "counter is excluded from TypeInvariant and bounded by StateConstraint" do
      ir =
        corr_ir([
          %Check{kind: :correspondence, spec: %{open: :borrow, close: [:return], by: nil}}
        ])

      {:ok, ss} = BuildStateSpace.run(ir, default_config())

      # Declared and initialized, but not type-constrained: the named
      # `pending >= 0` invariant is the meaningful check.
      assert Enum.any?(ss.variables, &(&1.name == "borrow_pending"))
      refute ss.type_invariant =~ "borrow_pending"
      assert ss.init =~ "borrow_pending = 0"

      # The upper bound moves to the state constraint.
      assert ss.state_constraint =~ "borrow_pending =< 3"
    end

    test "counter bound composes with a configured state constraint" do
      ir =
        corr_ir([
          %Check{kind: :correspondence, spec: %{open: :borrow, close: [:return], by: nil}}
        ])

      config = %ModelConfig{state_constraint: "counter =< 5"}
      {:ok, ss} = BuildStateSpace.run(ir, config)

      assert ss.state_constraint =~ "counter =< 5"
      assert ss.state_constraint =~ "borrow_pending =< 3"
      assert ss.state_constraint =~ "/\\"
    end

    test "identical correspondence checks share one counter" do
      ir =
        corr_ir([
          %Check{kind: :correspondence, spec: %{open: :borrow, close: [:return], by: nil}},
          %Check{kind: :correspondence, spec: %{open: :borrow, close: [:return], by: nil}}
        ])

      {:ok, ss} = BuildStateSpace.run(ir, default_config())

      counters = Enum.filter(ss.variables, &(&1.name == "borrow_pending"))
      assert length(counters) == 1
    end

    test "same open with different close sets reports E038" do
      ir =
        corr_ir([
          %Check{kind: :correspondence, spec: %{open: :borrow, close: [:return], by: nil}},
          %Check{kind: :correspondence, spec: %{open: :borrow, close: [:discard], by: nil}}
        ])

      assert {:error, [report]} = BuildStateSpace.run(ir, default_config())
      assert report.code == "E038"
      assert report.message =~ ":borrow"
    end

    test "keyed correspondence gets no counter variable" do
      ir =
        corr_ir([
          %Check{kind: :correspondence, spec: %{open: :borrow, close: [:return], by: :item}}
        ])

      {:ok, ss} = BuildStateSpace.run(ir, default_config())

      refute Enum.any?(ss.variables, &(&1.name == "borrow_pending"))
    end
  end

  describe "boolean tracks" do
    test "domain, init, and TypeInvariant use TLA+ booleans consistently" do
      ir = %{
        minimal_ir()
        | tracks: [%Track{name: :flag, type: :boolean, default: false}]
      }

      {:ok, ss} = BuildStateSpace.run(ir, default_config())
      flag_var = Enum.find(ss.variables, &(&1.name == "flag"))

      assert flag_var.type == "BOOLEAN"
      assert flag_var.init == "FALSE"
      assert ss.type_invariant =~ "flag \\in BOOLEAN"
      assert ss.init =~ "flag = FALSE"
      # The broken form: a string-set domain contradicting a boolean init.
      refute ss.type_invariant =~ ~s("true")
    end
  end

  describe "symmetry sets" do
    test "model-value symmetry sets produce permutation expressions" do
      ir = %{
        minimal_ir()
        | tracks: [%Track{name: :client, type: :term, default: nil}]
      }

      config = %ModelConfig{
        domains: %{client: {:model_values, 3}},
        symmetry_sets: [:client]
      }

      {:ok, ss} = BuildStateSpace.run(ir, config)

      assert ss.symmetry_exprs == ["Permutations({mv1, mv2, mv3})"]
    end

    test "symmetry set over a non-model-value domain reports E046" do
      config = %ModelConfig{
        domains: %{counter: 0..3},
        symmetry_sets: [:counter]
      }

      assert {:error, [report]} = BuildStateSpace.run(minimal_ir(), config)
      assert report.code == "E046"
      assert report.message =~ ":counter"
    end

    test "symmetry set with no configured domain reports E046" do
      config = %ModelConfig{symmetry_sets: [:ghost]}

      assert {:error, [report]} = BuildStateSpace.run(minimal_ir(), config)
      assert report.code == "E046"
      assert report.message =~ "no domain is configured"
    end
  end

  describe "event variable" do
    test "not present without local invariants" do
      {:ok, ss} = BuildStateSpace.run(minimal_ir(), default_config())

      refute Enum.any?(ss.variables, &(&1.name == "event"))
    end

    test "not present even with local invariants" do
      # No generated formula ever read the event variable; it only
      # multiplied the distinct-state count and, by turning self-loops
      # into variable-changing steps, could flip liveness verdicts.
      ir = %{
        minimal_ir()
        | properties: [
            %Property{
              name: :state_check,
              checks: [
                %Check{
                  kind: :local_invariant,
                  spec: %{state: :ready, fun: fn _, _ -> true end, ast: nil}
                }
              ]
            }
          ]
      }

      {:ok, ss} = BuildStateSpace.run(ir, default_config())

      refute Enum.any?(ss.variables, &(&1.name == "event"))
    end
  end

  describe "correspondence counter variables" do
    test "generates counter var for correspondence checks" do
      ir = %{
        minimal_ir()
        | properties: [
            %Property{
              name: :open_close,
              checks: [
                %Check{kind: :correspondence, spec: %{open: :open, close: [:close]}}
              ]
            }
          ]
      }

      {:ok, ss} = BuildStateSpace.run(ir, default_config())

      assert length(ss.correspondences) == 1
      [corr] = ss.correspondences
      assert corr.open == :open
      assert corr.close == [:close]
      assert corr.counter_var == "open_pending"

      counter_var = Enum.find(ss.variables, &(&1.name == "open_pending"))
      assert counter_var
      assert counter_var.init == "0"
    end

    test "counter var uses default correspondence_counter domain from ModelConfig" do
      ir = %{
        minimal_ir()
        | properties: [
            %Property{
              name: :open_close,
              checks: [
                %Check{kind: :correspondence, spec: %{open: :open, close: [:close]}}
              ]
            }
          ]
      }

      {:ok, ss} = BuildStateSpace.run(ir, default_config())
      counter_var = Enum.find(ss.variables, &(&1.name == "open_pending"))

      # Default correspondence_counter domain is -1..3.
      assert counter_var.type == "-1..3"
    end

    test "counter var domain can be overridden per-counter in ModelConfig" do
      ir = %{
        minimal_ir()
        | properties: [
            %Property{
              name: :open_close,
              checks: [
                %Check{kind: :correspondence, spec: %{open: :open, close: [:close]}}
              ]
            }
          ]
      }

      config = %ModelConfig{domains: %{open_pending: -1..10}}
      {:ok, ss} = BuildStateSpace.run(ir, config)
      counter_var = Enum.find(ss.variables, &(&1.name == "open_pending"))

      assert counter_var.type == "-1..10"
    end
  end

  describe "TypeInvariant and Init" do
    test "TypeInvariant references all variables" do
      ir = %{
        minimal_ir()
        | tracks: [
            %Track{name: :x, type: :integer, default: 0}
          ]
      }

      {:ok, ss} = BuildStateSpace.run(ir, %ModelConfig{domains: %{x: 0..5}})

      assert ss.type_invariant =~ "state \\in"
      assert ss.type_invariant =~ "x \\in 0..5"
    end

    test "Init assigns all initial values" do
      ir = %{
        minimal_ir()
        | tracks: [
            %Track{name: :x, type: :integer, default: 1}
          ]
      }

      {:ok, ss} = BuildStateSpace.run(ir, default_config())

      assert ss.init =~ ~s(state = "ready")
      assert ss.init =~ "x = 1"
    end
  end
end
