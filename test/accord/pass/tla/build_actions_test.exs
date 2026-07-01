defmodule Accord.Pass.TLA.BuildActionsTest do
  use ExUnit.Case, async: true

  alias Accord.IR
  alias Accord.IR.{Branch, State, Track, Transition}
  alias Accord.Pass.TLA.{BuildActions, BuildStateSpace}
  alias Accord.TLA.ModelConfig

  defp build(ir, config \\ %ModelConfig{}) do
    {:ok, ss} = BuildStateSpace.run(ir, config)
    {:ok, actions} = BuildActions.run(ir, ss, config)
    {ss, actions}
  end

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

  describe "call actions" do
    test "creates one action per state/transition/branch combination" do
      {_ss, actions} = build(minimal_ir())

      assert length(actions) == 1
      [action] = actions
      assert action.source_state == "ready"
      assert action.target_state == "done"
      assert action.message_tag == "go"
    end

    test "action name encodes source and target" do
      {_ss, actions} = build(minimal_ir())
      [action] = actions

      assert action.name == "GoFromReadyToDone"
    end

    test "state precondition matches source state" do
      {_ss, actions} = build(minimal_ir())
      [action] = actions

      assert ~s(state = "ready") in action.preconditions
    end

    test "primed state assignment matches target" do
      {_ss, actions} = build(minimal_ir())
      [action] = actions

      assert action.primed["state"] == ~s("done")
    end
  end

  describe "cast actions" do
    test "cast stays in same state" do
      ir = %{
        minimal_ir()
        | anystate: [
            %Transition{
              message_pattern: :heartbeat,
              message_types: [],
              kind: :cast,
              branches: []
            }
          ]
      }

      {_ss, actions} = build(ir)
      casts = Enum.filter(actions, &(&1.message_tag == "heartbeat"))

      assert length(casts) > 0

      Enum.each(casts, fn cast ->
        assert cast.source_state == cast.target_state
      end)
    end

    test "cast name includes Cast prefix" do
      ir = %{
        minimal_ir()
        | anystate: [
            %Transition{
              message_pattern: :heartbeat,
              message_types: [],
              kind: :cast,
              branches: []
            }
          ]
      }

      {_ss, actions} = build(ir)
      cast = Enum.find(actions, &(&1.message_tag == "heartbeat"))

      assert cast.name =~ "Cast"
    end
  end

  describe "existential variables" do
    test "typed message args become existential vars" do
      ir = %IR{
        name: Test.Protocol,
        initial: :ready,
        states: %{
          ready: %State{
            name: :ready,
            transitions: [
              %Transition{
                message_pattern: {:set, :_},
                message_types: [:integer],
                kind: :call,
                branches: [%Branch{reply_type: {:literal, :ok}, next_state: :ready}]
              }
            ]
          }
        }
      }

      config = %ModelConfig{domains: %{integer: -2..2}}
      {_ss, actions} = build(ir, config)
      [action] = actions

      assert length(action.existential_vars) == 1
      [{var_name, domain}] = action.existential_vars
      assert var_name =~ "msg_"
      assert domain == "-2..2"
    end

    test "no existential vars for bare atom messages" do
      {_ss, actions} = build(minimal_ir())
      [action] = actions

      assert action.existential_vars == []
    end
  end

  describe "guards as preconditions" do
    test "guard AST compiles to TLA+ precondition" do
      guard_ast = quote(do: fn {:bet, chips}, tracks -> chips <= tracks.balance end)

      ir = %IR{
        name: Test.Protocol,
        initial: :ready,
        tracks: [%Track{name: :balance, type: :integer, default: 100}],
        states: %{
          ready: %State{
            name: :ready,
            transitions: [
              %Transition{
                message_pattern: {:bet, :_},
                message_types: [:pos_integer],
                message_arg_names: ["chips"],
                kind: :call,
                branches: [%Branch{reply_type: {:literal, :ok}, next_state: :ready}],
                guard: %{
                  fun: fn {:bet, chips}, tracks -> chips <= tracks.balance end,
                  ast: guard_ast
                }
              }
            ]
          }
        }
      }

      config = %ModelConfig{domains: %{balance: 0..100, pos_integer: 1..10}}
      {_ss, actions} = build(ir, config)
      [action] = actions

      # Guard should appear as a precondition beyond just the state check.
      assert length(action.preconditions) > 1
    end
  end

  describe "primed assignments" do
    test "update fn map updates become primed track assignments" do
      update_ast = quote(do: fn {:set, val}, _reply, tracks -> %{tracks | counter: val} end)

      ir = %IR{
        name: Test.Protocol,
        initial: :ready,
        tracks: [%Track{name: :counter, type: :integer, default: 0}],
        states: %{
          ready: %State{
            name: :ready,
            transitions: [
              %Transition{
                message_pattern: {:set, :_},
                message_types: [:integer],
                kind: :call,
                branches: [%Branch{reply_type: {:literal, :ok}, next_state: :ready}],
                update: %{
                  fun: fn {:set, val}, _reply, tracks -> %{tracks | counter: val} end,
                  ast: update_ast
                }
              }
            ]
          }
        }
      }

      config = %ModelConfig{domains: %{counter: 0..10, integer: 0..10}}
      {_ss, actions} = build(ir, config)
      [action] = actions

      assert Map.has_key?(action.primed, "counter")
    end
  end

  describe "UNCHANGED sets" do
    test "unmodified variables appear in unchanged" do
      ir = %IR{
        name: Test.Protocol,
        initial: :ready,
        tracks: [
          %Track{name: :x, type: :integer, default: 0},
          %Track{name: :y, type: :integer, default: 0}
        ],
        states: %{
          ready: %State{
            name: :ready,
            transitions: [
              %Transition{
                message_pattern: :go,
                message_types: [],
                kind: :call,
                branches: [%Branch{reply_type: {:literal, :ok}, next_state: :ready}]
              }
            ]
          }
        }
      }

      config = %ModelConfig{domains: %{x: 0..5, y: 0..5}}
      {_ss, actions} = build(ir, config)
      [action] = actions

      # No update fn, so tracks are unchanged.
      assert "x" in action.unchanged
      assert "y" in action.unchanged
    end

    test "state is not in unchanged when it changes" do
      {_ss, actions} = build(minimal_ir())
      [action] = actions

      # State changes from ready to done.
      refute "state" in action.unchanged
    end
  end

  describe "branching" do
    test "multiple branches produce multiple actions" do
      ir = %IR{
        name: Test.Protocol,
        initial: :ready,
        states: %{
          ready: %State{
            name: :ready,
            transitions: [
              %Transition{
                message_pattern: {:try, :_},
                message_types: [:integer],
                kind: :call,
                branches: [
                  %Branch{reply_type: {:literal, :ok}, next_state: :done},
                  %Branch{reply_type: {:tagged, :error, :atom}, next_state: :ready}
                ]
              }
            ]
          },
          done: %State{name: :done, terminal: true}
        }
      }

      config = %ModelConfig{domains: %{integer: 0..3}}
      {_ss, actions} = build(ir, config)

      try_actions = Enum.filter(actions, &(&1.message_tag == "try"))
      assert length(try_actions) == 2

      targets = Enum.map(try_actions, & &1.target_state) |> Enum.sort()
      assert targets == ["done", "ready"]
    end
  end

  describe "fidelity errors" do
    defp guarded_ir(guard_ast, opts \\ []) do
      arg_names = Keyword.get(opts, :arg_names, ["chips"])

      %IR{
        name: Test.Protocol,
        initial: :ready,
        tracks: [%Track{name: :balance, type: :integer, default: 0}],
        states: %{
          ready: %State{
            name: :ready,
            transitions: [
              %Transition{
                message_pattern: {:bet, :_},
                message_types: [:pos_integer],
                message_arg_names: arg_names,
                kind: :call,
                branches: [%Branch{reply_type: {:literal, :ok}, next_state: :ready}],
                guard: %{fun: fn _msg, _tracks -> true end, ast: guard_ast}
              }
            ]
          }
        }
      }
    end

    defp run_actions(ir, config \\ %ModelConfig{}) do
      {:ok, ss} = BuildStateSpace.run(ir, config)
      BuildActions.run(ir, ss, config)
    end

    test "untranslatable guard reports E041" do
      ast = quote(do: fn {:bet, chips}, tracks -> Enum.max([chips, 1]) > 0 end)

      assert {:error, [report]} = run_actions(guarded_ir(ast))
      assert report.code == "E041"
      assert report.message =~ "cannot compile guard to TLA+"
      assert report.message =~ "Enum.max"
    end

    test "guard variable not matching a declared argument reports E043" do
      # The declared name is `chips`; the guard binds `c` in its own head,
      # which the model cannot connect to the msg_chips existential.
      ast = quote(do: fn {:bet, c}, tracks -> c <= tracks.balance end)

      assert {:error, [report]} = run_actions(guarded_ir(ast))
      assert report.code == "E043"
      assert report.message =~ "`c`"
      assert Enum.any?(report.help, &(&1 =~ ":chips"))
    end

    test "guard referencing an unknown track reports E043" do
      ast = quote(do: fn {:bet, chips}, tracks -> chips <= tracks.balancee end)

      assert {:error, [report]} = run_actions(guarded_ir(ast))
      assert report.code == "E043"
      assert report.message =~ "unknown track `balancee`"
      assert Enum.any?(report.help, &(&1 =~ "balance"))
    end

    test "update writing an unknown track reports E043" do
      update_ast = quote(do: fn {:bet, chips}, _reply, tracks -> %{tracks | balanse: chips} end)

      ir = %IR{
        name: Test.Protocol,
        initial: :ready,
        tracks: [%Track{name: :balance, type: :integer, default: 0}],
        states: %{
          ready: %State{
            name: :ready,
            transitions: [
              %Transition{
                message_pattern: {:bet, :_},
                message_types: [:pos_integer],
                message_arg_names: ["chips"],
                kind: :call,
                branches: [%Branch{reply_type: {:literal, :ok}, next_state: :ready}],
                update: %{fun: fn _m, _r, t -> t end, ast: update_ast}
              }
            ]
          }
        }
      }

      assert {:error, [report]} = run_actions(ir)
      assert report.code == "E043"
      assert report.message =~ "unknown track `balanse`"
    end

    test "untranslatable where: constraint reports E045" do
      constraint_ast =
        quote(do: fn {:ok, token}, tracks -> String.valid?(token) end)

      ir = %IR{
        name: Test.Protocol,
        initial: :ready,
        tracks: [%Track{name: :balance, type: :integer, default: 0}],
        states: %{
          ready: %State{
            name: :ready,
            transitions: [
              %Transition{
                message_pattern: :go,
                message_types: [],
                kind: :call,
                branches: [
                  %Branch{
                    reply_type: {:tagged, :ok, :pos_integer},
                    next_state: :ready,
                    constraint: %{fun: fn _r, _t -> true end, ast: constraint_ast}
                  }
                ]
              }
            ]
          }
        }
      }

      assert {:error, [report]} = run_actions(ir)
      assert report.code == "E045"
      assert report.message =~ "where: constraint"
    end

    defp update_ir(update_ast, opts \\ []) do
      reply_type = Keyword.get(opts, :reply_type, {:literal, :ok})

      %IR{
        name: Test.Protocol,
        initial: :ready,
        tracks: [%Track{name: :balance, type: :integer, default: 0}],
        states: %{
          ready: %State{
            name: :ready,
            transitions: [
              %Transition{
                message_pattern: {:set, :_},
                message_types: [:pos_integer],
                message_arg_names: ["val"],
                kind: :call,
                branches: [%Branch{reply_type: reply_type, next_state: :ready}],
                update: %{fun: fn _m, _r, t -> t end, ast: update_ast}
              }
            ]
          }
        }
      }
    end

    test "update the extractor cannot understand reports E042" do
      ast = quote(do: fn {:set, val}, _reply, tracks -> Map.put(tracks, :balance, val) end)

      assert {:error, [report]} = run_actions(update_ir(ast))
      assert report.code == "E042"
      assert report.message =~ "Map.put"
      assert report.message =~ "vacuously"
    end

    test "identity update is a legitimate no-op, not an error" do
      ast = quote(do: fn _msg, _reply, tracks -> tracks end)

      assert {:ok, [action]} = run_actions(update_ir(ast))
      refute Map.has_key?(action.primed, "balance")
    end

    test "if resolvable against the reply literal takes the matching arm" do
      ast =
        quote(
          do: fn {:set, val}, reply, tracks ->
            if reply == :ok, do: %{tracks | balance: val}, else: tracks
          end
        )

      assert {:ok, [action]} = run_actions(update_ir(ast))
      assert action.primed["balance"] == "msg_val"
    end

    test "if resolving to a missing else is an identity update" do
      ast =
        quote(
          do: fn {:set, val}, reply, tracks ->
            if reply == :ok, do: %{tracks | balance: val}
          end
        )

      ir = update_ir(ast, reply_type: {:literal, :error})

      assert {:ok, [action]} = run_actions(ir)
      refute Map.has_key?(action.primed, "balance")
    end

    test "if condition on tracks reports E042" do
      ast =
        quote(
          do: fn {:set, val}, _reply, tracks ->
            if tracks.balance > 0, do: %{tracks | balance: val}, else: tracks
          end
        )

      assert {:error, [report]} = run_actions(update_ir(ast))
      assert report.code == "E042"
    end

    test "case with no matching arm and no wildcard reports E042" do
      ast =
        quote(
          do: fn {:set, val}, reply, tracks ->
            case reply do
              :other -> %{tracks | balance: val}
            end
          end
        )

      assert {:error, [report]} = run_actions(update_ir(ast))
      assert report.code == "E042"
    end

    test "errors from multiple sites are all collected" do
      guard_ast = quote(do: fn {:bet, chips}, tracks -> Enum.max([chips, 1]) > 0 end)
      update_ast = quote(do: fn {:bet, chips}, _reply, tracks -> %{tracks | balanse: chips} end)

      ir = %IR{
        name: Test.Protocol,
        initial: :ready,
        tracks: [%Track{name: :balance, type: :integer, default: 0}],
        states: %{
          ready: %State{
            name: :ready,
            transitions: [
              %Transition{
                message_pattern: {:bet, :_},
                message_types: [:pos_integer],
                message_arg_names: ["chips"],
                kind: :call,
                branches: [%Branch{reply_type: {:literal, :ok}, next_state: :ready}],
                guard: %{fun: fn _m, _t -> true end, ast: guard_ast},
                update: %{fun: fn _m, _r, t -> t end, ast: update_ast}
              }
            ]
          }
        }
      }

      assert {:error, reports} = run_actions(ir)
      codes = reports |> Enum.map(& &1.code) |> Enum.sort()
      assert codes == ["E041", "E043"]
    end
  end
end
