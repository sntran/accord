defmodule Accord.Pass.ValidateRolesTest do
  use ExUnit.Case, async: true

  alias Accord.IR
  alias Accord.IR.{Role, State}
  alias Accord.Pass.ValidateRoles
  alias Pentiment.Span.Search

  defp base_ir(roles) do
    %IR{
      name: Test.Protocol,
      initial: :ready,
      roles: roles,
      states: %{ready: %State{name: :ready, terminal: true}}
    }
  end

  defp role(name, line) do
    %Role{name: name, span: Search.new(line: line, pattern: "role")}
  end

  test "accepts no roles (defaults apply)" do
    ir = base_ir([])
    assert {:ok, ^ir} = ValidateRoles.run(ir)
  end

  test "accepts one role" do
    ir = base_ir([role(:consumer, 3)])
    assert {:ok, ^ir} = ValidateRoles.run(ir)
  end

  test "accepts two roles" do
    ir = base_ir([role(:consumer, 3), role(:producer, 4)])
    assert {:ok, ^ir} = ValidateRoles.run(ir)
  end

  test "rejects three roles with E050" do
    ir = base_ir([role(:a, 3), role(:b, 4), role(:c, 5)])

    assert {:error, [report]} = ValidateRoles.run(ir)
    assert report.code == "E050"
    assert report.message =~ "two-party"
    assert Enum.any?(report.help, &(&1 =~ "projection"))
  end

  test "rejects duplicate role names with E051" do
    ir = base_ir([role(:peer, 3), role(:peer, 4)])

    assert {:error, [report]} = ValidateRoles.run(ir)
    assert report.code == "E051"
    assert report.message =~ ":peer"
  end
end
