defmodule Accord.Protocol.ConstTest do
  @moduledoc """
  Protocol constants: declared once, substituted at compile time into
  every captured expression — the runtime closure and the TLA+ spec see
  the same literal.
  """
  use ExUnit.Case, async: true

  alias Accord.TLA.Files

  defmodule ConstProtocol do
    use Accord.Protocol

    initial :ready

    const :limit, 2

    track :count, :non_neg_integer, default: 0, domain: 0..4

    state :ready do
      on :bump do
        guard fn :bump, tracks -> tracks.count < const(:limit) end
        reply :ok
        goto :ready
        update fn :bump, _reply, tracks -> %{tracks | count: tracks.count + 1} end
      end

      on :stop, reply: :stopped, goto: :stopped
    end

    state :stopped, terminal: true

    property :bounded_by_limit do
      invariant fn tracks -> tracks.count <= const(:limit) end
    end

    property :count_capped do
      bounded :count, max: const(:limit)
    end
  end

  test "substitution reaches the runtime guard closure" do
    ir = ConstProtocol.__ir__()
    transition = hd(ir.states[:ready].transitions)

    # The closure was compiled with the literal: count 1 < 2 passes,
    # count 2 < 2 fails.
    assert transition.guard.fun.(:bump, %{count: 1})
    refute transition.guard.fun.(:bump, %{count: 2})
  end

  test "substitution reaches the escaped AST and the TLA+ spec" do
    ir = ConstProtocol.__ir__()
    transition = hd(ir.states[:ready].transitions)

    # No const/1 call survives in the stored AST.
    refute Macro.to_string(transition.guard.ast) =~ "const"

    {tla_path, _} = Files.paths(ConstProtocol)
    tla = File.read!(tla_path)

    assert tla =~ "count < 2"
    assert tla =~ "BoundedByLimit == count =< 2"
    assert tla =~ "CountCapped == count =< 2"
  end

  test "bounded max: accepts a const" do
    ir = ConstProtocol.__ir__()

    bounded =
      for prop <- ir.properties, check <- prop.checks, check.kind == :bounded, do: check

    assert [%{spec: %{max: 2}}] = bounded
  end

  test "unknown constants are compile errors" do
    assert_raise CompileError, ~r/unknown protocol constant :missing/, fn ->
      defmodule UnknownConst do
        use Accord.Protocol, tla: :off

        initial :ready

        const :limit, 2

        state :ready do
          on :bump do
            guard fn :bump, tracks -> tracks.count < const(:missing) end
            reply :ok
            goto :ready
          end
        end
      end
    end
  end

  test "duplicate constants are compile errors" do
    assert_raise CompileError, ~r/duplicate protocol constant :limit/, fn ->
      defmodule DuplicateConst do
        use Accord.Protocol, tla: :off

        initial :ready
        const :limit, 2
        const :limit, 3

        state :ready, terminal: true
      end
    end
  end

  test "non-literal constants are compile errors" do
    assert_raise CompileError, ~r/must be a literal/, fn ->
      defmodule NonLiteralConst do
        use Accord.Protocol, tla: :off

        initial :ready
        const :limit, 1 + 1

        state :ready, terminal: true
      end
    end
  end
end
