defmodule Accord.Protocol.Property do
  @moduledoc false

  # Inner macros for the `property :name do ... end` block form.
  # These accumulate checks into module attributes that are read
  # after the block closes.
  #
  # Each check captures its own span at the check keyword line,
  # so violations and errors point at the specific check rather
  # than the parent property declaration.

  alias Accord.IR.Check

  alias Accord.Protocol.Const

  @doc false
  defmacro invariant(func) do
    func = Const.substitute(func, __CALLER__.module, __CALLER__.file, __CALLER__.line)
    escaped_ast = Macro.escape(func)
    line = __CALLER__.line

    quote do
      checks = Module.get_attribute(__MODULE__, :accord_property_checks)

      check = %Check{
        kind: :invariant,
        spec: %{fun: unquote(func), ast: unquote(escaped_ast)},
        span: Pentiment.Span.search(line: unquote(line), pattern: "invariant")
      }

      Module.put_attribute(__MODULE__, :accord_property_checks, [check | checks])
    end
  end

  @doc false
  defmacro invariant(state_name, func) do
    func = Const.substitute(func, __CALLER__.module, __CALLER__.file, __CALLER__.line)
    escaped_ast = Macro.escape(func)
    line = __CALLER__.line

    quote do
      checks = Module.get_attribute(__MODULE__, :accord_property_checks)

      check = %Check{
        kind: :local_invariant,
        spec: %{state: unquote(state_name), fun: unquote(func), ast: unquote(escaped_ast)},
        span: Pentiment.Span.search(line: unquote(line), pattern: "invariant")
      }

      Module.put_attribute(__MODULE__, :accord_property_checks, [check | checks])
    end
  end

  @doc false
  defmacro action(func) do
    func = Const.substitute(func, __CALLER__.module, __CALLER__.file, __CALLER__.line)
    escaped_ast = Macro.escape(func)
    line = __CALLER__.line

    quote do
      checks = Module.get_attribute(__MODULE__, :accord_property_checks)

      check = %Check{
        kind: :action,
        spec: %{fun: unquote(func), ast: unquote(escaped_ast)},
        span: Pentiment.Span.search(line: unquote(line), pattern: "action")
      }

      Module.put_attribute(__MODULE__, :accord_property_checks, [check | checks])
    end
  end

  @doc false
  # `assuming:` names message tags whose generated actions receive a
  # fairness assumption (WF by default, SF with `fairness: :strong`).
  # Without it, `P ~> Q` is checked under blanket WF_vars(Next), which
  # asserts only "the system does not stutter forever" — any client loop
  # or reachable terminal state then fails realistic liveness properties
  # (see W005).
  defmacro liveness(trigger, opts) do
    target = Keyword.fetch!(opts, :leads_to)
    fairness = Keyword.get(opts, :fairness, :weak)
    timeout = Keyword.get(opts, :timeout, :infinity)
    assuming = Keyword.get(opts, :assuming)
    line = __CALLER__.line

    quote do
      checks = Module.get_attribute(__MODULE__, :accord_property_checks)

      check = %Check{
        kind: :liveness,
        spec: %{
          trigger: unquote(trigger),
          target: unquote(target),
          fairness: unquote(fairness),
          timeout: unquote(timeout),
          assuming: unquote(assuming)
        },
        span: Pentiment.Span.search(line: unquote(line), pattern: "liveness")
      }

      Module.put_attribute(__MODULE__, :accord_property_checks, [check | checks])
    end
  end

  @doc false
  defmacro correspondence(open, close, opts \\ []) do
    by = Keyword.get(opts, :by)
    line = __CALLER__.line

    quote do
      checks = Module.get_attribute(__MODULE__, :accord_property_checks)

      check = %Check{
        kind: :correspondence,
        spec: %{open: unquote(open), close: unquote(close), by: unquote(by)},
        span: Pentiment.Span.search(line: unquote(line), pattern: "correspondence")
      }

      Module.put_attribute(__MODULE__, :accord_property_checks, [check | checks])
    end
  end

  @doc false
  defmacro bounded(track_name, opts) do
    max =
      opts
      |> Keyword.fetch!(:max)
      |> Const.substitute(__CALLER__.module, __CALLER__.file, __CALLER__.line)

    line = __CALLER__.line

    quote do
      checks = Module.get_attribute(__MODULE__, :accord_property_checks)

      check = %Check{
        kind: :bounded,
        spec: %{track: unquote(track_name), max: unquote(max)},
        span: Pentiment.Span.search(line: unquote(line), pattern: "bounded")
      }

      Module.put_attribute(__MODULE__, :accord_property_checks, [check | checks])
    end
  end

  @doc false
  defmacro ordered(event, opts) do
    by = Keyword.fetch!(opts, :by)
    line = __CALLER__.line

    quote do
      checks = Module.get_attribute(__MODULE__, :accord_property_checks)

      check = %Check{
        kind: :ordered,
        spec: %{event: unquote(event), by: unquote(by)},
        span: Pentiment.Span.search(line: unquote(line), pattern: "ordered")
      }

      Module.put_attribute(__MODULE__, :accord_property_checks, [check | checks])
    end
  end

  @doc false
  defmacro precedence(target, required) do
    line = __CALLER__.line

    quote do
      checks = Module.get_attribute(__MODULE__, :accord_property_checks)

      check = %Check{
        kind: :precedence,
        spec: %{target: unquote(target), required: unquote(required)},
        span: Pentiment.Span.search(line: unquote(line), pattern: "precedence")
      }

      Module.put_attribute(__MODULE__, :accord_property_checks, [check | checks])
    end
  end

  @doc false
  # Mutual exclusion across sessions: at most one session in the state.
  # Model-only — verified by TLC at sessions >= 2, not runtime-enforced
  # (the monitor observes a single session; see ADR-009).
  defmacro exclusive(state) do
    line = __CALLER__.line

    quote do
      checks = Module.get_attribute(__MODULE__, :accord_property_checks)

      check = %Check{
        kind: :exclusive,
        spec: %{state: unquote(state)},
        span: Pentiment.Span.search(line: unquote(line), pattern: "exclusive")
      }

      Module.put_attribute(__MODULE__, :accord_property_checks, [check | checks])
    end
  end

  @doc false
  # Cross-session uniqueness: no two sessions hold the same non-empty
  # value of a per-session track — "no two workers hold the same lease".
  # Model-only, verified by TLC at sessions >= 2 (see ADR-009).
  defmacro distinct(track_name, opts) do
    empty = Keyword.fetch!(opts, :empty)
    line = __CALLER__.line

    quote do
      checks = Module.get_attribute(__MODULE__, :accord_property_checks)

      check = %Check{
        kind: :distinct,
        spec: %{track: unquote(track_name), empty: unquote(empty)},
        span: Pentiment.Span.search(line: unquote(line), pattern: "distinct")
      }

      Module.put_attribute(__MODULE__, :accord_property_checks, [check | checks])
    end
  end

  @doc false
  defmacro reachable(target) do
    line = __CALLER__.line

    quote do
      checks = Module.get_attribute(__MODULE__, :accord_property_checks)

      check = %Check{
        kind: :reachable,
        spec: %{target: unquote(target)},
        span: Pentiment.Span.search(line: unquote(line), pattern: "reachable")
      }

      Module.put_attribute(__MODULE__, :accord_property_checks, [check | checks])
    end
  end

  @doc false
  defmacro forbidden(func) do
    func = Const.substitute(func, __CALLER__.module, __CALLER__.file, __CALLER__.line)
    escaped_ast = Macro.escape(func)
    line = __CALLER__.line

    quote do
      checks = Module.get_attribute(__MODULE__, :accord_property_checks)

      check = %Check{
        kind: :forbidden,
        spec: %{fun: unquote(func), ast: unquote(escaped_ast)},
        span: Pentiment.Span.search(line: unquote(line), pattern: "forbidden")
      }

      Module.put_attribute(__MODULE__, :accord_property_checks, [check | checks])
    end
  end
end
