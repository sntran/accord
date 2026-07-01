defmodule Accord.Protocol.Const do
  @moduledoc """
  Macro-time substitution for protocol constants.

  A threshold that appears in a guard, an update, and an invariant must
  stay in sync — `const :threshold, 3` declares it once, and
  `const(:threshold)` references it anywhere a user expression is
  captured (guards, updates, `where:` constraints, property functions,
  `bounded` maxima, timeouts).

  Substitution happens before the expression is compiled or escaped, so
  the runtime closure and the TLA+ spec both see the literal — one
  source of truth, zero runtime machinery.
  """

  @doc """
  Replaces `const(:name)` calls in the AST with their declared values.

  Raises `CompileError` for references to undeclared constants.
  """
  @spec substitute(Macro.t(), module(), String.t(), pos_integer()) :: Macro.t()
  def substitute(ast, module, file, line) do
    consts = Module.get_attribute(module, :accord_consts) || []

    Macro.prewalk(ast, fn
      {:const, _meta, [name]} when is_atom(name) ->
        case List.keyfind(consts, name, 0) do
          {^name, value} ->
            value

          nil ->
            known =
              case consts do
                [] -> "no constants are declared"
                consts -> "declared: #{Enum.map_join(consts, ", ", fn {n, _} -> ":#{n}" end)}"
              end

            raise CompileError,
              description: "unknown protocol constant :#{name} — #{known}",
              file: file,
              line: line
        end

      other ->
        other
    end)
  end

  @doc """
  Validates and registers a constant declaration.

  Called from the `const/2` macro at module-body evaluation time.
  """
  @spec register(module(), atom(), term(), String.t(), pos_integer()) :: :ok
  def register(module, name, value, file, line) do
    unless is_integer(value) or is_atom(value) or is_binary(value) or is_boolean(value) do
      raise CompileError,
        description:
          "const :#{name} must be a literal (integer, atom, string, or boolean), " <>
            "got: #{inspect(value)}",
        file: file,
        line: line
    end

    consts = Module.get_attribute(module, :accord_consts) || []

    if List.keymember?(consts, name, 0) do
      raise CompileError,
        description: "duplicate protocol constant :#{name}",
        file: file,
        line: line
    end

    Module.put_attribute(module, :accord_consts, [{name, value} | consts])
    :ok
  end
end
