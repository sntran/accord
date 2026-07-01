defmodule Accord.Protocol.ModelBlock do
  @moduledoc """
  Macros available inside `model do ... end` blocks.

  Each entry accumulates into the protocol's inline model configuration,
  which has the highest resolution precedence (see
  `Accord.TLA.ModelConfig.apply_inline/2`). Keeping domains next to the
  protocol they bound means editing them recompiles the protocol and the
  spec can never go stale against a forgotten external file.
  """

  @doc false
  # Number of interleaved sessions TLC explores (see ADR-009).
  defmacro sessions(count) do
    quote do
      Module.put_attribute(__MODULE__, :accord_model, {:sessions, unquote(count)})
    end
  end

  @doc false
  # Finite domain for a parameter or type name.
  defmacro domain(name, spec) do
    quote do
      Module.put_attribute(
        __MODULE__,
        :accord_model,
        {:domain, {unquote(name), unquote(spec)}}
      )
    end
  end

  @doc false
  # Maximum length used when abstracting list-typed replies.
  defmacro max_list_length(n) do
    quote do
      Module.put_attribute(__MODULE__, :accord_model, {:max_list_length, unquote(n)})
    end
  end

  @doc false
  # Raw TLA+ state constraint for bounded checking.
  defmacro state_constraint(expr) do
    quote do
      Module.put_attribute(__MODULE__, :accord_model, {:state_constraint, unquote(expr)})
    end
  end
end
