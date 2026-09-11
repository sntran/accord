defmodule Accord.TLA.Sessions do
  @moduledoc """
  Session context for multi-session TLA+ emission.

  With `sessions: N` (N >= 2) in the model config, TLC explores N
  interleaved client sessions against one server: per-session variables
  (the state machine, non-shared tracks, correspondence counters) become
  functions `[Sessions -> Domain]`, shared tracks stay scalar, and every
  action existentially quantifies the acting session. This is where the
  concurrency bugs live — mutual-exclusion violations, fencing races —
  that a single-session model structurally cannot represent.

  `count: 1` (the default) must leave emission byte-identical to the
  unsessioned output; every multi-session path is gated on `multi?/1`.
  """

  alias Accord.IR

  @type t :: %__MODULE__{
          count: pos_integer(),
          var: String.t(),
          per_session: MapSet.t(String.t()) | nil
        }

  # per_session defaults to nil (not MapSet.new/0) so the struct default
  # is not a compile-time literal of an opaque type; every accessor
  # short-circuits on multi?/1 before touching it, and build/3 always
  # sets a real set.
  # Defaults describe the single-session case; build/3 fills the rest.
  @enforce_keys []
  defstruct count: 1, var: "s", per_session: nil

  @doc """
  Builds the session context from the IR and the configured count.

  Per-session variables: `state`, non-shared tracks, and correspondence
  counters (each monitor instance counts its own session's traffic).
  """
  @spec build(IR.t(), pos_integer(), [String.t()]) :: t()
  def build(%IR{} = ir, count, counter_vars) do
    per_session =
      ["state"] ++
        for(track <- ir.tracks, not track.shared, do: Atom.to_string(track.name)) ++
        counter_vars

    %__MODULE__{count: count, per_session: MapSet.new(per_session)}
  end

  @spec multi?(t()) :: boolean()
  def multi?(%__MODULE__{count: count}), do: count > 1

  @doc """
  The session model value names: `["s1", "s2", ...]`.
  """
  @spec values(t()) :: [String.t()]
  def values(%__MODULE__{count: count}) do
    for i <- 1..count, do: "s#{i}"
  end

  @doc """
  Reads a variable in the acting session: `state[s]` for per-session
  variables, the bare name for shared ones. Single-session: bare names.
  """
  @spec read(t(), String.t()) :: String.t()
  def read(%__MODULE__{} = sessions, var_name) do
    if multi?(sessions) and MapSet.member?(sessions.per_session, var_name) do
      "#{var_name}[#{sessions.var}]"
    else
      var_name
    end
  end

  @doc """
  A primed read: `state'[s]` / `state'` / `fence'`.
  """
  @spec read_primed(t(), String.t()) :: String.t()
  def read_primed(%__MODULE__{} = sessions, var_name) do
    if multi?(sessions) and MapSet.member?(sessions.per_session, var_name) do
      "#{var_name}'[#{sessions.var}]"
    else
      "#{var_name}'"
    end
  end

  @doc """
  A primed assignment value: per-session variables update via EXCEPT
  (`[state EXCEPT ![s] = expr]`), shared ones assign directly.
  """
  @spec assign(t(), String.t(), String.t()) :: String.t()
  def assign(%__MODULE__{} = sessions, var_name, value_expr) do
    if multi?(sessions) and MapSet.member?(sessions.per_session, var_name) do
      "[#{var_name} EXCEPT ![#{sessions.var}] = #{value_expr}]"
    else
      value_expr
    end
  end

  @doc """
  The field renderer for `Accord.TLA.GuardCompiler` — renders track
  accesses in the acting session.
  """
  @spec render_field(t()) :: (String.t(), boolean() -> String.t())
  def render_field(%__MODULE__{} = sessions) do
    fn
      field, false -> read(sessions, field)
      field, true -> read_primed(sessions, field)
    end
  end

  @doc """
  Universally quantifies a formula over sessions (multi only).

  Quantifying an expression that mentions only shared variables is
  redundant but sound (Sessions is non-empty), so callers quantify
  unconditionally when multi.
  """
  @spec forall(t(), String.t()) :: String.t()
  def forall(%__MODULE__{} = sessions, body) do
    if multi?(sessions) do
      "\\A #{sessions.var} \\in Sessions : (#{body})"
    else
      body
    end
  end
end
