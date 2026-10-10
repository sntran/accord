defmodule Accord.Explore do
  @moduledoc """
  A native explicit-state model checker for Accord protocols.

  The explorer does a breadth-first search over `Accord.Explore.Model`.
  It does not use Java or TLC. It checks the same safety properties as
  the generated TLA+ spec:

  - `TypeInvariant`, and each invariant, local invariant, forbidden,
    bounded, correspondence, exclusive, and distinct check.
  - Each action property, on each step that changes a track.
  - Deadlock: a state with no successor.

  The search follows the rules of TLC, so that the two checkers give the
  same results:

  - A state outside the state constraint is not explored and not
    counted. The invariants are still checked on it.
  - Action properties are checked on all steps, also on steps into a
    state outside the constraint.
  - A state is a deadlock only if it has no successor at all.
  - For each property, the search keeps the first violation. Because the
    search is breadth-first, this trace has the minimum length.

  Liveness is not checked yet. The result lists each check that the
  explorer did not do in `skipped`.

  ## Example

      result = Accord.Explore.run(MyApp.Protocol)
      result.violations["TypeInvariant"]
  """

  alias Accord.Explore.Model
  alias Accord.Explore.Model.EvaluationFailure

  defmodule Result do
    @moduledoc """
    The result of an exploration.

    - `distinct` — the number of distinct states in the model (inside the
      state constraint).
    - `depth` — the number of breadth-first levels.
    - `violations` — a map from check name to the first violation.
      A violation has `kind` (`:invariant`, `:action`, `:deadlock`, or
      `:error`), `name`, `message`, and `trace`.
    - `checked` — the names of the checks that the explorer did.
    - `skipped` — `{name, reason}` for each check that it did not do.
    - `states` — all distinct states, when `collect_states: true`.
    - `complete` — false when the search stopped at `max_states`.
    """

    @type step :: %{state: Model.state(), label: Model.label() | nil}

    @type violation :: %{
            kind: :invariant | :action | :deadlock | :error,
            name: String.t(),
            message: String.t() | nil,
            trace: [step()]
          }

    @type t :: %__MODULE__{
            distinct: non_neg_integer(),
            depth: non_neg_integer(),
            violations: %{String.t() => violation()},
            checked: [String.t()],
            skipped: [{String.t(), String.t()}],
            states: [Model.state()] | nil,
            complete: boolean(),
            model: Model.t()
          }

    @enforce_keys [:model]
    defstruct distinct: 0,
              depth: 0,
              violations: %{},
              checked: [],
              skipped: [],
              states: nil,
              complete: true,
              model: nil

    @doc "Tells if the exploration found no violation."
    @spec ok?(t()) :: boolean()
    def ok?(%__MODULE__{violations: violations, complete: complete}),
      do: complete and violations == %{}
  end

  @doc """
  Explores a protocol.

  `protocol` is a protocol module or an `Accord.Explore.Model`.

  ## Options

  - `:symmetry` — when true, two states that differ only in the order of
    the sessions count as one state. Traces are not kept. Default: false.
  - `:deadlock` — when false, do not check for deadlock. Default: true.
  - `:collect_states` — when true, put all states in the result.
  - `:stop` — `:never` (default) checks all properties to the end.
    `:first` stops at the first violation, as TLC does.
  - `:max_states` — stop after this number of distinct states.
    Default: 1_000_000.
  - `:config` — a `%Accord.TLA.ModelConfig{}` to use instead of the
    config of the protocol.
  """
  @spec run(module() | Model.t(), keyword()) :: Result.t()
  def run(protocol, opts \\ [])

  def run(%Model{} = model, opts), do: explore(model, opts)

  def run(protocol, opts) when is_atom(protocol) do
    protocol |> Model.build(Keyword.get(opts, :config)) |> explore(opts)
  end

  defp explore(model, opts) do
    symmetry = Keyword.get(opts, :symmetry, false)
    deadlock = Keyword.get(opts, :deadlock, true)
    stop = Keyword.get(opts, :stop, :never)
    max_states = Keyword.get(opts, :max_states, 1_000_000)
    key = if symmetry, do: &Model.canonical/1, else: & &1

    ctx = %{
      model: model,
      key: key,
      symmetry: symmetry,
      deadlock: deadlock,
      stop: stop,
      max_states: max_states
    }

    # `seen` maps a state key to {parent_key, label, depth}. The state of
    # the parent is the key itself when symmetry is off.
    acc = %{
      seen: %{},
      queue: :queue.new(),
      violations: %{},
      depth: 0,
      halted: false,
      truncated: false
    }

    acc =
      Enum.reduce(Model.init_states(model), acc, fn state, acc ->
        visit(ctx, acc, state, nil, nil, 0)
      end)

    acc = loop(ctx, acc)

    checked =
      Enum.map(model.invariants ++ model.action_checks, & &1.name) ++
        if(deadlock, do: ["Deadlock"], else: [])

    %Result{
      distinct: map_size(acc.seen),
      depth: acc.depth,
      violations: acc.violations,
      checked: checked,
      skipped: model.skipped,
      states: if(Keyword.get(opts, :collect_states, false), do: Map.keys(acc.seen)),
      complete: not acc.truncated,
      model: model
    }
  end

  defp loop(ctx, acc) do
    cond do
      acc.halted ->
        acc

      map_size(acc.seen) > ctx.max_states ->
        %{acc | halted: true, truncated: true}

      true ->
        case :queue.out(acc.queue) do
          {:empty, _} -> acc
          {{:value, state_key}, queue} -> loop(ctx, expand(ctx, %{acc | queue: queue}, state_key))
        end
    end
  end

  defp expand(ctx, acc, state_key) do
    {_parent, _label, depth} = Map.fetch!(acc.seen, state_key)
    state = state_key

    case safe_successors(ctx.model, state) do
      {:error, error} ->
        trace = trace_to(ctx, acc, state_key, error.label, state)
        acc |> record(ctx, "Error", :error, Exception.message(error), trace) |> halt()

      {:ok, []} ->
        if ctx.deadlock do
          record(acc, ctx, "Deadlock", :deadlock, nil, trace(ctx, acc, state_key))
        else
          acc
        end

      {:ok, successors} ->
        Enum.reduce_while(successors, acc, fn {label, next}, acc ->
          acc = check_actions(ctx, acc, state_key, state, label, next)
          acc = visit(ctx, acc, next, state_key, label, depth)
          if acc.halted, do: {:halt, acc}, else: {:cont, acc}
        end)
    end
  end

  defp safe_successors(model, state) do
    {:ok, Model.successors(model, state)}
  rescue
    e in EvaluationFailure -> {:error, e}
  end

  # Checks a new state: the invariants, then (if it is inside the
  # constraint and new) adds it to the search.
  defp visit(ctx, acc, state, parent_key, label, parent_depth) do
    key = ctx.key.(state)
    in_model = Model.in_model?(ctx.model, state)
    new = not Map.has_key?(acc.seen, key)

    acc =
      if in_model and new do
        seen = Map.put(acc.seen, key, {parent_key, label, parent_depth + 1})

        %{
          acc
          | seen: seen,
            queue: :queue.in(key, acc.queue),
            depth: max(acc.depth, parent_depth + 1)
        }
      else
        acc
      end

    if new or not in_model do
      check_invariants(ctx, acc, state, parent_key, label)
    else
      acc
    end
  end

  defp check_invariants(ctx, acc, state, parent_key, label) do
    Enum.reduce_while(ctx.model.invariants, acc, fn check, acc ->
      acc =
        if Map.has_key?(acc.violations, check.name) do
          acc
        else
          case safe_check(fn -> check.fun.(state) end) do
            :ok ->
              acc

            {:violated, message} ->
              trace = trace_to(ctx, acc, parent_key, label, state)
              record(acc, ctx, check.name, :invariant, message, trace)

            {:error, message} ->
              trace = trace_to(ctx, acc, parent_key, label, state)
              acc |> record(ctx, "Error", :error, message, trace) |> halt()
          end
        end

      if acc.halted, do: {:halt, acc}, else: {:cont, acc}
    end)
  end

  defp check_actions(ctx, acc, state_key, state, label, next) do
    Enum.reduce(ctx.model.action_checks, acc, fn check, acc ->
      if Map.has_key?(acc.violations, check.name) or acc.halted do
        acc
      else
        case safe_check(fn -> check.fun.(state, next) end) do
          :ok ->
            acc

          {:violated, message} ->
            trace = trace_to(ctx, acc, state_key, label, next)
            record(acc, ctx, check.name, :action, message, trace)

          {:error, message} ->
            trace = trace_to(ctx, acc, state_key, label, next)
            acc |> record(ctx, "Error", :error, message, trace) |> halt()
        end
      end
    end)
  end

  defp safe_check(fun) do
    if fun.(), do: :ok, else: {:violated, nil}
  rescue
    e -> {:error, Exception.message(e)}
  end

  defp record(acc, ctx, name, kind, message, trace) do
    if Map.has_key?(acc.violations, name) do
      acc
    else
      violation = %{kind: kind, name: name, message: message, trace: trace}
      acc = %{acc | violations: Map.put(acc.violations, name, violation)}
      if ctx.stop == :first, do: halt(acc), else: acc
    end
  end

  defp halt(acc), do: %{acc | halted: true}

  # -- Traces --

  defp trace_to(%{symmetry: true}, _acc, _parent_key, _label, _state), do: []
  defp trace_to(_ctx, _acc, nil, _label, state), do: [step(state, nil)]

  defp trace_to(ctx, acc, parent_key, label, state),
    do: trace(ctx, acc, parent_key) ++ [step(state, label)]

  # Symmetry keeps only one state of each class, so the parent chain is
  # not a valid behavior. Traces are not kept in that mode.
  defp trace(%{symmetry: true}, _acc, _key), do: []

  defp trace(_ctx, acc, key), do: build_trace(acc.seen, key, [])

  defp build_trace(_seen, nil, steps), do: steps

  defp build_trace(seen, key, steps) do
    {parent, label, _depth} = Map.fetch!(seen, key)
    build_trace(seen, parent, [step(key, label) | steps])
  end

  defp step(state, label), do: %{state: state, label: label}
end
