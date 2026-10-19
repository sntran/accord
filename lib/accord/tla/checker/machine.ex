defmodule Accord.TLA.Checker.Machine do
  @moduledoc """
  Runs a TLA+ specification one step at a time, for a runtime monitor.

  The model checker explores all the states of a model. A monitor does a
  different thing: it follows one run of a real system. Each message of
  the system names an action of the specification, with arguments. The
  machine finds the next states that the action allows from the current
  states, with the rules of TLC (see `Accord.TLA.Checker.Eval`).

  The machine keeps a set of states, not one state: a specification can
  allow more than one next state for the same action and arguments (a
  nondeterministic choice that the messages do not show). The set becomes
  empty when the run is not a behavior of the specification.

  ## Open parameters

  `step/5` can leave the last parameter of the action open (option
  `open: true`). The action then gives the values of that parameter, as
  it gives the values of the primed variables: `r = "ok"` or
  `r \\in {"ok", "busy"}` assigns `r` when `r` has no value yet. A monitor
  uses this to find the replies that the specification allows.
  """

  alias Accord.TLA.Checker
  alias Accord.TLA.Checker.{Context, Eval, Spec, Value}

  defstruct [:ctx, :init, :invariants, :path]

  @type state :: tuple()
  @type t :: %__MODULE__{}

  @doc """
  Loads the module in `path`.

  Options:

  - `:config` — the `.cfg` file (default: the module path with the
    extension `.cfg`, else a `CONFIG` section of the module file, else no
    config).
  - `:paths` — more directories to search for modules.

  Without `INIT` or `SPECIFICATION` in the config, the initial predicate
  is `Init`.
  """
  @spec load(Path.t(), keyword()) :: {:ok, t()} | {:error, String.t()}
  def load(path, opts \\ []) do
    with {:ok, ctx} <- Checker.context(path, opts) do
      setup_process(ctx)

      try do
        config = ctx.config

        init =
          if config.specification || (config.init && config.next) do
            Spec.analyze(ctx, config).init
          else
            [root_closure(ctx, config.init || "Init")]
          end

        invariants = Enum.map(config.invariants, &{&1, root_closure(ctx, &1)})
        {:ok, %__MODULE__{ctx: ctx, init: init, invariants: invariants, path: path}}
      rescue
        e in [Value.Error, Context.Error] -> {:error, Exception.message(e)}
      end
    else
      {:error, _kind, message} -> {:error, message}
    end
  end

  defp root_closure(ctx, name) do
    if Context.root_entry(ctx, name) == nil,
      do: raise(Value.Error, message: "the module has no definition #{name}")

    {{:name, name, nil}, ctx.root, %{}, %{}}
  end

  defp setup_process(ctx) do
    Process.put(:tla_registers, Process.get(:tla_registers) || %{})
    Process.put(:tla_properties, Process.get(:tla_properties) || %{})
    Process.put(:tla_warn, true)
    Process.put(:tla_deadlock, ctx.config.check_deadlock)
    Eval.reset_cache()
  end

  @doc "The initial states."
  @spec init_states(t()) :: {:ok, [state()]} | {:error, String.t()}
  def init_states(%__MODULE__{} = m) do
    guarded(m, fn ->
      env = %{Eval.new(m.ctx) | state: %{}, label: "Init", level: 0}

      m.init
      |> Enum.reduce([%{}], fn {e, scope, bound, frames}, acc ->
        Enum.flat_map(acc, fn p ->
          e
          |> Eval.gen(%{env | scope: scope, bound: bound, frames: frames, state: p}, :init)
          |> Enum.map(&elem(&1, 0))
        end)
      end)
      |> Enum.map(&complete!(m, &1, "the initial predicate"))
      |> Enum.uniq()
    end)
  end

  @doc """
  Tells the arity of the action `name`, or `nil` when the module has no
  operator definition with that name.
  """
  @spec arity(t(), String.t()) :: non_neg_integer() | nil
  def arity(%__MODULE__{ctx: ctx}, name) do
    case definition(ctx, name) do
      {:ok, d, _sid} -> length(d.params)
      :error -> nil
    end
  end

  @doc """
  The steps of the action `name` with the arguments `args` (TLA+ values)
  from the state `state`.

  Gives `{:ok, [{next_state, open_value}]}`; `open_value` is the value of
  the open parameter (option `open: true`; then `args` has one value less
  than the action has parameters), else `nil`.
  """
  @spec step(t(), state(), String.t(), [term()], keyword()) ::
          {:ok, [{state(), term()}]} | {:error, String.t()}
  def step(%__MODULE__{ctx: ctx} = m, state, name, args, opts \\ []) do
    open? = Keyword.get(opts, :open, false)

    guarded(m, fn ->
      {d, sid} =
        case definition(ctx, name) do
          {:ok, d, sid} -> {d, sid}
          :error -> raise Value.Error, message: "the module has no action #{name}"
        end

      params = Enum.map(d.params, &elem(&1, 0))
      want = length(args) + if(open?, do: 1, else: 0)

      if want != length(params),
        do:
          raise(Value.Error,
            message: "the action #{name} has #{length(params)} parameters, not #{want}"
          )

      values = Enum.map(args, &Value.canon/1)
      values = if open?, do: values ++ [{:free_param, List.last(params)}], else: values
      bound = Map.new(Enum.zip(params, values))

      env = %{
        Eval.new(ctx)
        | scope: sid,
          bound: bound,
          state: state,
          next: %{},
          label: name
      }

      key = if open?, do: {:free_param, List.last(params)}

      d.body
      |> Eval.gen(env, :next)
      |> Enum.map(fn {p, _label} ->
        {open_value, p} = if key, do: Map.pop(p, key), else: {nil, p}

        if key && open_value == nil,
          do:
            raise(Value.Error,
              message: "the action #{name} does not give a value to #{List.last(params)}"
            )

        {complete!(m, p, "the action #{name}"), open_value}
      end)
      |> Enum.uniq()
    end)
  end

  defp definition(ctx, name) do
    case Context.root_entry(ctx, name) do
      {:def, %{kind: :op} = d, sid} -> {:ok, d, sid}
      {:alias, sid, target} -> definition(%{ctx | root: sid}, target)
      _ -> :error
    end
  end

  @doc """
  The first invariant of the config that is false in `state`, or `:ok`.
  """
  @spec check_invariants(t(), state()) :: :ok | {:violated, String.t()} | {:error, String.t()}
  def check_invariants(%__MODULE__{} = m, state) do
    result =
      guarded(m, fn ->
        Enum.find_value(m.invariants, :ok, fn {name, {e, scope, bound, frames}} ->
          env = %{Eval.new(m.ctx) | state: state, scope: scope, bound: bound, frames: frames}
          if Eval.bool(e, env), do: nil, else: {:violated, name}
        end)
      end)

    case result do
      {:ok, r} -> r
      error -> error
    end
  end

  @doc "The state as a map from variable names to TLA+ values."
  @spec to_map(t(), state()) :: %{String.t() => term()}
  def to_map(%__MODULE__{ctx: ctx}, state) do
    ctx.variables
    |> Tuple.to_list()
    |> Enum.with_index()
    |> Map.new(fn {name, i} -> {name, elem(state, i)} end)
  end

  @doc """
  The model values of the config (`{:mv, name}`), by name. A monitor
  maps an Elixir atom to the model value with the same name.
  """
  @spec model_values(t()) :: %{String.t() => term()}
  def model_values(%__MODULE__{ctx: ctx}) do
    ctx.constants
    |> Map.values()
    |> Enum.flat_map(&collect_model_values/1)
    |> Map.new(fn {:mv, name} = v -> {name, v} end)
  end

  defp collect_model_values({:mv, _} = v), do: [v]
  defp collect_model_values(%MapSet{} = s), do: Enum.flat_map(s, &collect_model_values/1)

  defp collect_model_values({:seq, t}),
    do: t |> Tuple.to_list() |> Enum.flat_map(&collect_model_values/1)

  defp collect_model_values({:fun, map}),
    do: Enum.flat_map(map, fn {k, v} -> collect_model_values(k) ++ collect_model_values(v) end)

  defp collect_model_values(_), do: []

  defp complete!(m, p, what) do
    nvars = tuple_size(m.ctx.variables)

    if map_size(p) == nvars do
      List.to_tuple(for i <- 0..(nvars - 1)//1, do: Map.fetch!(p, i))
    else
      missing = for i <- 0..(nvars - 1)//1, not Map.has_key?(p, i), do: elem(m.ctx.variables, i)

      raise Value.Error,
        message:
          "#{what} does not give a value to all the variables. These variables have no value: #{Enum.join(missing, ", ")}."
    end
  end

  defp guarded(m, fun) do
    setup_process(m.ctx)
    {:ok, fun.()}
  rescue
    e in [Value.Error, Context.Error] -> {:error, Exception.message(e)}
  end
end
