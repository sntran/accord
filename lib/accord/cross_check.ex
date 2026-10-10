defmodule Accord.CrossCheck do
  @moduledoc """
  Compares the native explorer (`Accord.Explore`) with TLC.

  TLC is the reference. For each protocol, the cross-check runs both
  checkers on the same finite model and compares the results. A
  difference shows a defect in one of the two: in the explorer, or in
  the translation from the protocol to TLA+.

  ## What it compares

  1. The state space. TLC dumps its state graph (`-dump dot`). The
     cross-check compares the set of states, the set of steps between
     them, the distinct state count, and the search depth with the
     explorer. Two models with the same states can still have different
     steps.
  2. The symmetry-reduced state count, for a model with more than one
     session.
  3. Each safety check: `TypeInvariant`, each invariant, each action
     property, and deadlock. For each check, TLC runs with only that
     check. The two verdicts must be the same. When both find a
     violation:
     - the two traces must have the same length (both searches are
       breadth-first, so both traces have the minimum length);
     - the explorer must replay the TLC trace, and the last step must
       violate the check;
     - TLC must replay the explorer trace, and the last step must
       violate the check.

  Liveness properties are not compared. The report lists them as
  skipped.

  A model with more states than `:max_states` is not complete. Then the
  cross-check compares only the checks that the explorer finds violated,
  because TLC stops at the first violation.
  """

  alias Accord.CrossCheck.{TLAValue, TLC}
  alias Accord.Explore
  alias Accord.Explore.Model
  alias Accord.TLA.Compiler

  defmodule Outcome do
    @moduledoc """
    The result of one comparison.

    `status` is `:match`, `:mismatch`, `:inconclusive`, or `:skipped`.
    """
    @type t :: %__MODULE__{
            check: String.t(),
            status: :match | :mismatch | :inconclusive | :skipped,
            detail: String.t()
          }
    @enforce_keys [:check, :status]
    defstruct [:check, :status, detail: ""]
  end

  defmodule Report do
    @moduledoc """
    The cross-check report for one protocol.
    """
    @type t :: %__MODULE__{
            protocol: module(),
            label: String.t() | nil,
            outcomes: [Accord.CrossCheck.Outcome.t()],
            error: String.t() | nil
          }
    @enforce_keys [:protocol]
    defstruct [:protocol, :label, outcomes: [], error: nil]

    @doc "Tells if no comparison found a difference."
    @spec ok?(t()) :: boolean()
    def ok?(%__MODULE__{error: error, outcomes: outcomes}) do
      error == nil and not Enum.any?(outcomes, &(&1.status == :mismatch))
    end

    @doc "Writes the report as text."
    @spec format(t()) :: String.t()
    def format(%__MODULE__{} = report) do
      header =
        if report.label,
          do: "#{inspect(report.protocol)} (#{report.label})",
          else: inspect(report.protocol)

      body =
        if report.error do
          ["  ! #{report.error}"]
        else
          Enum.map(report.outcomes, fn o ->
            mark =
              case o.status do
                :match -> "✓"
                :mismatch -> "✗"
                :inconclusive -> "?"
                :skipped -> "-"
              end

            detail = if o.detail == "", do: "", else: " — " <> o.detail
            "  #{mark} #{o.check}#{detail}"
          end)
        end

      Enum.join([header | body], "\n")
    end
  end

  @doc """
  Cross-checks one protocol module, or one IR with its model config.

  With an IR, the `:config` option is required. The report names the
  protocol by the module name in the IR.

  ## Options

  - `:jar` — the path of `tla2tools.jar`. Default: the same places as
    `mix accord.check`.
  - `:dir` — the work directory. Default: a new temporary directory.
  - `:config` — a `%Accord.TLA.ModelConfig{}` to use.
  - `:max_states` — the state limit of the explorer. Default: 200_000.
  - `:timeout` — the time limit of one TLC run, in seconds. Default: 120.
  - `:label` — a text that the report shows after the protocol name.
  """
  @spec run(module() | Accord.IR.t(), keyword()) :: Report.t()
  def run(protocol, opts \\ [])

  def run(%Accord.IR{} = ir, opts) do
    config = Keyword.get(opts, :config) || raise ArgumentError, "an IR needs the :config option"
    run_ir(ir.name, ir, config, opts)
  end

  def run(protocol, opts) when is_atom(protocol) do
    config = Keyword.get_lazy(opts, :config, fn -> Model.model_config(protocol) end)
    run_ir(protocol, protocol.__ir__(), config, opts)
  end

  defp run_ir(protocol, ir, config, opts) do
    jar = Keyword.get_lazy(opts, :jar, &TLC.find_jar/0) || raise "tla2tools.jar not found"

    with {:ok, compiled} <- compile(ir, config),
         {:ok, model} <- build_model(ir, config) do
      module = compiled.state_space.module_name
      dir = Keyword.get_lazy(opts, :dir, fn -> tmp_dir(module) end)
      File.mkdir_p!(dir)
      File.write!(Path.join(dir, module <> ".tla"), compiled.tla)

      ctx = %{
        protocol: protocol,
        model: model,
        compiled: compiled,
        module: module,
        dir: dir,
        base_cfg: base_cfg(compiled.cfg),
        tlc_opts: [jar: jar, timeout: Keyword.get(opts, :timeout, 120)]
      }

      native =
        Explore.run(model,
          collect_states: true,
          max_states: Keyword.get(opts, :max_states, 200_000)
        )

      outcomes =
        [compare_state_space(ctx, native)] ++
          compare_symmetry(ctx, native) ++
          compare_checks(ctx, native) ++
          skipped(ctx)

      %Report{protocol: protocol, label: opts[:label], outcomes: outcomes}
    else
      {:error, reason} -> %Report{protocol: protocol, label: opts[:label], error: reason}
    end
  end

  defp compile(ir, config) do
    case Compiler.compile(ir, config) do
      {:ok, compiled} ->
        {:ok, compiled}

      {:error, reports} ->
        {:error, "no TLA+ spec: " <> Enum.map_join(reports, "; ", & &1.message)}
    end
  rescue
    e -> {:error, "no TLA+ spec: " <> Exception.message(e)}
  end

  defp build_model(ir, config) do
    {:ok, Model.build(ir, config)}
  rescue
    e in Model.UnsupportedFailure -> {:error, "explorer: " <> Exception.message(e)}
  end

  defp tmp_dir(module) do
    Path.join(
      System.tmp_dir!(),
      "accord_cross_check_#{module}_#{System.os_time()}"
    )
  end

  # The generated config without INVARIANT, PROPERTY, and SYMMETRY lines.
  # Each run adds the lines that it needs.
  defp base_cfg(cfg) do
    cfg
    |> String.split("\n")
    |> Enum.reject(&String.match?(&1, ~r/^(INVARIANT|PROPERTY|SYMMETRY)\b/))
    |> Enum.join("\n")
  end

  defp tlc(ctx, cfg_lines, opts) do
    cfg = ctx.base_cfg <> "\n" <> Enum.join(cfg_lines, "\n") <> "\n"
    TLC.run(ctx.dir, ctx.module <> ".tla", cfg, Keyword.merge(ctx.tlc_opts, opts))
  end

  defp native_error(native), do: Map.get(native.violations, "Error")

  # -- State space --

  defp compare_state_space(ctx, native) do
    check = "state space"

    cond do
      not native.complete ->
        outcome(check, :inconclusive, "the model has more than #{native.distinct - 1} states")

      native_error(native) ->
        tlc = tlc(ctx, [], deadlock: false, name: "space")
        error_outcome(check, native, tlc)

      true ->
        tlc = tlc(ctx, [], deadlock: false, dump: true, name: "space")

        case tlc.status do
          :ok -> state_space_outcome(ctx, native, tlc)
          :timeout -> outcome(check, :inconclusive, "TLC timed out")
          _ -> outcome(check, :mismatch, "TLC: #{tlc_summary(tlc)}")
        end
    end
  end

  defp state_space_outcome(ctx, native, tlc) do
    to_tla = &TLAValue.from_state(ctx.model, &1)
    native_set = MapSet.new(native.states, to_tla)
    tlc_set = MapSet.new(tlc.states)
    only_native = MapSet.difference(native_set, tlc_set)
    only_tlc = MapSet.difference(tlc_set, native_set)

    native_edges =
      MapSet.new(native_edges(ctx.model, native.states), fn {a, b} -> {to_tla.(a), to_tla.(b)} end)

    tlc_edges = MapSet.new(tlc.edges)
    edges_only_native = MapSet.difference(native_edges, tlc_edges)
    edges_only_tlc = MapSet.difference(tlc_edges, native_edges)

    counts =
      "#{native.distinct} states, #{MapSet.size(native_edges)} steps, depth #{native.depth} " <>
        "(TLC: #{tlc.distinct} states, #{MapSet.size(tlc_edges)} steps, depth #{tlc.depth})"

    same? =
      Enum.all?(
        [only_native, only_tlc, edges_only_native, edges_only_tlc],
        &(MapSet.size(&1) == 0)
      ) and
        native.distinct == tlc.distinct and native.depth == tlc.depth

    if same? do
      outcome("state space", :match, counts)
    else
      detail =
        [counts] ++
          sample("states only in the explorer", only_native, &render_vars/1) ++
          sample("states only in TLC", only_tlc, &render_vars/1) ++
          sample("steps only in the explorer", edges_only_native, &render_edge/1) ++
          sample("steps only in TLC", edges_only_tlc, &render_edge/1)

      outcome("state space", :mismatch, Enum.join(detail, "; "))
    end
  end

  # The steps between states inside the constraint. TLC does not dump a
  # step into a state outside the constraint.
  defp native_edges(model, states) do
    for state <- states,
        {_label, next} <- Model.successors(model, state),
        Model.in_model?(model, next),
        uniq: true,
        do: {state, next}
  end

  defp render_edge({from, to}), do: "{#{render_vars(from)}} -> {#{render_vars(to)}}"

  defp sample(label, set, render) do
    if MapSet.size(set) == 0 do
      []
    else
      examples = set |> Enum.take(2) |> Enum.map_join(" | ", render)
      ["#{MapSet.size(set)} #{label}, for example #{examples}"]
    end
  end

  defp render_vars(vars) do
    vars |> Enum.sort() |> Enum.map_join(", ", fn {k, v} -> "#{k} = #{TLAValue.render(v)}" end)
  end

  # -- Symmetry --

  defp compare_symmetry(ctx, native) do
    symmetric? = String.match?(ctx.compiled.cfg, ~r/^SYMMETRY Symmetry/m)

    cond do
      not symmetric? or ctx.model.sessions < 2 ->
        []

      not native.complete or native_error(native) ->
        [outcome("symmetry", :inconclusive, "the full state space is not available")]

      ctx.model.config.symmetry_sets != [] ->
        [outcome("symmetry", :skipped, "model-value symmetry sets are not supported")]

      true ->
        reduced = Explore.run(ctx.model, symmetry: true, deadlock: false)
        tlc = tlc(ctx, ["SYMMETRY Symmetry"], deadlock: false, name: "symmetry")

        counts =
          "#{reduced.distinct} states, depth #{reduced.depth} " <>
            "(TLC: #{tlc.distinct} states, depth #{tlc.depth})"

        status =
          if tlc.status == :ok and tlc.distinct == reduced.distinct and tlc.depth == reduced.depth,
            do: :match,
            else: :mismatch

        [outcome("symmetry", status, counts)]
    end
  end

  # -- Safety checks --

  defp compare_checks(ctx, native) do
    native_checks =
      Enum.map(ctx.model.invariants, &{&1.name, :invariant}) ++
        Enum.map(ctx.model.action_checks, &{&1.name, :action})

    tla_checks = tla_safety_checks(ctx.compiled)

    missing =
      for {name, kind} <- tla_checks, not List.keymember?(native_checks, name, 0) do
        outcome(name, :mismatch, "TLC checks this #{kind}, but the explorer does not")
      end

    extra =
      for {name, kind} <- native_checks, not List.keymember?(tla_checks, name, 0) do
        outcome(name, :mismatch, "the explorer checks this #{kind}, but the TLA+ spec does not")
      end

    compared =
      for {name, kind} <- native_checks, List.keymember?(tla_checks, name, 0) do
        compare_check(ctx, native, name, kind)
      end

    compared ++ [compare_check(ctx, native, "Deadlock", :deadlock)] ++ missing ++ extra
  end

  defp tla_safety_checks(compiled) do
    [{"TypeInvariant", :invariant}] ++
      for prop <- compiled.properties,
          kind = safety_kind(prop),
          kind != nil,
          do: {prop.name, kind}
  end

  defp safety_kind(%{kind: :invariant}), do: :invariant

  defp safety_kind(%{kind: :temporal, formula: formula}) do
    if String.contains?(formula, "~>"), do: nil, else: :action
  end

  defp safety_kind(_), do: nil

  defp skipped(ctx) do
    liveness =
      for prop <- ctx.compiled.properties,
          prop.kind == :temporal,
          String.contains?(prop.formula, "~>") do
        outcome(prop.name, :skipped, "liveness is not compared yet")
      end

    liveness_names = MapSet.new(liveness, & &1.check)

    others =
      for {name, why} <- ctx.model.skipped, not MapSet.member?(liveness_names, name) do
        outcome(name, :skipped, why)
      end

    liveness ++ others
  end

  defp compare_check(ctx, native, name, kind) do
    violation = Map.get(native.violations, name)

    cond do
      violation == nil and native_error(native) ->
        tlc = run_check(ctx, name, kind)
        error_outcome(name, native, tlc)

      violation == nil and not native.complete ->
        outcome(name, :inconclusive, "holds in the first #{native.distinct - 1} states")

      true ->
        tlc = run_check(ctx, name, kind)
        verdict_outcome(ctx, name, kind, violation, tlc)
    end
  end

  defp run_check(ctx, name, :invariant),
    do: tlc(ctx, ["INVARIANT #{name}"], deadlock: false, name: "check_#{name}")

  defp run_check(ctx, name, :action),
    do: tlc(ctx, ["PROPERTY #{name}"], deadlock: false, name: "check_#{name}")

  defp run_check(ctx, _name, :deadlock), do: tlc(ctx, [], deadlock: true, name: "check_deadlock")

  defp verdict_outcome(ctx, name, kind, violation, tlc) do
    case {violation, tlc.status} do
      {_, :timeout} ->
        outcome(name, :inconclusive, "TLC timed out")

      {_, :error} ->
        outcome(name, :mismatch, "TLC reports an error: #{first_line(tlc.message)}")

      {nil, :ok} ->
        outcome(name, :match, "holds")

      {nil, :violated} ->
        replay = replay_in_explorer(ctx, name, kind, tlc.trace)

        outcome(
          name,
          :mismatch,
          "TLC finds a violation in #{length(tlc.trace)} states, the explorer does not " <>
            "(explorer replay of the TLC trace: #{replay_text(replay)})"
        )

      {violation, :ok} ->
        replay = replay_in_tlc(ctx, name, kind, violation.trace)

        outcome(
          name,
          :mismatch,
          "the explorer finds a violation in #{length(violation.trace)} states, TLC does not " <>
            "(TLC replay of the explorer trace: #{replay_text(replay)})"
        )

      {violation, :violated} ->
        both_violated(ctx, name, kind, violation, tlc)
    end
  end

  # TLC gives no trace for an invariant that is a constant FALSE. Then the
  # explorer trace must be the initial state alone.
  defp both_violated(ctx, name, kind, violation, %{constant: true}) do
    in_tlc = replay_in_tlc(ctx, name, kind, violation.trace)

    cond do
      length(violation.trace) != 1 ->
        outcome(
          name,
          :mismatch,
          "TLC: constant FALSE, but the explorer trace has #{length(violation.trace)} states"
        )

      in_tlc != :ok ->
        outcome(name, :mismatch, "TLC: constant FALSE, TLC replay: #{replay_text(in_tlc)}")

      true ->
        outcome(name, :match, "constant FALSE, violated in the initial state")
    end
  end

  defp both_violated(ctx, name, kind, violation, tlc) do
    native_len = length(violation.trace)
    tlc_len = length(tlc.trace)
    in_explorer = replay_in_explorer(ctx, name, kind, tlc.trace)
    in_tlc = replay_in_tlc(ctx, name, kind, violation.trace)

    problems =
      if(native_len != tlc_len,
        do: ["trace length #{native_len} (TLC: #{tlc_len})"],
        else: []
      ) ++
        if(in_explorer != :ok, do: ["explorer replay: #{replay_text(in_explorer)}"], else: []) ++
        if in_tlc != :ok, do: ["TLC replay: #{replay_text(in_tlc)}"], else: []

    if problems == [] do
      outcome(name, :match, "violated in #{native_len} states, both traces replay")
    else
      outcome(name, :mismatch, "violated in both, but " <> Enum.join(problems, "; "))
    end
  end

  # When the explorer stops at an evaluation error, TLC must report an
  # error too.
  defp error_outcome(check, native, tlc) do
    error = native_error(native)

    case tlc.status do
      :error ->
        outcome(check, :match, "both report an evaluation error")

      :timeout ->
        outcome(check, :inconclusive, "TLC timed out")

      _ ->
        outcome(
          check,
          :mismatch,
          "the explorer stops at an evaluation error (#{first_line(error.message)}), " <>
            "TLC: #{tlc_summary(tlc)}"
        )
    end
  end

  defp tlc_summary(%{status: :ok}), do: "no error"
  defp tlc_summary(%{status: :timeout}), do: "timeout"
  defp tlc_summary(%{status: :error, message: m}), do: "error: #{first_line(m)}"

  defp tlc_summary(%{status: :violated} = tlc),
    do: "#{tlc.kind} #{tlc.property} in #{length(tlc.trace)} states"

  defp first_line(nil), do: ""
  defp first_line(text), do: text |> String.split("\n") |> hd()

  defp outcome(check, status, detail), do: %Outcome{check: check, status: status, detail: detail}

  # -- Replay of a TLC trace in the explorer --

  @doc false
  @spec replay_in_explorer(map(), String.t(), atom(), [map()]) :: :ok | {:error, String.t()}
  def replay_in_explorer(ctx, name, kind, [first | rest]) do
    model = ctx.model

    with {:ok, init} <- find_state(model, Model.init_states(model), first.vars, 1),
         {:ok, path} <- follow(model, [init], rest, 2) do
      final_check(model, name, kind, path)
    end
  rescue
    e -> {:error, "explorer error: #{Exception.message(e)}"}
  end

  def replay_in_explorer(_ctx, _name, _kind, []), do: {:error, "empty TLC trace"}

  defp follow(_model, path, [], _index), do: {:ok, path}

  defp follow(model, [current | _] = path, [step | rest], index) do
    candidates = model |> Model.successors(current) |> Enum.map(&elem(&1, 1))

    case find_state(model, candidates, step.vars, index) do
      {:ok, next} -> follow(model, [next | path], rest, index + 1)
      error -> error
    end
  end

  defp find_state(model, candidates, vars, index) do
    case Enum.find(candidates, &(TLAValue.from_state(model, &1) == vars)) do
      nil -> {:error, "no explorer step makes state #{index}: #{render_vars(vars)}"}
      state -> {:ok, state}
    end
  end

  # `path` is in reverse order: the last state is first.
  defp final_check(model, name, :invariant, [last | _]) do
    check = Enum.find(model.invariants, &(&1.name == name))
    if check.fun.(last), do: {:error, "the last state does not violate #{name}"}, else: :ok
  end

  defp final_check(model, name, :action, [last, prev | _]) do
    check = Enum.find(model.action_checks, &(&1.name == name))
    if check.fun.(prev, last), do: {:error, "the last step does not violate #{name}"}, else: :ok
  end

  defp final_check(model, _name, :deadlock, [last | _]) do
    case Model.successors(model, last) do
      [] -> :ok
      _ -> {:error, "the last state has successors in the explorer"}
    end
  end

  defp final_check(_model, name, _kind, _path), do: {:error, "the trace is too short for #{name}"}

  # -- Replay of an explorer trace in TLC --

  @doc false
  @spec replay_in_tlc(map(), String.t(), atom(), [map()]) :: :ok | {:error, String.t()}
  def replay_in_tlc(ctx, name, kind, trace) do
    replay = ctx.module <> "Replay"
    states = Enum.map(trace, &TLAValue.from_state(ctx.model, &1.state))

    case replay_check(ctx, name, kind) do
      {:ok, check_def, cfg_line} ->
        File.write!(
          Path.join(ctx.dir, replay <> ".tla"),
          replay_module(ctx, replay, states, check_def)
        )

        cfg =
          ["INIT ReplayInit", "NEXT ReplayNext", cfg_line] ++ constant_lines(ctx.compiled.cfg)

        run =
          TLC.run(ctx.dir, replay <> ".tla", Enum.join(cfg, "\n") <> "\n",
            jar: ctx.tlc_opts[:jar],
            timeout: ctx.tlc_opts[:timeout],
            deadlock: false,
            name: "replay_#{name}"
          )

        cond do
          run.status == :violated and length(run.trace) == length(states) -> :ok
          run.status == :ok -> {:error, "TLC cannot replay the trace to the violation"}
          true -> {:error, "TLC: #{tlc_summary(run)}"}
        end

      {:error, _} = error ->
        error
    end
  end

  defp replay_check(_ctx, name, :invariant) do
    {:ok, "ReplayCheck == ~(replay_i = Len(ReplayTrace) /\\ ~(#{name}))", "INVARIANT ReplayCheck"}
  end

  defp replay_check(_ctx, _name, :deadlock) do
    {:ok, "ReplayCheck == ~(replay_i = Len(ReplayTrace) /\\ ~(ENABLED Next))",
     "INVARIANT ReplayCheck"}
  end

  defp replay_check(ctx, name, :action) do
    prop = Enum.find(ctx.compiled.properties, &(&1.name == name))

    case Regex.run(~r/^\w+\s*==\s*\[\]\[(.*)\]_(<<.*>>)\s*$/s, prop.formula) do
      [_, body, sub] ->
        {:ok,
         "ReplayCheck == [][~(replay_i' = Len(ReplayTrace) /\\ (#{sub})' /= #{sub} /\\ ~(#{body}))]_<<vars, replay_i>>",
         "PROPERTY ReplayCheck"}

      nil ->
        {:error, "cannot read the action property #{name}"}
    end
  end

  defp replay_module(ctx, replay, states, check_def) do
    vars = Enum.map(ctx.compiled.state_space.variables, & &1.name)

    records =
      Enum.map_join(states, ",\n    ", fn state ->
        "[" <>
          Enum.map_join(vars, ", ", &"#{&1} |-> #{TLAValue.render(Map.fetch!(state, &1))}") <> "]"
      end)

    init = Enum.map_join(vars, " /\\ ", &"#{&1} = ReplayTrace[1].#{&1}")
    next = Enum.map_join(vars, " /\\ ", &"#{&1}' = ReplayTrace[replay_i + 1].#{&1}")

    """
    ---- MODULE #{replay} ----
    EXTENDS #{ctx.module}, Integers, Sequences, TLC

    VARIABLE replay_i

    ReplayTrace == <<
        #{records}
    >>

    ReplayInit == Init /\\ replay_i = 1 /\\ #{init}

    ReplayNext ==
        /\\ replay_i < Len(ReplayTrace)
        /\\ Next
        /\\ replay_i' = replay_i + 1
        /\\ #{next}

    #{check_def}
    ====
    """
  end

  defp constant_lines(cfg) do
    cfg |> String.split("\n") |> Enum.filter(&String.starts_with?(&1, "CONSTANT"))
  end

  defp replay_text(:ok), do: "ok"
  defp replay_text({:error, reason}), do: reason
end
