defmodule Accord.Explore.Model do
  @moduledoc """
  An executable model of a protocol, made from the IR and a model config.

  The model runs the same Elixir functions as the runtime monitor:
  guards, updates, `where:` constraints, and property checks. It does not
  read the generated TLA+ spec. It uses only the finite domains of the
  model config, so it explores the same finite model as TLC.

  ## Semantics

  The model follows the runtime monitor, with these declared
  abstractions (the same ones that the TLA+ model uses):

  - Message arguments and reply values come from the model domains.
  - A list in a reply is a list of placeholder values. Its length is in
    `0..max_list_length`.
  - A state timeout can fire at any time while its state is active.
  - A plain cast (no `goto`, no branches) is a step that changes nothing.
  - A session in a terminal state stays there. When all sessions are in
    terminal states, the model can stay in the same state.
  - With `sessions: N`, the model has N sessions. Shared tracks have one
    value for all sessions. All other tracks, the state, and the
    correspondence counters have one value for each session.

  A call reply selects the first branch whose reply type matches and
  whose `where:` constraint holds. This is the rule of the monitor.

  ## State

  A model state is `{sessions, shared}`. `sessions` is a tuple with one
  `{state_name, tracks, counters}` entry for each session. `shared` is a
  map of the shared tracks.
  """

  alias Accord.IR
  alias Accord.IR.{Branch, Transition}
  alias Accord.TLA.ModelConfig

  @type session :: {atom(), map(), map()}
  @type state :: {tuple(), map()}

  @type label :: %{
          required(:session) => pos_integer(),
          required(:kind) => :call | :cast | :event | :timeout | :stutter | :terminating,
          required(:from) => atom() | nil,
          required(:to) => atom() | nil,
          optional(:message) => term(),
          optional(:reply) => term(),
          optional(:tag) => atom(),
          optional(:action) => action_key()
        }

  @typedoc """
  The TLA+ action that makes a step: `{state, index, branch}` for a
  transition of a state (the branch index is 0 for a step without
  branches), `{:timeout, state}` for a state timeout, or `:terminating`.
  """
  @type action_key ::
          {atom(), non_neg_integer(), non_neg_integer()} | {:timeout, atom()} | :terminating

  @typedoc """
  A liveness check: `trigger ~> target` for each session, under the
  fairness of the check. `fairness` is a list of `{:weak | :strong,
  action}`, where `action` is an `action_key()` or `:next` (any step that
  changes the state).
  """
  @type liveness :: %{
          name: String.t(),
          trigger: atom(),
          target: atom(),
          fairness: [{:weak | :strong, action_key() | :next}]
        }

  @type check :: %{
          name: String.t(),
          kind: :invariant | :action,
          fun: (state() -> boolean()) | (state(), state() -> boolean())
        }

  @type t :: %__MODULE__{
          ir: IR.t(),
          config: ModelConfig.t(),
          sessions: pos_integer(),
          shared_tracks: [atom()],
          session_tracks: [atom()],
          counters: [%{open: atom(), close: [atom()], var: String.t()}],
          actions: %{atom() => [map()]},
          terminal: MapSet.t(atom()),
          type_domains: %{atom() => {term(), boolean()}},
          constraint: [(state() -> boolean())],
          invariants: [check()],
          action_checks: [check()],
          liveness: [liveness()],
          skipped: [{String.t(), String.t()}],
          model_values: MapSet.t(atom())
        }

  @enforce_keys [:ir, :config]
  defstruct [
    :ir,
    :config,
    sessions: 1,
    shared_tracks: [],
    session_tracks: [],
    counters: [],
    actions: %{},
    terminal: MapSet.new(),
    type_domains: %{},
    constraint: [],
    invariants: [],
    action_checks: [],
    liveness: [],
    skipped: [],
    model_values: MapSet.new()
  ]

  defmodule EvaluationFailure do
    @moduledoc """
    A protocol function raised an error, or returned a bad value, while
    the explorer evaluated it.
    """
    defexception [:message, :label, :reason]
  end

  defmodule UnsupportedFailure do
    @moduledoc """
    The protocol uses a model feature that the explorer cannot evaluate.
    """
    defexception [:message]
  end

  # -- Build --

  @doc """
  Builds the model for a protocol module or for an IR and a config.

  Raises `Accord.Explore.Model.UnsupportedFailure` when the protocol uses a
  feature that the explorer cannot evaluate.
  """
  @spec build(module() | IR.t(), ModelConfig.t() | nil) :: t()
  def build(protocol, config \\ nil)

  def build(protocol, config) when is_atom(protocol) do
    config = config || model_config!(protocol)
    build(protocol.__ir__(), config)
  end

  def build(%IR{} = ir, %ModelConfig{} = config) do
    config = %{config | max_list_length: config.max_list_length || 3}
    {shared, session_tracks} = split_tracks(ir)

    model = %__MODULE__{
      ir: ir,
      config: config,
      sessions: config.sessions,
      shared_tracks: shared,
      session_tracks: session_tracks,
      counters: build_counters(ir),
      terminal: for({name, %{terminal: true}} <- ir.states, into: MapSet.new(), do: name)
    }

    model
    |> put_actions()
    |> put_type_domains()
    |> put_constraint()
    |> put_checks()
    |> put_model_values()
  end

  @doc """
  Gives the model config of a protocol module.

  This is the config that the generated spec uses. A protocol with
  `tla: :off` has no generated spec. For it, the config comes from the
  project file and the inline model options, as in
  `Accord.Test.TLACheck`.
  """
  @spec model_config(module()) :: ModelConfig.t()
  def model_config(protocol) do
    Code.ensure_loaded(protocol)

    if function_exported?(protocol, :__model_config__, 0) and protocol.__model_config__() do
      protocol.__model_config__()
    else
      [project_root: File.cwd!()]
      |> ModelConfig.load()
      |> ModelConfig.apply_inline(protocol.__ir__())
    end
  end

  defp model_config!(protocol), do: model_config(protocol)

  defp split_tracks(ir) do
    {shared, own} = Enum.split_with(ir.tracks, & &1.shared)
    {Enum.map(shared, & &1.name), Enum.map(own, & &1.name)}
  end

  # Unkeyed correspondence checks get one counter for each open event.
  # Checks with the same open event and close set share the counter.
  defp build_counters(%IR{properties: properties}) do
    for prop <- properties,
        check <- prop.checks,
        check.kind == :correspondence,
        Map.get(check.spec, :by) == nil,
        uniq: true do
      %{open: check.spec.open, close: check.spec.close, var: "#{check.spec.open}_pending"}
    end
  end

  # -- Actions --

  defp put_actions(%__MODULE__{ir: ir} = model) do
    actions =
      for {name, state} <- ir.states, into: %{} do
        transitions =
          if state.terminal, do: state.transitions, else: state.transitions ++ ir.anystate

        # Each action has its index in the state, so that a step names the
        # TLA+ action that makes it (for fairness).
        built =
          (Enum.map(transitions, &build_action(model, name, &1)) ++ timeout_action(state))
          |> Enum.with_index()
          |> Enum.map(fn {action, idx} -> Map.put(action, :index, idx) end)

        {name, built}
      end

    %{model | actions: actions}
  end

  defp timeout_action(%{state_timeout: nil}), do: []

  defp timeout_action(%{state_timeout: {_ms, target}}) do
    [%{kind: :timeout, tag: :__state_timeout__, to: target}]
  end

  defp build_action(model, source, %Transition{} = t) do
    tag = message_tag(t.message_pattern)
    messages = messages(model, t)

    cond do
      t.kind == :cast and t.branches != [] ->
        %{kind: :cast_branches, tag: tag, transition: t, messages: messages}

      t.kind == :event or (t.kind == :cast and t.to != nil) ->
        %{kind: t.kind, tag: tag, transition: t, messages: messages, to: resolve(t.to, source)}

      t.kind == :cast ->
        %{kind: :stutter, tag: tag}

      true ->
        %{
          kind: :call,
          tag: tag,
          transition: t,
          messages: messages,
          replies: replies(model, t)
        }
    end
  end

  defp resolve(:__same__, current), do: current
  defp resolve(nil, current), do: current
  defp resolve(state, _current), do: state

  defp message_tag(pattern) when is_atom(pattern), do: pattern
  defp message_tag(pattern) when is_tuple(pattern), do: elem(pattern, 0)

  # All messages of a transition. Each argument takes the values of its
  # model domain. The domain lookup uses the declared argument name, or
  # the name in the pattern, or `argN`, as the TLA+ model does.
  defp messages(model, %Transition{message_pattern: pattern} = t) when is_tuple(pattern) do
    [tag | args] = Tuple.to_list(pattern)
    names = t.message_arg_names || []

    if length(args) != length(t.message_types) do
      raise UnsupportedFailure,
        message:
          "message #{inspect(pattern)} has #{length(args)} arguments but #{length(t.message_types)} types"
    end

    args
    |> Enum.zip(t.message_types)
    |> Enum.with_index()
    |> Enum.map(fn {{arg, type}, idx} ->
      name =
        case Enum.at(names, idx) do
          name when is_binary(name) -> String.to_atom(name)
          _ -> param_name(arg, idx)
        end

      type_values(model, type, name)
    end)
    |> product()
    |> Enum.map(&List.to_tuple([tag | &1]))
  end

  defp messages(_model, %Transition{message_pattern: tag}), do: [tag]

  defp param_name(:_, idx), do: :"arg#{idx}"
  defp param_name(name, _idx) when is_atom(name), do: name
  defp param_name(_, idx), do: :"arg#{idx}"

  # All reply values that the server can send for a call. Each branch
  # adds the values of its reply type. A value that two branches accept
  # is kept one time: the monitor gives it to the first branch.
  defp replies(model, %Transition{branches: branches} = t) do
    branches
    |> Enum.flat_map(fn branch ->
      names = reply_names(t, branch)
      reply_values(model, branch.reply_type, names)
    end)
    |> Enum.uniq()
  end

  defp reply_values(model, {:tagged, tag, inner}, names) do
    inner
    |> List.wrap()
    |> Enum.with_index()
    |> Enum.map(fn {type, idx} -> type_values(model, type, Enum.at(names, idx)) end)
    |> product()
    |> Enum.map(&List.to_tuple([tag | &1]))
  end

  defp reply_values(model, type, _names), do: type_values(model, type, nil)

  # The values of a type in the model. Literal, union, tuple, and tagged
  # types are built from their parts. Lists are placeholder lists with a
  # length in `0..max_list_length`. Other types use the model domain.
  defp type_values(_model, {:literal, value}, _name), do: [value]

  defp type_values(model, {:union, types}, name) do
    types |> Enum.flat_map(&type_values(model, &1, name)) |> Enum.uniq()
  end

  defp type_values(model, {:list, _elem}, _name) do
    for len <- 0..model.config.max_list_length, do: List.duplicate(nil, len)
  end

  defp type_values(model, {:tuple, types}, _name) do
    types
    |> Enum.map(&type_values(model, &1, nil))
    |> product()
    |> Enum.map(&List.to_tuple/1)
  end

  defp type_values(model, {:tagged, _tag, _inner} = type, _name) do
    reply_values(model, type, [])
  end

  defp type_values(model, type, name) do
    model.config |> ModelConfig.resolve_domain(name || :_, type) |> domain_values()
  end

  @doc """
  Gives the Elixir values of a model domain.

  Model values become atoms with the TLC name: `{:model_values, 2}`
  gives `[:mv1, :mv2]`.
  """
  @spec domain_values(ModelConfig.domain()) :: [term()]
  def domain_values(%Range{} = range), do: Enum.to_list(range)
  def domain_values(list) when is_list(list), do: list
  def domain_values({:model_values, n}) when is_integer(n), do: for(i <- 1..n, do: :"mv#{i}")
  def domain_values({:model_values, names}) when is_list(names), do: names

  defp product([]), do: [[]]

  defp product([values | rest]) do
    rest_product = product(rest)
    for v <- values, tail <- rest_product, do: [v | tail]
  end

  # The variable names in the update and `where:` patterns of a branch,
  # by reply position. The TLA+ model looks up the domain of a reply
  # value with these names.
  defp reply_names(%Transition{} = t, %Branch{} = branch) do
    from_update = update_reply_names(t.update, branch)
    from_constraint = constraint_reply_names(branch.constraint)

    max_len = max(length(from_update), length(from_constraint))

    for i <- 0..(max_len - 1)//1 do
      Enum.at(from_update, i) || Enum.at(from_constraint, i)
    end
  end

  defp update_reply_names(
         %{ast: {:fn, _, [{:->, _, [[_msg, reply_pat, _tracks], body]}]}},
         branch
       ) do
    case var_name(reply_pat) do
      nil -> position_names(reply_pat)
      reply_var -> case_arm_names(body, reply_var, branch.reply_type)
    end
  end

  defp update_reply_names(_, _), do: []

  defp constraint_reply_names(%{ast: {:fn, _, [{:->, _, [[reply_pat, _tracks], _]}]}}) do
    position_names(reply_pat)
  end

  defp constraint_reply_names(_), do: []

  defp case_arm_names({:case, _, [{name, _, ctx}, [do: clauses]]}, name, reply_type)
       when is_atom(ctx) do
    Enum.find_value(clauses, [], fn {:->, _, [[pattern], _]} ->
      if arm_matches?(pattern, reply_type), do: position_names(pattern)
    end)
  end

  defp case_arm_names({:__block__, _, exprs}, name, reply_type) do
    Enum.find_value(exprs, [], fn expr ->
      case case_arm_names(expr, name, reply_type) do
        [] -> nil
        names -> names
      end
    end)
  end

  defp case_arm_names(_, _, _), do: []

  defp arm_matches?({tag, _}, {:tagged, tag, _}) when is_atom(tag), do: true
  defp arm_matches?({:{}, _, [tag | _]}, {:tagged, tag, _}), do: true
  defp arm_matches?(_, _), do: false

  defp position_names({tag, inner}) when is_atom(tag), do: [var_name(inner)]
  defp position_names({:{}, _, [_tag | rest]}), do: Enum.map(rest, &var_name/1)
  defp position_names(_), do: []

  defp var_name({name, meta, ctx}) when is_atom(name) and is_list(meta) and is_atom(ctx) do
    if String.starts_with?(Atom.to_string(name), "_"), do: nil, else: name
  end

  defp var_name(_), do: nil

  # -- Type invariant --

  # The TLA+ TypeInvariant: each track value is in its model domain. An
  # `abstract: :monotonic` track gets one more value, and a track with a
  # nil default can also be nil (NULL).
  defp put_type_domains(%__MODULE__{ir: ir, config: config} = model) do
    domains =
      for track <- ir.tracks, into: %{} do
        domain = ModelConfig.resolve_domain(config, track.name, track.type)

        domain =
          case {track.abstract, domain} do
            {:monotonic, %Range{first: lo, last: hi}} -> lo..(hi + 1)
            _ -> domain
          end

        {track.name, {domain, track.default == nil}}
      end

    %{model | type_domains: domains}
  end

  defp in_domain?(value, %Range{} = range), do: is_integer(value) and value in range
  defp in_domain?(value, list) when is_list(list), do: value in list

  defp in_domain?(value, {:model_values, _} = domain),
    do: is_atom(value) and value in domain_values(domain)

  # -- State constraint --

  defp put_constraint(%__MODULE__{ir: ir, config: config} = model) do
    counter_bounds =
      for %{var: var} <- model.counters,
          %Range{last: hi} <-
            [ModelConfig.resolve_domain(config, String.to_atom(var), :correspondence_counter)] do
        fn {sessions, _shared} ->
          sessions |> Tuple.to_list() |> Enum.all?(fn {_, _, c} -> Map.fetch!(c, var) <= hi end)
        end
      end

    abstract_bounds =
      for track <- ir.tracks,
          track.abstract == :monotonic,
          %Range{last: hi} <- [ModelConfig.resolve_domain(config, track.name, track.type)] do
        name = track.name
        fn state -> Enum.all?(track_values(model, state, name), &(&1 <= hi)) end
      end

    user = parse_user_constraint(model, config.state_constraint)
    %{model | constraint: user ++ counter_bounds ++ abstract_bounds}
  end

  # A user state constraint is raw TLA+ text. The explorer supports a
  # conjunction of `track op integer` terms only.
  defp parse_user_constraint(_model, nil), do: []

  defp parse_user_constraint(model, text) do
    text
    |> String.split("/\\")
    |> Enum.map(&String.trim/1)
    |> Enum.map(fn term ->
      case Regex.run(~r/^\(?\s*(\w+)\s*(=<|<=|>=|<|>|=|\/=|#)\s*(-?\d+)\s*\)?$/, term) do
        [_, var, op, int] ->
          name = String.to_atom(var)

          unless name in model.shared_tracks or
                   (name in model.session_tracks and model.sessions == 1) do
            raise UnsupportedFailure,
              message: "state constraint #{inspect(text)}: #{var} is not a scalar track"
          end

          limit = String.to_integer(int)
          compare = comparator(op)
          fn state -> Enum.all?(track_values(model, state, name), &compare.(&1, limit)) end

        _ ->
          raise UnsupportedFailure,
            message:
              "state constraint #{inspect(text)} is not supported " <>
                "(use a conjunction of `track op integer` terms)"
      end
    end)
  end

  defp comparator(op) when op in ["=<", "<="], do: &(is_integer(&1) and &1 <= &2)
  defp comparator(">="), do: &(is_integer(&1) and &1 >= &2)
  defp comparator("<"), do: &(is_integer(&1) and &1 < &2)
  defp comparator(">"), do: &(is_integer(&1) and &1 > &2)
  defp comparator("="), do: &(&1 == &2)
  defp comparator(op) when op in ["/=", "#"], do: &(&1 != &2)

  # -- Property checks --

  defp put_checks(%__MODULE__{ir: ir} = model) do
    type_inv = %{name: "TypeInvariant", kind: :invariant, fun: &type_invariant(model, &1)}

    {checks, skipped} =
      ir.properties
      |> Enum.flat_map(fn prop -> Enum.map(prop.checks, &{prop.name, &1}) end)
      |> Enum.reduce({[], []}, fn {prop_name, check}, {checks, skipped} ->
        case build_check(model, prop_name, check) do
          {:check, c} -> {[c | checks], skipped}
          {:skip, name, why} -> {checks, [{name, why} | skipped]}
          :none -> {checks, skipped}
        end
      end)

    checks = Enum.reverse(checks)

    %{
      model
      | invariants: [type_inv | Enum.filter(checks, &(&1.kind == :invariant))],
        action_checks: Enum.filter(checks, &(&1.kind == :action)),
        liveness: Enum.filter(checks, &(&1.kind == :liveness)),
        skipped: Enum.reverse(skipped)
    }
  end

  defp build_check(model, prop, %{kind: :invariant, spec: %{fun: fun}}) do
    {:check,
     %{
       name: camelize(prop),
       kind: :invariant,
       fun: fn state -> all_sessions?(model, state, fn tracks, _ -> truthy?(fun.(tracks)) end) end
     }}
  end

  defp build_check(model, prop, %{kind: :local_invariant, spec: %{state: in_state, fun: fun}}) do
    {:check,
     %{
       name: camelize(prop) <> camelize(in_state),
       kind: :invariant,
       fun: fn state ->
         all_sessions?(model, state, fn tracks, {name, _, _} ->
           name != in_state or truthy?(fun.(nil, tracks))
         end)
       end
     }}
  end

  defp build_check(model, prop, %{kind: :forbidden, spec: %{fun: fun}}) do
    {:check,
     %{
       name: camelize(prop),
       kind: :invariant,
       fun: fn state ->
         all_sessions?(model, state, fn tracks, _ -> not truthy?(fun.(tracks)) end)
       end
     }}
  end

  defp build_check(model, prop, %{kind: :bounded, spec: %{track: track, max: max}}) do
    {:check,
     %{
       name: camelize(prop),
       kind: :invariant,
       fun: fn state ->
         all_sessions?(model, state, fn tracks, _ ->
           case Map.fetch!(tracks, track) do
             value when is_integer(value) ->
               value <= max

             value ->
               raise EvaluationFailure,
                 message: "bounded #{track}: #{inspect(value)} is not an integer",
                 reason: :not_integer
           end
         end)
       end
     }}
  end

  defp build_check(_model, prop, %{kind: :correspondence, spec: %{open: open} = spec}) do
    if Map.get(spec, :by) do
      {:skip, camelize(prop), "keyed correspondence is runtime-only"}
    else
      var = "#{open}_pending"

      {:check,
       %{
         name: camelize(prop),
         kind: :invariant,
         fun: fn {sessions, _} ->
           sessions |> Tuple.to_list() |> Enum.all?(fn {_, _, c} -> Map.fetch!(c, var) >= 0 end)
         end
       }}
    end
  end

  defp build_check(model, prop, %{kind: :exclusive, spec: %{state: in_state}}) do
    if model.sessions > 1 do
      {:check,
       %{
         name: camelize(prop) <> "Exclusive",
         kind: :invariant,
         fun: fn {sessions, _} ->
           sessions |> Tuple.to_list() |> Enum.count(fn {name, _, _} -> name == in_state end) <=
             1
         end
       }}
    else
      :none
    end
  end

  defp build_check(model, prop, %{kind: :distinct, spec: %{track: track} = spec}) do
    if model.sessions > 1 do
      empty = Map.get(spec, :empty)

      {:check,
       %{
         name: camelize(prop) <> "Distinct",
         kind: :invariant,
         fun: fn {sessions, _} ->
           values =
             sessions
             |> Tuple.to_list()
             |> Enum.map(fn {_, tracks, _} -> Map.fetch!(tracks, track) end)
             |> Enum.reject(&(&1 == empty))

           length(values) == length(Enum.uniq(values))
         end
       }}
    else
      :none
    end
  end

  defp build_check(model, prop, %{kind: :action, spec: %{fun: fun}}) do
    {:check,
     %{
       name: camelize(prop),
       kind: :action,
       fun: fn old, new ->
         # `[][P]_<<tracks>>`: a step that changes no track is not checked.
         if track_tuple(model, old) == track_tuple(model, new) do
           true
         else
           Enum.all?(1..model.sessions, fn i ->
             truthy?(fun.(session_tracks(model, old, i), session_tracks(model, new, i)))
           end)
         end
       end
     }}
  end

  defp build_check(model, prop, %{kind: :liveness, spec: spec}) do
    case {spec.trigger, spec.target} do
      {{:in_state, trigger}, {:in_state, target}} ->
        {:check,
         %{
           name: camelize(prop),
           kind: :liveness,
           trigger: trigger,
           target: target,
           fairness: fairness(model, spec)
         }}

      _ ->
        {:skip, camelize(prop), "liveness supports only in_state predicates"}
    end
  end

  defp build_check(_model, prop, %{kind: kind}) when kind in [:ordered, :precedence],
    do: {:skip, camelize(prop), "#{kind} is runtime-only"}

  defp build_check(_model, _prop, _check), do: :none

  defp truthy?(value), do: value not in [nil, false]

  # The fairness of a liveness check, as the TLA+ spec states it. Without
  # `assuming:`, weak fairness on all of Next. With `assuming:`, weak (or
  # strong) fairness on each action of each named message tag: one action
  # for each branch. A state timeout is always weakly fair: a real timer
  # always fires.
  defp fairness(model, spec) do
    declared =
      case Map.get(spec, :assuming) do
        nil ->
          [{:weak, :next}]

        tags ->
          strength = if Map.get(spec, :fairness) == :strong, do: :strong, else: :weak

          for {state, actions} <- Enum.sort(model.actions),
              action <- actions,
              action.kind != :timeout,
              action.tag in tags,
              key <- action_keys(state, action),
              do: {strength, key}
      end

    timeouts =
      for {state, actions} <- Enum.sort(model.actions),
          %{kind: :timeout} <- actions,
          do: {:weak, {:timeout, state}}

    Enum.uniq(declared ++ timeouts)
  end

  defp action_keys(state, %{kind: kind, transition: t, index: idx})
       when kind in [:call, :cast_branches] do
    for b <- 0..(length(t.branches) - 1)//1, do: {state, idx, b}
  end

  defp action_keys(state, %{index: idx}), do: [{state, idx, 0}]

  # Calls `fun.(tracks, session)` for each session, where `tracks` has the
  # session tracks and the shared tracks.
  defp all_sessions?(model, {sessions, _shared} = state, fun) do
    sessions
    |> Tuple.to_list()
    |> Enum.with_index(1)
    |> Enum.all?(fn {session, i} -> fun.(session_tracks(model, state, i), session) end)
  end

  defp type_invariant(model, {sessions, shared}) do
    shared_ok = Enum.all?(shared, fn {name, value} -> typed?(model, name, value) end)

    sessions_ok =
      sessions
      |> Tuple.to_list()
      |> Enum.all?(fn {_name, tracks, _} ->
        Enum.all?(tracks, fn {name, value} -> typed?(model, name, value) end)
      end)

    shared_ok and sessions_ok
  end

  defp typed?(model, name, value) do
    {domain, nullable} = Map.fetch!(model.type_domains, name)
    (nullable and value == nil) or in_domain?(value, domain)
  end

  @doc false
  def camelize(name) when is_atom(name) do
    name |> Atom.to_string() |> String.split("_") |> Enum.map_join("", &String.capitalize/1)
  end

  # -- Model values --

  # The atoms that stand for TLC model values. The TLA+ value of such an
  # atom is the model value with the same name, not a string.
  defp put_model_values(%__MODULE__{ir: ir, config: config} = model) do
    domains =
      Map.values(config.domains) ++
        Enum.map(ir.tracks, &ModelConfig.resolve_domain(config, &1.name, &1.type)) ++
        Map.values(ModelConfig.builtin_defaults())

    names =
      for {:model_values, _} = domain <- domains,
          value <- domain_values(domain),
          into: MapSet.new(),
          do: value

    %{model | model_values: names}
  end

  # -- States --

  @doc """
  Gives the initial states.
  """
  @spec init_states(t()) :: [state()]
  def init_states(%__MODULE__{ir: ir, config: config} = model) do
    tracks =
      for track <- ir.tracks, into: %{} do
        {track.name, ModelConfig.resolve_init(config, track.name, track.default)}
      end

    counters = for %{var: var} <- model.counters, into: %{}, do: {var, 0}
    session = {ir.initial, Map.take(tracks, model.session_tracks), counters}
    sessions = List.to_tuple(List.duplicate(session, model.sessions))
    [{sessions, Map.take(tracks, model.shared_tracks)}]
  end

  @doc """
  Tells if a state satisfies the state constraint.

  TLC does not explore a state outside the constraint, and does not
  count it. TLC still checks the invariants on it.
  """
  @spec in_model?(t(), state()) :: boolean()
  def in_model?(%__MODULE__{constraint: constraint}, state) do
    Enum.all?(constraint, & &1.(state))
  end

  @doc """
  Gives the tracks that session `i` sees: its own tracks and the shared
  tracks.
  """
  @spec session_tracks(t(), state(), pos_integer()) :: map()
  def session_tracks(_model, {sessions, shared}, i) do
    {_name, tracks, _counters} = elem(sessions, i - 1)
    Map.merge(tracks, shared)
  end

  defp track_tuple(_model, {sessions, shared}) do
    {sessions |> Tuple.to_list() |> Enum.map(fn {_, tracks, _} -> tracks end), shared}
  end

  defp track_values(model, {sessions, shared}, name) do
    if name in model.shared_tracks do
      [Map.fetch!(shared, name)]
    else
      sessions |> Tuple.to_list() |> Enum.map(fn {_, tracks, _} -> Map.fetch!(tracks, name) end)
    end
  end

  @doc """
  Gives the symmetry representative of a state: the sessions in sorted
  order. Two states that differ only in the order of the sessions have
  the same representative.
  """
  @spec canonical(state()) :: state()
  def canonical({sessions, shared}) do
    {sessions |> Tuple.to_list() |> Enum.sort() |> List.to_tuple(), shared}
  end

  # -- Successors --

  @doc """
  Gives all successors of a state, as `{label, next_state}` pairs.

  Raises `Accord.Explore.Model.EvaluationFailure` when a protocol function
  raises an error or returns a bad value.
  """
  @spec successors(t(), state()) :: [{label(), state()}]
  def successors(%__MODULE__{} = model, {sessions, _shared} = state) do
    session_list = Tuple.to_list(sessions)

    steps =
      session_list
      |> Enum.with_index(1)
      |> Enum.flat_map(fn {{name, _, _}, i} ->
        model.actions
        |> Map.get(name, [])
        |> Enum.flat_map(&action_steps(model, state, i, name, &1))
      end)

    if Enum.all?(session_list, fn {name, _, _} -> MapSet.member?(model.terminal, name) end) do
      label = %{session: 1, kind: :terminating, from: nil, to: nil, action: :terminating}
      steps ++ [{label, state}]
    else
      steps
    end
  end

  defp action_steps(_model, state, i, name, %{kind: :stutter, tag: tag} = action) do
    label = %{
      session: i,
      kind: :cast,
      from: name,
      to: name,
      message: tag,
      tag: tag,
      action: {name, action.index, 0}
    }

    [{label, state}]
  end

  defp action_steps(model, state, i, name, %{kind: :timeout, tag: tag, to: target}) do
    label = %{
      session: i,
      kind: :timeout,
      from: name,
      to: target,
      tag: tag,
      action: {:timeout, name}
    }

    [{label, move(model, state, i, tag, name, target, session_tracks(model, state, i))}]
  end

  defp action_steps(model, state, i, name, %{kind: kind, to: target} = action)
       when kind in [:event, :cast] do
    t = action.transition
    tracks = session_tracks(model, state, i)

    for msg <- action.messages,
        label = %{
          session: i,
          kind: kind,
          from: name,
          to: target,
          message: msg,
          tag: action.tag,
          action: {name, action.index, 0}
        },
        guard?(t.guard, [msg, tracks], label) do
      new_tracks = update(t.update, [msg, tracks], tracks, label)
      {label, move(model, state, i, action.tag, name, target, new_tracks)}
    end
  end

  defp action_steps(model, state, i, name, %{kind: :cast_branches} = action) do
    t = action.transition
    tracks = session_tracks(model, state, i)

    for msg <- action.messages,
        label = %{session: i, kind: :cast, from: name, to: nil, message: msg, tag: action.tag},
        guard?(t.guard, [msg, tracks], label),
        b_idx = Enum.find_index(t.branches, &cast_branch?(&1, msg, tracks, label)),
        b_idx != nil do
      branch = Enum.at(t.branches, b_idx)
      target = resolve(branch.next_state, name)
      label = label |> Map.put(:to, target) |> Map.put(:action, {name, action.index, b_idx})
      new_tracks = update(t.update, [msg, tracks], tracks, label)
      {label, move(model, state, i, action.tag, name, target, new_tracks)}
    end
  end

  defp action_steps(model, state, i, name, %{kind: :call} = action) do
    t = action.transition
    tracks = session_tracks(model, state, i)

    for msg <- action.messages,
        label = %{session: i, kind: :call, from: name, to: nil, message: msg, tag: action.tag},
        guard?(t.guard, [msg, tracks], label),
        reply <- action.replies,
        b_idx = select_branch(t.branches, reply, tracks),
        b_idx != nil do
      branch = Enum.at(t.branches, b_idx)
      target = resolve(branch.next_state, name)

      label =
        label
        |> Map.put(:reply, reply)
        |> Map.put(:to, target)
        |> Map.put(:action, {name, action.index, b_idx})

      new_tracks = update(t.update, [msg, reply, tracks], tracks, label)
      {label, move(model, state, i, action.tag, name, target, new_tracks)}
    end
  end

  # The monitor rule: the first branch whose reply type matches and whose
  # `where:` constraint holds. A constraint that raises does not hold.
  defp select_branch(branches, reply, tracks) do
    Enum.find_index(branches, fn branch ->
      type_match?(branch.reply_type, reply) and constraint?(branch.constraint, reply, tracks)
    end)
  end

  defp constraint?(nil, _reply, _tracks), do: true

  defp constraint?(%{fun: fun}, reply, tracks) do
    fun.(reply, tracks) == true
  rescue
    _ -> false
  end

  defp cast_branch?(%{constraint: nil}, _msg, _tracks, _label), do: true

  defp cast_branch?(%{constraint: %{fun: fun}}, msg, tracks, label) do
    call(fun, [msg, tracks], label) == true
  end

  defp guard?(nil, _args, _label), do: true
  defp guard?(%{fun: fun}, args, label), do: truthy?(call(fun, args, label))

  defp update(nil, _args, tracks, _label), do: tracks

  defp update(%{fun: fun}, args, tracks, label) do
    case call(fun, args, label) do
      %{} = new_tracks ->
        if Map.keys(new_tracks) |> Enum.sort() == Map.keys(tracks) |> Enum.sort() do
          new_tracks
        else
          raise EvaluationFailure,
            message: "update changed the set of track names: #{inspect(new_tracks)}",
            label: label,
            reason: :bad_update
        end

      other ->
        raise EvaluationFailure,
          message: "update returned #{inspect(other)}, not a map of tracks",
          label: label,
          reason: :bad_update
    end
  end

  defp call(fun, args, label) do
    apply(fun, args)
  rescue
    e in EvaluationFailure ->
      reraise e, __STACKTRACE__

    e ->
      reraise EvaluationFailure,
              [message: Exception.message(e), label: label, reason: e],
              __STACKTRACE__
  end

  # Moves session `i` to `target` with new tracks, and updates the
  # correspondence counters of the session. A counter changes only on a
  # step that changes the state, as in the TLA+ model.
  defp move(model, {sessions, _shared}, i, tag, source, target, new_tracks) do
    {_name, _tracks, counters} = elem(sessions, i - 1)

    counters =
      if source == target do
        counters
      else
        Enum.reduce(model.counters, counters, fn %{open: open, close: close, var: var}, acc ->
          cond do
            tag == open -> Map.update!(acc, var, &(&1 + 1))
            tag in close -> Map.update!(acc, var, &(&1 - 1))
            true -> acc
          end
        end)
      end

    session = {target, Map.take(new_tracks, model.session_tracks), counters}
    {put_elem(sessions, i - 1, session), Map.take(new_tracks, model.shared_tracks)}
  end

  # A structural match of a reply against a reply type. Model domains
  # can use model values (atoms) for strings, binaries, maps, and
  # structs, so an atom matches these types.
  @doc false
  def type_match?({:literal, value}, reply), do: reply === value
  def type_match?(:term, _), do: true
  def type_match?({:union, types}, reply), do: Enum.any?(types, &type_match?(&1, reply))

  def type_match?({:tagged, tag, inner}, reply) when is_tuple(reply) do
    types = List.wrap(inner)

    tuple_size(reply) == length(types) + 1 and elem(reply, 0) == tag and
      types
      |> Enum.with_index(1)
      |> Enum.all?(fn {type, idx} -> type_match?(type, elem(reply, idx)) end)
  end

  def type_match?({:tuple, types}, reply) when is_tuple(reply) do
    tuple_size(reply) == length(types) and
      types
      |> Enum.with_index()
      |> Enum.all?(fn {type, idx} -> type_match?(type, elem(reply, idx)) end)
  end

  def type_match?({:list, _}, reply), do: is_list(reply)
  def type_match?(:integer, reply), do: is_integer(reply)
  def type_match?(:pos_integer, reply), do: is_integer(reply) and reply > 0
  def type_match?(:non_neg_integer, reply), do: is_integer(reply) and reply >= 0
  def type_match?(:boolean, reply), do: is_boolean(reply)
  def type_match?(:atom, reply), do: is_atom(reply)

  def type_match?(type, reply) when type in [:string, :binary],
    do: is_binary(reply) or is_atom(reply)

  def type_match?(:map, reply), do: is_map(reply) or is_atom(reply)
  def type_match?({:struct, _}, reply), do: is_map(reply) or is_atom(reply)
  def type_match?(_type, _reply), do: false
end
