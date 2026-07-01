defmodule Accord.Monitor do
  @moduledoc """
  Runtime protocol monitor as an explicit gen_statem proxy.

  Sits between client and server, validating messages against the
  protocol specification and assigning blame on violations.

      Client ──msg──▶ [Monitor] ──msg──▶ Server
                          │
                     on violation:
                     log / reject / crash
  """

  @behaviour :gen_statem

  alias Accord.IR.Branch
  alias Accord.Monitor.{Compiled, TransitionTable}
  alias Accord.Type.Check
  alias Accord.Violation

  @type violation_policy :: :log | :reject | :crash | {module(), atom()}

  defstruct [
    :compiled,
    :upstream,
    :downstream,
    :tracks,
    :violation_policy,
    :trace_sink,
    trace_seq: 0,
    call_timeout: 5_000,
    liveness_timeout: nil,
    # Property checking state.
    correspondence: %{},
    visited_states: MapSet.new(),
    ordered_last: %{}
  ]

  # -- Public API --

  @doc """
  Starts a monitor process.

  ## Options

  - `:upstream` (required) — PID of the server to forward messages to.
  - `:downstream` — PID that receives validated server-push events
    (see `event/2`). `nil` means validate-only: events are checked and
    consumed without forwarding.
  - `:violation_policy` — `:log` | `:reject` | `:crash` | `{mod, fun}`. Default `:crash`.
  - `:call_timeout` — timeout for upstream calls in ms. Default 5000.
  - `:liveness_timeout` — override all per-property liveness timeouts. Default `nil` (use per-property defaults).
  - `:trace_sink` — a `(Accord.Trace.Event.t() -> any())` fun or a pid
    receiving `{:accord_trace, event}` for every applied transition
    (see `Accord.TLA.TraceSpec` for replaying traces against the spec).
  """
  @spec start_link(Compiled.t(), keyword()) :: :gen_statem.start_ret()
  def start_link(%Compiled{} = compiled, opts) do
    upstream = Keyword.fetch!(opts, :upstream)
    downstream = Keyword.get(opts, :downstream)
    policy = Keyword.get(opts, :violation_policy, :crash)
    timeout = Keyword.get(opts, :call_timeout, 5_000)
    liveness_timeout = Keyword.get(opts, :liveness_timeout)
    trace_sink = Keyword.get(opts, :trace_sink)
    name = Keyword.get(opts, :name)

    init_arg = {compiled, upstream, downstream, policy, timeout, liveness_timeout, trace_sink}

    if name do
      :gen_statem.start_link({:local, name}, __MODULE__, init_arg, [])
    else
      :gen_statem.start_link(__MODULE__, init_arg, [])
    end
  end

  @doc """
  Sends a synchronous call through the monitor.
  """
  @spec call(pid() | atom(), term(), timeout()) :: term()
  def call(monitor, message, timeout \\ 5_000) do
    :gen_statem.call(monitor, {:accord_call, message}, timeout)
  end

  @doc """
  Sends an asynchronous cast through the monitor.
  """
  @spec cast(pid() | atom(), term()) :: :ok
  def cast(monitor, message) do
    :gen_statem.cast(monitor, {:accord_cast, message})
  end

  @doc """
  Pushes a server event through the monitor (server → client).

  The server sends events via the monitor rather than directly to the
  client, so the monitor can validate them against the protocol's
  `event` declarations for the current state. Valid events are forwarded
  to the `:downstream` pid (when configured) with `send/2`; violations
  blame the server.
  """
  @spec event(pid() | atom(), term()) :: :ok
  def event(monitor, message) do
    :gen_statem.cast(monitor, {:accord_event, message})
  end

  # -- gen_statem callbacks --

  @impl true
  def callback_mode, do: :handle_event_function

  @impl true
  def init({compiled, upstream, downstream, policy, timeout, liveness_timeout, trace_sink}) do
    data = %__MODULE__{
      compiled: compiled,
      upstream: upstream,
      downstream: downstream,
      tracks: compiled.track_init,
      violation_policy: policy,
      call_timeout: timeout,
      liveness_timeout: liveness_timeout,
      trace_sink: trace_sink,
      visited_states: MapSet.new([compiled.ir.initial])
    }

    {:ok, compiled.ir.initial, data, arm_state_timeout(data, nil, compiled.ir.initial)}
  end

  @impl true
  # Synchronous call
  def handle_event({:call, from}, {:accord_call, message}, state, data) do
    handle_call(message, from, state, data)
  end

  # Asynchronous cast
  def handle_event(:cast, {:accord_cast, message}, state, data) do
    handle_cast(message, state, data)
  end

  # Server-push event
  def handle_event(:cast, {:accord_event, message}, state, data) do
    handle_push_event(message, state, data)
  end

  # State timeout expiry: the monitor transitions on its own.
  def handle_event(:state_timeout, {:accord_after, target}, state, data) do
    apply_internal_transition(target, state, data)
  end

  # Liveness timer expiry.
  def handle_event({:timeout, {:liveness, prop_name}}, _content, state, data) do
    property = Enum.find(data.compiled.ir.properties, &(&1.name == prop_name))

    violation = %{
      Violation.liveness_violated(state, prop_name)
      | span: if(property, do: property.span)
    }

    handle_liveness_violation(violation, state, data)
  end

  # -- Call Pipeline --

  defp handle_call(message, from, state, data) do
    table = data.compiled.transition_table

    cond do
      TransitionTable.terminal?(table, state) ->
        violation = Violation.session_ended(state, message)
        handle_violation(violation, from, state, data)

      true ->
        case TransitionTable.lookup(table, state, message) do
          {:ok, transition} when transition.kind == :call ->
            process_call_transition(transition, message, from, state, data)

          {:ok, _transition} ->
            # The tag belongs to a cast or a server event — not callable.
            violation = Violation.invalid_message(state, message, valid_tags(table, state))
            handle_violation(violation, from, state, data)

          :error ->
            violation = Violation.invalid_message(state, message, valid_tags(table, state))
            handle_violation(violation, from, state, data)
        end
    end
  end

  defp process_call_transition(transition, message, from, state, data) do
    # Step 1: Type-check message arguments.
    case check_message_types(message, transition, state, :client) do
      :ok ->
        # Step 2: Evaluate guard (if present).
        case evaluate_guard(transition.guard, message, data.tracks) do
          :ok ->
            # Step 3: Forward to upstream, get reply.
            forward_call(transition, message, from, state, data)

          {:error, :guard_failed} ->
            violation = Violation.guard_failed(state, message)
            handle_violation(violation, from, state, data)
        end

      {:error, violation} ->
        handle_violation(violation, from, state, data)
    end
  end

  defp forward_call(transition, message, from, state, data) do
    # Per-transition timeout takes precedence over the monitor default.
    timeout = transition.call_timeout || data.call_timeout

    try do
      reply = GenServer.call(data.upstream, message, timeout)
      handle_reply(transition, message, reply, from, state, data)
    catch
      :exit, {:timeout, _} ->
        violation = Violation.timeout(state, message, timeout)
        handle_violation(violation, from, state, data)
    end
  end

  defp handle_reply(transition, message, reply, from, state, data) do
    case select_branch(transition.branches, reply, data.tracks) do
      {:ok, %Branch{next_state: next_state}} ->
        actual_next = if next_state == :__same__, do: state, else: next_state

        apply_transition_and_check_properties(
          transition,
          message,
          reply,
          from,
          state,
          actual_next,
          data
        )

      {:error, {:constraint_failed, %Branch{reply_type: reply_type}}} ->
        violation = Violation.constraint_failed(state, message, reply, reply_type)
        handle_violation(violation, from, state, data)

      {:error, :no_type_match} ->
        valid = Enum.map(transition.branches, & &1.reply_type)
        violation = Violation.invalid_reply(state, message, reply, valid)
        handle_violation(violation, from, state, data)
    end
  end

  # Selects the branch for a reply: the first branch whose type matches
  # AND whose where: constraint (if any) holds for the current tracks —
  # the same semantics as the TLA+ model, where each branch is an action
  # with the constraint as a precondition.
  #
  # When a branch matches on type but fails its constraint, later branches
  # are still tried (the model would take their action instead); only if
  # nothing accepts the reply is the first constraint failure reported.
  defp select_branch(branches, reply, tracks) do
    result =
      Enum.reduce_while(branches, {:error, :no_type_match}, fn branch, acc ->
        case Check.check(reply, branch.reply_type) do
          :ok ->
            if constraint_holds?(branch.constraint, reply, tracks) do
              {:halt, {:ok, branch}}
            else
              # Remember the first constraint failure, keep trying.
              acc =
                case acc do
                  {:error, :no_type_match} -> {:error, {:constraint_failed, branch}}
                  other -> other
                end

              {:cont, acc}
            end

          {:error, _} ->
            {:cont, acc}
        end
      end)

    result
  end

  defp constraint_holds?(nil, _reply, _tracks), do: true

  defp constraint_holds?(%{fun: fun}, reply, tracks) when is_function(fun) do
    fun.(reply, tracks) == true
  rescue
    # A raising constraint cannot hold; the reply is treated as violating.
    _ -> false
  end

  defp constraint_holds?(_, _reply, _tracks), do: true

  defp apply_transition_and_check_properties(
         transition,
         message,
         reply,
         from,
         prev_state,
         next_state,
         data
       ) do
    old_tracks = data.tracks
    new_tracks = apply_update(transition.update, message, reply, data.tracks)

    case check_properties(message, prev_state, next_state, old_tracks, new_tracks, data) do
      {:ok, updated_data} ->
        updated_data = %{updated_data | tracks: new_tracks}
        updated_data = track_visited_state(updated_data, next_state)
        updated_data = emit_trace(updated_data, prev_state, message, reply, next_state)

        timer_actions =
          liveness_actions(updated_data, next_state) ++
            arm_state_timeout(updated_data, prev_state, next_state)

        {:next_state, next_state, updated_data, [{:reply, from, reply} | timer_actions]}

      {:violation, violation, updated_data} ->
        updated_data = %{updated_data | tracks: new_tracks}
        updated_data = track_visited_state(updated_data, next_state)
        updated_data = emit_trace(updated_data, prev_state, message, reply, next_state)

        timer_actions =
          liveness_actions(updated_data, next_state) ++
            arm_state_timeout(updated_data, prev_state, next_state)

        handle_property_violation(
          violation,
          reply,
          from,
          next_state,
          updated_data,
          timer_actions
        )
    end
  end

  # -- State Timeouts --

  # The timeout fired while still in `state`: transition to the target
  # with no message exchange. Tracks are untouched; properties are
  # checked with the pseudo-message :__state_timeout__ (a tag no
  # correspondence or ordering matches).
  defp apply_internal_transition(target, state, data) do
    case check_properties(:__state_timeout__, state, target, data.tracks, data.tracks, data) do
      {:ok, updated_data} ->
        updated_data = track_visited_state(updated_data, target)
        updated_data = emit_trace(updated_data, state, :__state_timeout__, nil, target)

        timer_actions =
          liveness_actions(updated_data, target) ++
            arm_state_timeout(updated_data, state, target)

        {:next_state, target, updated_data, timer_actions}

      {:violation, violation, updated_data} ->
        updated_data = track_visited_state(updated_data, target)
        updated_data = emit_trace(updated_data, state, :__state_timeout__, nil, target)

        timer_actions =
          liveness_actions(updated_data, target) ++
            arm_state_timeout(updated_data, state, target)

        handle_event_property_violation(violation, target, updated_data, timer_actions)
    end
  end

  # One trace event per applied transition (nil sink: free).
  defp emit_trace(%{trace_sink: nil} = data, _prev, _message, _reply, _next), do: data

  defp emit_trace(data, prev_state, message, reply, next_state) do
    event = %Accord.Trace.Event{
      seq: data.trace_seq,
      prev_state: prev_state,
      message: message,
      reply: reply,
      next_state: next_state,
      tracks: data.tracks
    }

    Accord.Trace.emit(data.trace_sink, event)
    %{data | trace_seq: data.trace_seq + 1}
  end

  # Arms the target state's timer on real entry. Self-loops keep the
  # running timer (gen_statem only cancels a state_timeout when the
  # state value changes, and we do not re-arm), so a busy state cannot
  # starve its own timeout by resetting it.
  defp arm_state_timeout(_data, prev_state, prev_state), do: []

  defp arm_state_timeout(data, _prev_state, next_state) do
    case Map.get(data.compiled.state_timeouts, next_state) do
      nil -> []
      {ms, target} -> [{:state_timeout, ms, {:accord_after, target}}]
    end
  end

  # -- Cast Pipeline --

  defp handle_cast(message, state, data) do
    table = data.compiled.transition_table

    cond do
      TransitionTable.terminal?(table, state) ->
        violation = Violation.session_ended(state, message)
        handle_cast_violation(violation, state, data)

      true ->
        case TransitionTable.lookup(table, state, message) do
          {:ok, transition} when transition.kind == :cast ->
            # Type-check message arguments.
            case check_message_types(message, transition, state, :client) do
              :ok ->
                # Forward to upstream.
                GenServer.cast(data.upstream, message)
                {:keep_state, data}

              {:error, violation} ->
                handle_cast_violation(violation, state, data)
            end

          {:ok, _transition} ->
            # Found a :call transition, not valid for cast.
            violation = Violation.invalid_message(state, message, [])
            handle_cast_violation(violation, state, data)

          :error ->
            violation = Violation.invalid_message(state, message, valid_tags(table, state))
            handle_cast_violation(violation, state, data)
        end
    end
  end

  # -- Event Pipeline (server → client) --

  defp handle_push_event(message, state, data) do
    table = data.compiled.transition_table

    cond do
      TransitionTable.terminal?(table, state) ->
        violation = Violation.session_ended(state, message, :server)
        handle_cast_violation(violation, state, data)

      true ->
        case TransitionTable.lookup(table, state, message) do
          {:ok, transition} when transition.kind == :event ->
            process_event_transition(transition, message, state, data)

          _ ->
            violation = Violation.invalid_event(state, message, valid_event_tags(table, state))
            handle_cast_violation(violation, state, data)
        end
    end
  end

  # Everything a pushed event violates is the server's fault — it is the
  # sender. Blame derives from message direction, not pipeline position.
  defp process_event_transition(transition, message, state, data) do
    case check_message_types(message, transition, state, :server) do
      :ok ->
        case evaluate_guard(transition.guard, message, data.tracks) do
          :ok ->
            apply_event_transition(transition, message, state, data)

          {:error, :guard_failed} ->
            violation = Violation.guard_failed(state, message, :server)
            handle_cast_violation(violation, state, data)
        end

      {:error, violation} ->
        handle_cast_violation(violation, state, data)
    end
  end

  defp apply_event_transition(transition, message, state, data) do
    next_state = if transition.to == :__same__, do: state, else: transition.to
    old_tracks = data.tracks
    new_tracks = apply_event_update(transition.update, message, old_tracks)

    case check_properties(message, state, next_state, old_tracks, new_tracks, data) do
      {:ok, updated_data} ->
        updated_data = %{updated_data | tracks: new_tracks}
        updated_data = track_visited_state(updated_data, next_state)
        updated_data = emit_trace(updated_data, state, message, nil, next_state)

        timer_actions =
          liveness_actions(updated_data, next_state) ++
            arm_state_timeout(updated_data, state, next_state)

        forward_event(data.downstream, message)
        {:next_state, next_state, updated_data, timer_actions}

      {:violation, violation, updated_data} ->
        updated_data = %{updated_data | tracks: new_tracks}
        updated_data = track_visited_state(updated_data, next_state)
        updated_data = emit_trace(updated_data, state, message, nil, next_state)

        timer_actions =
          liveness_actions(updated_data, next_state) ++
            arm_state_timeout(updated_data, state, next_state)

        # Like all property violations, the (valid) event is still
        # forwarded — the transition succeeded.
        forward_event(data.downstream, message)
        handle_event_property_violation(violation, next_state, updated_data, timer_actions)
    end
  end

  # nil downstream means validate-only: the event is checked and consumed.
  defp forward_event(nil, _message), do: :ok

  defp forward_event(downstream, message) do
    send(downstream, message)
    :ok
  end

  defp apply_event_update(nil, _message, tracks), do: tracks

  defp apply_event_update(%{fun: update_fn}, message, tracks) do
    update_fn.(message, tracks)
  end

  defp valid_event_tags(table, state) do
    for {{s, tag}, transition} <- table.table, s == state, transition.kind == :event, do: tag
  end

  # -- Message Type Checking --

  defp check_message_types(_message, %{message_types: []}, _state, _blame), do: :ok

  defp check_message_types(message, transition, state, blame) when is_tuple(message) do
    args = message |> Tuple.to_list() |> tl()
    types = transition.message_types

    if length(args) != length(types) do
      :ok
    else
      args
      |> Enum.zip(types)
      |> Enum.with_index()
      |> Enum.find_value(:ok, fn {{arg, type}, pos} ->
        case Check.check(arg, type) do
          :ok -> nil
          {:error, _} -> {:error, Violation.argument_type(state, message, pos, type, arg, blame)}
        end
      end)
    end
  end

  defp check_message_types(_message, _transition, _state, _blame), do: :ok

  # -- Guard Evaluation --

  defp evaluate_guard(nil, _message, _tracks), do: :ok

  defp evaluate_guard(%{fun: guard_fn}, message, tracks) do
    if guard_fn.(message, tracks) do
      :ok
    else
      {:error, :guard_failed}
    end
  end

  # -- Update Application --

  defp apply_update(nil, _message, _reply, tracks), do: tracks

  defp apply_update(%{fun: update_fn}, message, reply, tracks) do
    update_fn.(message, reply, tracks)
  end

  # -- Property Checking --

  defp check_properties(message, prev_state, next_state, old_tracks, new_tracks, data) do
    properties = data.compiled.ir.properties

    Enum.reduce_while(properties, {:ok, data}, fn property, {:ok, acc_data} ->
      case check_property_checks(
             property,
             message,
             prev_state,
             next_state,
             old_tracks,
             new_tracks,
             acc_data
           ) do
        {:ok, updated_data} -> {:cont, {:ok, updated_data}}
        {:violation, violation, updated_data} -> {:halt, {:violation, violation, updated_data}}
      end
    end)
  end

  defp check_property_checks(
         property,
         message,
         prev_state,
         next_state,
         old_tracks,
         new_tracks,
         data
       ) do
    Enum.reduce_while(property.checks, {:ok, data}, fn check, {:ok, acc_data} ->
      case check_single(
             check,
             property,
             message,
             prev_state,
             next_state,
             old_tracks,
             new_tracks,
             acc_data
           ) do
        {:ok, updated_data} -> {:cont, {:ok, updated_data}}
        {:violation, violation, updated_data} -> {:halt, {:violation, violation, updated_data}}
      end
    end)
  end

  defp check_single(
         %{kind: :invariant} = check,
         property,
         _msg,
         _prev_state,
         next_state,
         _old,
         new_tracks,
         data
       ) do
    if check.spec.fun.(new_tracks) do
      {:ok, data}
    else
      base = Violation.invariant_violated(next_state, property.name, new_tracks)

      violation = %{
        base
        | span: check.span,
          context: Map.put(base.context, :check_kind, check.kind)
      }

      {:violation, violation, data}
    end
  end

  defp check_single(
         %{kind: :local_invariant} = check,
         property,
         message,
         _prev_state,
         next_state,
         _old,
         new_tracks,
         data
       ) do
    if check.spec.state == next_state do
      if check.spec.fun.(message, new_tracks) do
        {:ok, data}
      else
        base = Violation.invariant_violated(next_state, property.name, new_tracks)

        violation = %{
          base
          | span: check.span,
            context: Map.put(base.context, :check_kind, check.kind)
        }

        {:violation, violation, data}
      end
    else
      {:ok, data}
    end
  end

  defp check_single(
         %{kind: :action} = check,
         property,
         _msg,
         _prev_state,
         next_state,
         old_tracks,
         new_tracks,
         data
       ) do
    if check.spec.fun.(old_tracks, new_tracks) do
      {:ok, data}
    else
      base = Violation.action_violated(next_state, property.name, old_tracks, new_tracks)

      violation = %{
        base
        | span: check.span,
          context: Map.put(base.context, :check_kind, check.kind)
      }

      {:violation, violation, data}
    end
  end

  defp check_single(
         %{kind: :bounded} = check,
         property,
         _msg,
         _prev_state,
         next_state,
         _old,
         new_tracks,
         data
       ) do
    value = Map.get(new_tracks, check.spec.track)

    if is_nil(value) or value <= check.spec.max do
      {:ok, data}
    else
      base = Violation.invariant_violated(next_state, property.name, new_tracks)

      violation = %{
        base
        | span: check.span,
          context: Map.put(base.context, :check_kind, check.kind)
      }

      {:violation, violation, data}
    end
  end

  defp check_single(
         %{kind: :forbidden} = check,
         property,
         _msg,
         _prev_state,
         next_state,
         _old,
         new_tracks,
         data
       ) do
    if check.spec.fun.(new_tracks) do
      base = Violation.invariant_violated(next_state, property.name, new_tracks)

      violation = %{
        base
        | span: check.span,
          context: Map.put(base.context, :check_kind, check.kind)
      }

      {:violation, violation, data}
    else
      {:ok, data}
    end
  end

  defp check_single(
         %{kind: :precedence} = check,
         property,
         _msg,
         _prev_state,
         next_state,
         _old,
         _new,
         data
       ) do
    if next_state == check.spec.target do
      if MapSet.member?(data.visited_states, check.spec.required) do
        {:ok, data}
      else
        base = Violation.precedence_violated(next_state, property.name, check.spec.required)

        violation = %{
          base
          | span: check.span,
            context: Map.put(base.context, :check_kind, check.kind)
        }

        {:violation, violation, data}
      end
    else
      {:ok, data}
    end
  end

  defp check_single(
         %{kind: :ordered} = check,
         property,
         message,
         _prev_state,
         next_state,
         _old,
         _new,
         data
       ) do
    tag = message_tag(message)

    if tag == check.spec.event and is_tuple(message) do
      value = extract_field(message, check.spec.extract)
      last = Map.get(data.ordered_last, property.name)

      if is_nil(last) or value >= last do
        {:ok, %{data | ordered_last: Map.put(data.ordered_last, property.name, value)}}
      else
        base = Violation.ordering_violated(next_state, property.name, last, value)

        violation = %{
          base
          | span: check.span,
            context: Map.put(base.context, :check_kind, check.kind)
        }

        {:violation, violation, data}
      end
    else
      {:ok, data}
    end
  end

  # Correspondence counts on the resolved branch — only transitions that
  # change state open or close (the same rule the TLA+ model uses for its
  # counter variable). A rejected self-loop (e.g. a release that stays
  # :locked) neither opens nor closes.
  defp check_single(
         %{kind: :correspondence} = check,
         property,
         message,
         prev_state,
         next_state,
         _old,
         _new,
         data
       ) do
    tag = message_tag(message)
    corr = data.correspondence
    state_changed? = prev_state != next_state

    cond do
      tag == check.spec.open and state_changed? ->
        key = correspondence_key(check, message, :open)
        {:ok, %{data | correspondence: Map.update(corr, key, 1, &(&1 + 1))}}

      tag in check.spec.close and state_changed? ->
        key = correspondence_key(check, message, :close)
        count = Map.get(corr, key, 0) - 1

        if count < 0 do
          # A close without a matching open. Reset to zero so one stray
          # close is reported once, not on every subsequent message.
          base =
            Violation.correspondence_violated(next_state, property.name, check.spec.open, tag)

          violation = %{
            base
            | span: check.span,
              context: Map.put(base.context, :check_kind, check.kind)
          }

          {:violation, violation, %{data | correspondence: Map.put(corr, key, 0)}}
        else
          {:ok, %{data | correspondence: Map.put(corr, key, count)}}
        end

      true ->
        {:ok, data}
    end
  end

  # Pass through other check kinds at runtime (design-time only).
  defp check_single(_check, _property, _msg, _prev_state, _next_state, _old, _new, data) do
    {:ok, data}
  end

  defp message_tag(msg) when is_atom(msg), do: msg
  defp message_tag(msg) when is_tuple(msg), do: elem(msg, 0)

  # -- Field Extraction --

  defp extract_field(message, %{position: pos, path: []}), do: elem(message, pos)

  defp extract_field(message, %{position: pos, path: path}) do
    get_in(elem(message, pos), Enum.map(path, &Access.key/1))
  end

  # -- Correspondence Key --

  defp correspondence_key(%{spec: spec} = _check, message, role) do
    case Map.get(spec, :open_extract) do
      nil ->
        # No :by option — use open tag as key (existing behavior).
        spec.open

      open_extract when role == :open ->
        {spec.open, extract_field(message, open_extract)}

      _open_extract when role == :close ->
        tag = message_tag(message)
        {spec.open, extract_field(message, spec.close_extracts[tag])}
    end
  end

  # -- Visited State Tracking --

  defp track_visited_state(data, state) do
    %{data | visited_states: MapSet.put(data.visited_states, state)}
  end

  # -- Liveness Timer Actions --

  defp liveness_actions(data, next_state) do
    timeout_override = data.liveness_timeout

    Enum.flat_map(data.compiled.ir.properties, fn prop ->
      Enum.flat_map(prop.checks, fn
        %{kind: :liveness} = check ->
          timeout = timeout_override || check.spec.timeout

          if timeout == :infinity do
            []
          else
            liveness_timer_actions(prop.name, check, next_state, timeout)
          end

        _ ->
          []
      end)
    end)
  end

  defp liveness_timer_actions(prop_name, check, next_state, timeout) do
    in_trigger = matches_predicate?(check.spec.trigger, next_state)
    in_target = matches_predicate?(check.spec.target, next_state)

    cond do
      in_target -> [{{:timeout, {:liveness, prop_name}}, :infinity, :cancel}]
      in_trigger -> [{{:timeout, {:liveness, prop_name}}, timeout, prop_name}]
      true -> []
    end
  end

  defp matches_predicate?({:in_state, state}, current), do: current == state

  # -- Liveness Violation Handling --

  defp handle_liveness_violation(violation, _state, data) do
    case data.violation_policy do
      :log ->
        log_violation(violation)
        {:keep_state, data}

      :reject ->
        log_violation(violation)
        {:keep_state, data}

      :crash ->
        {:stop, {:protocol_violation, violation}, data}

      {mod, fun} ->
        apply(mod, fun, [violation])
        {:keep_state, data}
    end
  end

  # Property violations allow the reply to be forwarded (the transition
  # succeeded) but then the violation is reported separately.
  defp handle_property_violation(violation, reply, from, next_state, data, timer_actions) do
    case data.violation_policy do
      :log ->
        log_violation(violation)
        {:next_state, next_state, data, [{:reply, from, reply} | timer_actions]}

      :reject ->
        log_violation(violation)
        {:next_state, next_state, data, [{:reply, from, reply} | timer_actions]}

      :crash ->
        {:stop_and_reply, {:protocol_violation, violation}, [{:reply, from, reply}]}

      {mod, fun} ->
        apply(mod, fun, [violation])
        {:next_state, next_state, data, [{:reply, from, reply} | timer_actions]}
    end
  end

  # -- Violation Handling --

  # Declared role names label the blame in diagnostics: the first role
  # initiates calls/casts (:client blame), the second replies and pushes
  # events (:server blame).
  defp assign_role(violation, data) do
    case {violation.blame, data.compiled.ir.roles} do
      {:client, [%{name: role} | _]} ->
        %{violation | context: Map.put(violation.context, :role, role)}

      {:server, [_, %{name: role} | _]} ->
        %{violation | context: Map.put(violation.context, :role, role)}

      _ ->
        violation
    end
  end

  defp handle_violation(violation, from, _state, data) do
    violation = assign_role(violation, data)

    case data.violation_policy do
      :log ->
        log_violation(violation)
        {:keep_state, data, [{:reply, from, {:accord_violation, violation}}]}

      :reject ->
        log_violation(violation)
        {:keep_state, data, [{:reply, from, {:accord_violation, violation}}]}

      :crash ->
        {:stop_and_reply, {:protocol_violation, violation},
         [{:reply, from, {:accord_violation, violation}}]}

      {mod, fun} ->
        apply(mod, fun, [violation])
        {:keep_state, data, [{:reply, from, {:accord_violation, violation}}]}
    end
  end

  defp handle_cast_violation(violation, _state, data) do
    violation = assign_role(violation, data)

    case data.violation_policy do
      :crash ->
        {:stop, {:protocol_violation, violation}, data}

      {mod, fun} ->
        apply(mod, fun, [violation])
        {:keep_state, data}

      _ ->
        log_violation(violation)
        {:keep_state, data}
    end
  end

  # Property violations on events still transition (the event was valid);
  # the violation is reported through the policy.
  defp handle_event_property_violation(violation, next_state, data, timer_actions) do
    case data.violation_policy do
      :crash ->
        {:stop, {:protocol_violation, violation}, data}

      {mod, fun} ->
        apply(mod, fun, [violation])
        {:next_state, next_state, data, timer_actions}

      _ ->
        log_violation(violation)
        {:next_state, next_state, data, timer_actions}
    end
  end

  defp log_violation(violation) do
    require Logger

    blame_label =
      case violation.context[:role] do
        nil -> "#{violation.blame}"
        role -> "#{violation.blame}, role :#{role}"
      end

    Logger.warning(
      "protocol violation: #{violation.kind} (#{blame_label}) in state :#{violation.state} — #{inspect(violation.message)}"
    )
  end

  defp valid_tags(table, state) do
    for {{s, tag}, _} <- table.table, s == state, do: tag
  end
end
