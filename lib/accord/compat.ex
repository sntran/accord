defmodule Accord.Compat do
  @moduledoc """
  Static compatibility checking between two versions of a protocol.

  `check(old, new)` answers the rolling-upgrade question: **can clients
  speaking the `old` contract talk to a server monitored by the `new`
  one?** Deploy servers first when it holds. The relation is directional
  but the same function answers the dual — `check(new, old)` asks
  whether *new* clients work against *old* servers (client-first
  deployment).

  The check is a state-by-state simulation over the IRs:

  - every old state must exist in new, and must not have become terminal
    (C001, C002);
  - every message an old client may send must still be accepted — same
    tag and kind (C003), argument types may only widen (contravariance,
    C004);
  - every reply the new contract permits must be understood by old
    clients — reply types may only narrow (covariance, C005) — and must
    lead to the state the old client will assume (C006). Old clients
    resolve replies by first-*value*-match in declaration order, so when
    reply types overlap (the `where:` refinement idiom) C006 requires the
    reply routing to stay identical rather than trusting a static,
    order-blind type comparison;
  - every event the new server may push in a state must be one old
    clients understand, with covariant payloads and matching targets
    (C007, C008);
  - state timeouts must not change the session's autonomous movement
    (C009);
  - changed guards, `where:` constraints, track updates, and track
    defaults are advisories (W-C010): they can shift which messages the
    new contract accepts or how tracks evolve (and track evolution feeds
    the `where:` refinements that route replies), none of which is
    statically decidable.

  Purely syntactic/structural: behavioral equivalence under renamed
  states or refactored guards is out of scope, and `false`-leaning by
  design — an incompatibility report may be conservative, but a clean
  result is trustworthy for the checks listed.
  """

  alias Accord.IR
  alias Accord.IR.Type
  alias Pentiment.Report

  import Accord.Pass.Helpers, only: [maybe_add_source: 2, maybe_add_span_label: 3, message_tag: 1]

  defmodule Result do
    @moduledoc """
    The outcome of a compatibility check.
    """

    @type t :: %__MODULE__{
            compatible?: boolean(),
            errors: [Pentiment.Report.t()],
            warnings: [Pentiment.Report.t()]
          }

    @enforce_keys [:compatible?, :errors, :warnings]
    defstruct [:compatible?, :errors, :warnings]
  end

  @doc """
  Checks whether clients of `old` can talk to a server monitored by
  `new`.

  Accepts protocol modules or IRs.
  """
  @spec check(module() | IR.t(), module() | IR.t()) :: Result.t()
  def check(old, new) do
    old_ir = to_ir(old)
    new_ir = to_ir(new)

    {errors, warnings} =
      []
      |> check_initial(old_ir, new_ir)
      |> check_tracks(old_ir, new_ir)
      |> check_states(old_ir, new_ir)
      |> Enum.split_with(fn {severity, _report} -> severity == :error end)

    %Result{
      compatible?: errors == [],
      errors: Enum.map(errors, fn {_s, r} -> r end),
      warnings: Enum.map(warnings, fn {_s, r} -> r end)
    }
  end

  defp to_ir(%IR{} = ir), do: ir
  defp to_ir(mod) when is_atom(mod), do: mod.__ir__()

  # -- Checks --

  defp check_initial(findings, old_ir, new_ir) do
    if old_ir.initial == new_ir.initial do
      findings
    else
      report =
        Report.error(
          "initial state changed from :#{old_ir.initial} to :#{new_ir.initial} — " <>
            "old clients start their session model in :#{old_ir.initial}"
        )
        |> Report.with_code("C001")
        |> maybe_add_source(new_ir.source_file)

      [{:error, report} | findings]
    end
  end

  # A track's default seeds the where: refinements that route replies, so
  # changing it can shift resolution for old clients from the first
  # message on. Server-side and not statically decidable — advisory.
  defp check_tracks(findings, old_ir, new_ir) do
    new_by_name = Map.new(new_ir.tracks, &{&1.name, &1})

    Enum.reduce(old_ir.tracks, findings, fn old_track, acc ->
      case Map.get(new_by_name, old_track.name) do
        %{default: new_default} when new_default != old_track.default ->
          report =
            Report.warning(
              "track :#{old_track.name} changed its default from " <>
                "#{inspect(old_track.default)} to #{inspect(new_default)} — where: " <>
                "refinements over it may resolve replies differently for old clients " <>
                "(not statically decidable; review the change)"
            )
            |> Report.with_code("C010")
            |> maybe_add_source(new_ir.source_file)

          [{:warning, report} | acc]

        _ ->
          acc
      end
    end)
  end

  defp check_states(findings, old_ir, new_ir) do
    Enum.reduce(old_ir.states, findings, fn {name, old_state}, acc ->
      case Map.get(new_ir.states, name) do
        nil ->
          report =
            Report.error(
              "state :#{name} no longer exists — old clients track their session " <>
                "through it"
            )
            |> Report.with_code("C001")
            |> maybe_add_source(old_ir.source_file)
            |> maybe_add_span_label(old_state.span, "defined in the old contract here")

          [{:error, report} | acc]

        new_state ->
          acc
          |> check_terminality(name, old_state, new_state, new_ir)
          |> check_transitions(name, old_state, new_state, old_ir, new_ir)
          |> check_events(name, old_state, new_state, old_ir, new_ir)
          |> check_state_timeout(name, old_state, new_state, new_ir)
      end
    end)
  end

  defp check_terminality(findings, name, old_state, new_state, new_ir) do
    if not old_state.terminal and new_state.terminal do
      report =
        Report.error("state :#{name} became terminal — old clients may still send messages there")
        |> Report.with_code("C002")
        |> maybe_add_source(new_ir.source_file)
        |> maybe_add_span_label(new_state.span, "terminal here")

      [{:error, report} | findings]
    else
      findings
    end
  end

  # Every message an old client may send in this state (including old
  # anystate) must still be accepted, with args only widening.
  defp check_transitions(findings, name, old_state, new_state, old_ir, new_ir) do
    old_effective = effective(old_state, old_ir, [:call, :cast])
    new_effective = effective(new_state, new_ir, [:call, :cast])

    Enum.reduce(old_effective, findings, fn {tag, old_t}, acc ->
      case Map.get(new_effective, tag) do
        nil ->
          report =
            Report.error(
              "message :#{tag} is no longer accepted in state :#{name} — " <>
                "old clients may send it"
            )
            |> Report.with_code("C003")
            |> maybe_add_source(old_ir.source_file)
            |> maybe_add_span_label(old_t.span, "accepted by the old contract here")

          [{:error, report} | acc]

        new_t when new_t.kind != old_t.kind ->
          report =
            Report.error(
              "message :#{tag} in state :#{name} changed kind from " <>
                "#{old_t.kind} to #{new_t.kind}"
            )
            |> Report.with_code("C003")
            |> maybe_add_source(new_ir.source_file)
            |> maybe_add_span_label(new_t.span, "declared here")

          [{:error, report} | acc]

        new_t ->
          acc
          |> check_arg_types(name, tag, old_t, new_t, new_ir)
          |> check_replies(name, tag, old_t, new_t, new_ir)
          |> check_guards(name, tag, old_t, new_t, new_ir)
      end
    end)
  end

  defp check_arg_types(findings, name, tag, old_t, new_t, new_ir) do
    if length(old_t.message_types) != length(new_t.message_types) do
      report =
        Report.error(
          "message :#{tag} in state :#{name} changed arity — old clients send " <>
            "#{length(old_t.message_types)} argument(s), the new contract expects " <>
            "#{length(new_t.message_types)}"
        )
        |> Report.with_code("C004")
        |> maybe_add_source(new_ir.source_file)
        |> maybe_add_span_label(new_t.span, "declared here")

      [{:error, report} | findings]
    else
      old_t.message_types
      |> Enum.zip(new_t.message_types)
      |> Enum.with_index()
      |> Enum.reduce(findings, fn {{old_type, new_type}, idx}, acc ->
        if Type.subtype?(old_type, new_type) do
          acc
        else
          report =
            Report.error(
              "message :#{tag} in state :#{name}: argument #{idx} narrowed from " <>
                "#{Type.to_string(old_type)} to #{Type.to_string(new_type)} — " <>
                "old clients may send values the new contract rejects"
            )
            |> Report.with_code("C004")
            |> maybe_add_source(new_ir.source_file)
            |> maybe_add_span_label(
              Enum.at(new_t.message_arg_spans, idx) || new_t.span,
              "narrowed here"
            )

          [{:error, report} | acc]
        end
      end)
    end
  end

  # Every reply the NEW contract permits must be one the old client
  # understands (covariance, C005) and must lead where the old client
  # will go (C006). "Where the old client goes" is decided by the old
  # client's own first-*value*-match rule, not by the static
  # first-supertype match used here — those agree only when reply types
  # do not overlap. When they do (the `where:` refinement idiom), a
  # value can match more than one branch, so an order-blind comparison is
  # unsound; C006 then falls back to requiring identical reply routing.
  defp check_replies(findings, name, tag, old_t, new_t, new_ir) do
    findings
    |> check_replies_understood(name, tag, old_t, new_t, new_ir)
    |> check_reply_targets(name, tag, old_t, new_t, new_ir)
  end

  # C005: every new reply must be a subtype of some old branch. Sound
  # regardless of overlap — a reply no old branch covers is unhandled.
  defp check_replies_understood(findings, name, tag, old_t, new_t, new_ir) do
    Enum.reduce(new_t.branches, findings, fn new_branch, acc ->
      if Enum.any?(old_t.branches, &Type.subtype?(new_branch.reply_type, &1.reply_type)) do
        acc
      else
        report =
          Report.error(
            "message :#{tag} in state :#{name}: the new contract may reply " <>
              "#{Type.to_string(new_branch.reply_type)}, which old clients do " <>
              "not understand"
          )
          |> Report.with_code("C005")
          |> maybe_add_source(new_ir.source_file)
          |> maybe_add_span_label(new_branch.span, "new reply declared here")

        [{:error, report} | acc]
      end
    end)
  end

  # C006: target divergence. When no reply types overlap, resolution is
  # unambiguous and the per-branch first-supertype comparison is exact.
  # When they overlap, resolution is order-dependent, so certify only if
  # the old and new reply routing is identical (same ordered reply types
  # and targets); any difference is a potential desync.
  defp check_reply_targets(findings, name, tag, old_t, new_t, new_ir) do
    if internal_overlap?(old_t.branches) or internal_overlap?(new_t.branches) do
      check_reply_targets_by_identity(findings, name, tag, old_t, new_t, new_ir)
    else
      check_reply_targets_by_type(findings, name, tag, old_t, new_t, new_ir)
    end
  end

  defp check_reply_targets_by_type(findings, name, tag, old_t, new_t, new_ir) do
    Enum.reduce(new_t.branches, findings, fn new_branch, acc ->
      case Enum.find(old_t.branches, &Type.subtype?(new_branch.reply_type, &1.reply_type)) do
        nil ->
          # Already reported as C005 by check_replies_understood.
          acc

        old_branch ->
          old_next = resolve_next(old_branch.next_state, name)
          new_next = resolve_next(new_branch.next_state, name)

          if old_next == new_next do
            acc
          else
            [
              {:error, reply_target_report(name, tag, new_branch, old_next, new_next, new_ir)}
              | acc
            ]
          end
      end
    end)
  end

  defp check_reply_targets_by_identity(findings, name, tag, old_t, new_t, new_ir) do
    if identical_routing?(old_t.branches, new_t.branches, name) do
      findings
    else
      report =
        Report.error(
          "message :#{tag} in state :#{name}: reply branches overlap (a value can " <>
            "match more than one), so old clients resolve replies by declaration " <>
            "order — the reply routing must stay identical, but it changed"
        )
        |> Report.with_code("C006")
        |> maybe_add_source(new_ir.source_file)
        |> maybe_add_span_label(
          List.first(new_t.branches).span,
          "reply branches changed here"
        )

      [{:error, report} | findings]
    end
  end

  defp reply_target_report(name, tag, new_branch, old_next, new_next, new_ir) do
    Report.error(
      "message :#{tag} in state :#{name}: reply " <>
        "#{Type.to_string(new_branch.reply_type)} now leads to " <>
        ":#{new_next}, but old clients will assume :#{old_next}"
    )
    |> Report.with_code("C006")
    |> maybe_add_source(new_ir.source_file)
    |> maybe_add_span_label(
      new_branch.next_state_span || new_branch.span,
      "diverging target here"
    )
  end

  # Two branches within one list whose reply types can share a value:
  # resolution between them is decided by declaration order.
  defp internal_overlap?(branches) do
    types = Enum.map(branches, & &1.reply_type)

    types
    |> pairs()
    |> Enum.any?(fn {a, b} -> Type.overlap?(a, b) end)
  end

  defp pairs([]), do: []
  defp pairs([head | tail]), do: Enum.map(tail, &{head, &1}) ++ pairs(tail)

  # Same ordered (reply_type, resolved target) for every branch.
  defp identical_routing?(old_branches, new_branches, state) do
    length(old_branches) == length(new_branches) and
      old_branches
      |> Enum.zip(new_branches)
      |> Enum.all?(fn {old_b, new_b} ->
        old_b.reply_type == new_b.reply_type and
          resolve_next(old_b.next_state, state) == resolve_next(new_b.next_state, state)
      end)
  end

  # Every event the NEW server may push must be one old clients handle.
  defp check_events(findings, name, old_state, new_state, old_ir, new_ir) do
    if old_state.terminal do
      findings
    else
      old_events = effective(old_state, old_ir, [:event])
      new_events = effective(new_state, new_ir, [:event])

      Enum.reduce(new_events, findings, fn {tag, new_t}, acc ->
        case Map.get(old_events, tag) do
          nil ->
            report =
              Report.error(
                "the new server may push event :#{tag} in state :#{name}, which " <>
                  "old clients do not handle"
              )
              |> Report.with_code("C007")
              |> maybe_add_source(new_ir.source_file)
              |> maybe_add_span_label(new_t.span, "new event declared here")

            [{:error, report} | acc]

          old_t ->
            acc
            |> check_event_payload(name, tag, old_t, new_t, new_ir)
            |> check_event_target(name, tag, old_t, new_t, new_ir)
        end
      end)
    end
  end

  defp check_event_payload(findings, name, tag, old_t, new_t, new_ir) do
    if length(old_t.message_types) == length(new_t.message_types) and
         new_t.message_types
         |> Enum.zip(old_t.message_types)
         |> Enum.all?(fn {new_type, old_type} -> Type.subtype?(new_type, old_type) end) do
      findings
    else
      report =
        Report.error(
          "event :#{tag} in state :#{name}: the new payload is not covariant with " <>
            "the old — old clients may receive values they cannot handle"
        )
        |> Report.with_code("C008")
        |> maybe_add_source(new_ir.source_file)
        |> maybe_add_span_label(new_t.span, "payload declared here")

      [{:error, report} | findings]
    end
  end

  defp check_event_target(findings, name, tag, old_t, new_t, new_ir) do
    old_next = resolve_next(old_t.to, name)
    new_next = resolve_next(new_t.to, name)

    if old_next == new_next do
      findings
    else
      report =
        Report.error(
          "event :#{tag} in state :#{name} now leads to :#{new_next}, but old " <>
            "clients will assume :#{old_next}"
        )
        |> Report.with_code("C008")
        |> maybe_add_source(new_ir.source_file)
        |> maybe_add_span_label(new_t.span, "diverging target here")

      [{:error, report} | findings]
    end
  end

  # The monitor moves the session on its own; old clients must track it.
  defp check_state_timeout(findings, name, old_state, new_state, new_ir) do
    old_target = timeout_target(old_state)
    new_target = timeout_target(new_state)

    if old_target == new_target do
      # Same target (or both absent): a duration change is behavioral,
      # not protocol-shape.
      findings
    else
      describe = fn
        nil -> "none"
        target -> ":#{target}"
      end

      report =
        Report.error(
          "state :#{name}'s autonomous movement changed — state_timeout target " <>
            "was #{describe.(old_target)}, now #{describe.(new_target)}; old " <>
            "clients track the session through the old behavior"
        )
        |> Report.with_code("C009")
        |> maybe_add_source(new_ir.source_file)
        |> maybe_add_span_label(new_state.span, "state defined here")

      [{:error, report} | findings]
    end
  end

  defp timeout_target(%{state_timeout: {_ms, target}}), do: target
  defp timeout_target(_state), do: nil

  # Guards, `where:` constraints, and updates that change may alter which
  # messages the new contract accepts or how tracks evolve — and track
  # evolution feeds the `where:` refinements that decide reply routing.
  # None is statically decidable, so each is an advisory (C010).
  defp check_guards(findings, name, tag, old_t, new_t, new_ir) do
    guard_changed? =
      normalize_ast(guard_ast(old_t.guard)) != normalize_ast(guard_ast(new_t.guard))

    # Compare the multiset of non-nil constraints, not positionally: a
    # branch added or removed is a reply-structure change (C005/C006), not
    # a constraint change, and must not misfire here as one.
    constraints_changed? =
      constraint_multiset(old_t.branches) != constraint_multiset(new_t.branches)

    update_changed? =
      normalize_ast(guard_ast(old_t.update)) != normalize_ast(guard_ast(new_t.update))

    reason =
      cond do
        guard_changed? or constraints_changed? ->
          "guard or where: constraints changed — the new contract may refuse " <>
            "messages old clients legitimately send"

        update_changed? ->
          "the track update changed — tracks evolve differently, which can shift " <>
            "how where: refinements resolve replies for old clients"

        true ->
          nil
      end

    if reason do
      report =
        Report.warning(
          "message :#{tag} in state :#{name}: #{reason} " <>
            "(not statically decidable; review the change)"
        )
        |> Report.with_code("C010")
        |> maybe_add_source(new_ir.source_file)
        |> maybe_add_span_label(new_t.span, "changed here")

      [{:warning, report} | findings]
    else
      findings
    end
  end

  defp constraint_multiset(branches) do
    branches
    |> Enum.map(&normalize_ast(guard_ast(&1.constraint)))
    |> Enum.reject(&is_nil/1)
    |> Enum.sort()
  end

  defp guard_ast(nil), do: nil
  defp guard_ast(%{ast: ast}), do: ast

  # Line metadata differs across compiles of identical source; strip it
  # so only structural changes register.
  defp normalize_ast(nil), do: nil

  defp normalize_ast(ast) do
    Macro.prewalk(ast, fn
      {name, _meta, ctx} -> {name, [], ctx}
      other -> other
    end)
  end

  # The messages effectively available in a state: its own transitions
  # plus anystate (for non-terminal states), filtered by kind.
  defp effective(state, ir, kinds) do
    transitions =
      if state.terminal do
        state.transitions
      else
        state.transitions ++ ir.anystate
      end

    for t <- transitions, t.kind in kinds, into: %{} do
      {message_tag(t), t}
    end
  end

  defp resolve_next(:__same__, current), do: current
  defp resolve_next(nil, current), do: current
  defp resolve_next(state, _current), do: state
end
