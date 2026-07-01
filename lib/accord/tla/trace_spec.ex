defmodule Accord.TLA.TraceSpec do
  @moduledoc """
  Replays a captured runtime trace against the generated TLA+ spec.

  The other checks cannot see accord's own translation bugs: TLC checks
  the (possibly mistranslated) model against itself, and the
  property-based exerciser checks the server against the monitor without
  ever consulting the model. Trace validation closes the loop — the
  trace is what actually happened, and the spec must accept it as a
  behavior. TLC walks the recorded states in lockstep with `Next`; a
  step no action can reproduce is reported as a deadlock at that index.

  Domains are synthesized from the values actually observed in the
  trace, so replay needs no hand-tuned model config and no truncation:
  a fence token of 12841 is simply in the domain.
  """

  alias Accord.IR
  alias Accord.TLA.{Compiler, ModelConfig}
  alias Accord.Trace.Event

  @type result :: %{
          module_name: String.t(),
          base_tla: String.t(),
          base_cfg: String.t(),
          trace_tla: String.t(),
          trace_cfg: String.t()
        }

  @doc """
  Generates the base spec (with per-trace domains) and the replay module.

  Returns `{:error, {:unsupported_term, value}}` when the trace contains
  values with no TLA+ literal rendering (pids, refs, functions).
  """
  @spec generate(module(), [Event.t()]) :: {:ok, result()} | {:error, term()}
  def generate(protocol_mod, events) do
    ir = protocol_mod.__ir__()

    with :ok <- validate_terms(ir, events),
         config = derive_config(ir, events),
         {:ok, base} <- Compiler.compile(ir, config) do
      module_name = base.state_space.module_name
      trace_name = module_name <> "Trace"
      pinned = pinned_vars(ir)

      {:ok,
       %{
         module_name: trace_name,
         base_tla: base.tla,
         base_cfg: base.cfg,
         trace_tla: render_trace_module(trace_name, module_name, ir, events, pinned),
         trace_cfg: render_trace_cfg(base.cfg)
       }}
    end
  end

  # -- Per-trace domains --

  # Track domains are the exact observed values; message/reply integers
  # feed the integer type pools (a superset only gives TLC more
  # witnesses to choose from, which is sound for replay).
  defp derive_config(%IR{} = ir, events) do
    snapshots = [initial_tracks(ir) | Enum.map(events, & &1.tracks)]

    track_domains =
      for track <- ir.tracks, into: %{} do
        observed =
          snapshots
          |> Enum.map(&Map.get(&1, track.name))
          |> Enum.reject(&is_nil/1)
          |> Enum.uniq()
          |> Enum.sort()

        {track.name, if(observed == [], do: [0], else: observed)}
      end

    ints = observed_ints(events)
    pos = ints |> Enum.filter(&(&1 > 0)) |> non_empty([1])
    non_neg = ints |> Enum.filter(&(&1 >= 0)) |> non_empty([0])
    atoms = observed_atoms(events) |> non_empty([:a])

    type_domains = %{
      pos_integer: pos,
      non_neg_integer: non_neg,
      integer: non_empty(ints, [0]),
      atom: atoms,
      term: atoms,
      string: observed_strings(events) |> non_empty(["s"]),
      binary: observed_strings(events) |> non_empty(["s"])
    }

    %ModelConfig{domains: Map.merge(type_domains, track_domains), max_list_length: 3}
  end

  defp non_empty([], fallback), do: fallback
  defp non_empty(values, _fallback), do: Enum.sort(Enum.uniq(values))

  defp payload_values(events) do
    Enum.flat_map(events, fn event ->
      message_args(event.message) ++ message_args(event.reply)
    end)
  end

  defp message_args(nil), do: []
  defp message_args(value) when is_tuple(value), do: value |> Tuple.to_list() |> tl()
  defp message_args(_scalar), do: []

  defp observed_ints(events) do
    events |> payload_values() |> Enum.filter(&is_integer/1) |> Enum.uniq()
  end

  defp observed_atoms(events) do
    events
    |> payload_values()
    |> Enum.filter(&(is_atom(&1) and not is_boolean(&1) and &1 != nil))
    |> Enum.uniq()
  end

  defp observed_strings(events) do
    events |> payload_values() |> Enum.filter(&is_binary/1) |> Enum.uniq()
  end

  defp validate_terms(ir, events) do
    values =
      payload_values(events) ++
        Enum.flat_map(events, fn event -> Map.values(event.tracks) end) ++
        Map.values(initial_tracks(ir))

    case Enum.find(values, &(not renderable?(&1))) do
      nil -> :ok
      bad -> {:error, {:unsupported_term, bad}}
    end
  end

  defp renderable?(value) do
    is_integer(value) or is_atom(value) or is_binary(value)
  end

  # -- Trace module rendering --

  defp initial_tracks(%IR{} = ir) do
    Map.new(ir.tracks, fn track -> {track.name, track.default} end)
  end

  # State plus tracks; correspondence counters follow Next unpinned.
  defp pinned_vars(%IR{} = ir) do
    for track <- ir.tracks, do: Atom.to_string(track.name)
  end

  defp render_trace_module(trace_name, base_name, ir, events, pinned) do
    records =
      [{Atom.to_string(ir.initial), initial_tracks(ir)}] ++
        Enum.map(events, fn event ->
          {Atom.to_string(event.next_state), event.tracks}
        end)

    trace_entries =
      Enum.map_join(records, ",\n", fn {state, tracks} ->
        fields =
          ["state |-> \"#{state}\""] ++
            Enum.map(pinned, fn name ->
              "#{name} |-> #{render_value(Map.get(tracks, String.to_existing_atom(name)))}"
            end)

        "    [#{Enum.join(fields, ", ")}]"
      end)

    # TLA+ bulleted conjunctions are indentation-sensitive: every pin
    # must sit at the same column as the other conjuncts in the first
    # disjunct (7 spaces).
    pins =
      Enum.map_join(["state" | pinned], "\n       ", fn var ->
        "/\\ #{var}' = Trace[ti + 1].#{var}"
      end)

    """
    ---- MODULE #{trace_name} ----
    EXTENDS #{base_name}

    VARIABLE ti

    \\* One record per reached state: the initial state, then each
    \\* transition's recorded successor.
    Trace == <<
    #{trace_entries}
    >>

    TInit ==
        /\\ Init
        /\\ ti = 1

    \\* Each replay step must be SOME protocol action producing exactly
    \\* the recorded successor. A step no action can reproduce deadlocks
    \\* here, with ti naming the failing trace index.
    TNext ==
        \\/ /\\ ti < Len(Trace)
           /\\ Next
           /\\ ti' = ti + 1
           #{pins}
        \\/ /\\ ti = Len(Trace)
           /\\ UNCHANGED <<vars, ti>>

    TSpec == TInit /\\ [][TNext]_<<vars, ti>>

    \\* The full trace was replayed.
    Complete == ti = Len(Trace)
    ====
    """
  end

  # The replay cfg: TSpec plus the base module's constants.
  defp render_trace_cfg(base_cfg) do
    inherited =
      base_cfg
      |> String.split("\n")
      |> Enum.filter(&String.starts_with?(&1, "CONSTANT"))

    Enum.join(["SPECIFICATION TSpec", "" | inherited], "\n") <> "\n"
  end

  defp render_value(nil), do: "NULL"
  defp render_value(true), do: "TRUE"
  defp render_value(false), do: "FALSE"
  defp render_value(n) when is_integer(n), do: Integer.to_string(n)
  defp render_value(s) when is_binary(s), do: ~s("#{s}")
  defp render_value(a) when is_atom(a), do: ~s("#{a}")
end
