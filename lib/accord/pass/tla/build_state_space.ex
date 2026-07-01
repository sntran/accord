defmodule Accord.Pass.TLA.BuildStateSpace do
  @moduledoc """
  TLA+ pass: IR → StateSpace.

  Produces VARIABLES, TypeInvariant, and Init predicate from states,
  tracks, and roles. For two-party protocols: a single `state` variable
  plus one variable per track, plus one auxiliary counter per
  correspondence check.
  """

  alias Accord.IR
  alias Accord.TLA.{ModelConfig, StateSpace}
  alias Pentiment.Report

  import Accord.Pass.Helpers, only: [maybe_add_source: 2, maybe_add_span_label: 3]

  @spec run(IR.t(), ModelConfig.t()) :: {:ok, StateSpace.t()} | {:error, [Report.t()]}
  def run(%IR{} = ir, %ModelConfig{} = config) do
    case collect_init_errors(ir, config) do
      [] -> {:ok, build_state_space(ir, config)}
      errors -> {:error, errors}
    end
  end

  defp build_state_space(%IR{} = ir, %ModelConfig{} = config) do
    states = Map.keys(ir.states) |> Enum.map(&state_to_tla/1)

    # Build variable list.
    state_var = %{
      name: "state",
      type: state_type_expr(states),
      init: ~s("#{ir.initial}")
    }

    track_vars =
      Enum.map(ir.tracks, fn track ->
        domain = ModelConfig.resolve_domain(config, track.name, track.type)
        type_str = ModelConfig.domain_to_tla(domain)
        init_value = ModelConfig.resolve_init(config, track.name, track.default)

        # Include NULL in the type set when the track can be nil.
        type_str =
          if track.default == nil do
            "#{type_str} \\union {NULL}"
          else
            type_str
          end

        %{
          name: Atom.to_string(track.name),
          type: type_str,
          init: value_to_tla(init_value)
        }
      end)

    # Build correspondence counter variables.
    correspondences = build_correspondences(ir)

    correspondence_vars =
      Enum.map(correspondences, fn corr ->
        domain =
          ModelConfig.resolve_domain(
            config,
            String.to_atom(corr.counter_var),
            :correspondence_counter
          )

        type_str = ModelConfig.domain_to_tla(domain)
        %{name: corr.counter_var, type: type_str, init: "0"}
      end)

    variables = [state_var] ++ track_vars ++ correspondence_vars

    # Build TypeInvariant.
    type_invariant = build_type_invariant(variables)

    # Build Init.
    init = build_init(variables)

    # Build module name.
    module_name =
      ir.name
      |> Module.split()
      |> List.last()

    # Collect model value constants needed for the cfg.
    constants = collect_constants(ir, config)

    %StateSpace{
      module_name: module_name,
      variables: variables,
      type_invariant: type_invariant,
      init: init,
      states: states,
      correspondences: correspondences,
      constants: constants,
      state_constraint: config.state_constraint
    }
  end

  defp state_to_tla(state_name), do: Atom.to_string(state_name)

  defp state_type_expr(states) do
    elements = Enum.map_join(states, ", ", &~s("#{&1}"))
    "{#{elements}}"
  end

  # A track whose init value falls outside its model domain would make Init
  # violate TypeInvariant on the very first state — report it at compile
  # time with a span instead of letting TLC produce a confusing violation.
  defp collect_init_errors(%IR{} = ir, %ModelConfig{} = config) do
    Enum.flat_map(ir.tracks, fn track ->
      domain = ModelConfig.resolve_domain(config, track.name, track.type)
      init_value = ModelConfig.resolve_init(config, track.name, track.default)

      if value_in_domain?(init_value, domain) do
        []
      else
        [init_error(ir, track, init_value, domain)]
      end
    end)
  end

  defp init_error(ir, track, init_value, domain) do
    Report.error(
      "track :#{track.name} default #{inspect(init_value)} is outside " <>
        "its model domain #{inspect_domain(domain)}"
    )
    |> Report.with_code("E044")
    |> Report.with_help(
      "add init: %{#{track.name}: <value>} to your model config, or widen the domain"
    )
    |> maybe_add_source(ir.source_file)
    |> maybe_add_span_label(track.span, "declared here")
  end

  defp value_in_domain?(nil, _domain), do: true
  defp value_in_domain?(value, %Range{} = range) when is_integer(value), do: value in range
  defp value_in_domain?(value, list) when is_list(list), do: value in list
  defp value_in_domain?(_value, {:model_values, _}), do: true
  defp value_in_domain?(_value, _domain), do: true

  defp inspect_domain(%Range{first: first, last: last}), do: "#{first}..#{last}"
  defp inspect_domain(domain), do: inspect(domain)

  defp value_to_tla(nil), do: "NULL"
  defp value_to_tla(true), do: "TRUE"
  defp value_to_tla(false), do: "FALSE"
  defp value_to_tla(n) when is_integer(n), do: Integer.to_string(n)
  defp value_to_tla(s) when is_binary(s), do: ~s("#{s}")
  defp value_to_tla(a) when is_atom(a), do: ~s("#{a}")
  defp value_to_tla(_), do: "NULL"

  defp build_type_invariant(variables) do
    conjuncts =
      Enum.map_join(variables, "\n    /\\ ", fn var ->
        "#{var.name} \\in #{var.type}"
      end)

    "TypeInvariant == \n    /\\ #{conjuncts}"
  end

  defp build_init(variables) do
    conjuncts =
      Enum.map_join(variables, "\n    /\\ ", fn var ->
        "#{var.name} = #{var.init}"
      end)

    "Init == \n    /\\ #{conjuncts}"
  end

  # Collects all model value constant names from resolved domains.
  # Includes NULL if any variable has a nil default.
  defp collect_constants(%IR{} = ir, %ModelConfig{} = config) do
    # Gather all domains: track domains + message type domains.
    track_domains =
      Enum.map(ir.tracks, fn track ->
        ModelConfig.resolve_domain(config, track.name, track.type)
      end)

    msg_type_domains =
      ir.states
      |> Enum.flat_map(fn {_name, state} ->
        state.transitions ++ if(state.terminal, do: [], else: ir.anystate)
      end)
      |> Enum.flat_map(fn transition ->
        Enum.map(transition.message_types, fn type ->
          ModelConfig.resolve_domain(config, :_, type)
        end)
      end)

    # Also include reply type domains for transitions with branches.
    reply_type_domains =
      ir.states
      |> Enum.flat_map(fn {_name, state} -> state.transitions end)
      |> Enum.flat_map(fn transition ->
        Enum.flat_map(transition.branches, fn branch ->
          extract_reply_types(branch.reply_type)
          |> Enum.map(fn type -> ModelConfig.resolve_domain(config, :_, type) end)
        end)
      end)

    all_domains = track_domains ++ msg_type_domains ++ reply_type_domains

    model_value_names =
      all_domains
      |> Enum.flat_map(&extract_model_value_names/1)
      |> Enum.uniq()
      |> Enum.sort()

    # Add NULL if any track defaults to nil.
    has_null = Enum.any?(ir.tracks, &(&1.default == nil))

    if has_null do
      Enum.uniq(["NULL" | model_value_names])
    else
      model_value_names
    end
  end

  defp extract_model_value_names({:model_values, count}) when is_integer(count) do
    Enum.map(1..count, &"mv#{&1}")
  end

  defp extract_model_value_names({:model_values, names}) when is_list(names) do
    Enum.map(names, &Atom.to_string/1)
  end

  defp extract_model_value_names(_), do: []

  defp extract_reply_types({:tagged, _tag, inner}), do: [inner]
  defp extract_reply_types(_), do: []

  defp build_correspondences(%IR{properties: properties}) do
    properties
    |> Enum.flat_map(fn prop ->
      prop.checks
      # Keyed correspondence (by:) counts per key value; a single global
      # counter would model something else, so those checks are
      # runtime-only and get no counter variable.
      |> Enum.filter(&(&1.kind == :correspondence and Map.get(&1.spec, :by) == nil))
      |> Enum.map(fn check ->
        open = check.spec.open
        close = check.spec.close
        counter_var = "#{open}_pending"
        %{open: open, close: close, counter_var: counter_var}
      end)
    end)
  end
end
