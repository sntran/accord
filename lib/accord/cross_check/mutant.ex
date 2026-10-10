defmodule Accord.CrossCheck.Mutant do
  @moduledoc """
  Makes mutants of a protocol IR for the cross-check.

  A correct protocol where both checkers say "pass" proves little. A
  mutant is a small change to the IR: a guard removed, a branch sent to
  a different state, an update removed. Many mutants have violations and
  deadlocks, so the cross-check also compares counterexamples.

  A mutant changes only IR data. It does not change a protocol function,
  so the explorer and the TLA+ translation see the same change.

  Each mutant has a new module name (`<Protocol>.Mutant<N>`), so that its
  TLA+ files do not replace the files of the original protocol.
  """

  alias Accord.IR

  @type mutant :: %{description: String.t(), ir: IR.t()}

  @doc """
  Gives all mutants of an IR, in a fixed order.
  """
  @spec all(IR.t()) :: [mutant()]
  def all(%IR{} = ir) do
    state_names = ir.states |> Map.keys() |> Enum.sort()

    sites =
      for name <- state_names,
          state = Map.fetch!(ir.states, name),
          {transition, t_idx} <- Enum.with_index(state.transitions),
          mutation <- transition_mutations(transition, state_names),
          do: {name, t_idx, transition, mutation}

    transition_mutants =
      Enum.map(sites, fn {name, t_idx, transition, {description, fun}} ->
        mutated = fun.(transition)

        ir =
          update_in(ir.states[name].transitions, fn list ->
            List.replace_at(list, t_idx, mutated)
          end)

        %{description: "#{description} of #{tag(transition)} in :#{name}", ir: ir}
      end)

    removal_mutants =
      for name <- state_names,
          state = Map.fetch!(ir.states, name),
          {transition, t_idx} <- Enum.with_index(state.transitions) do
        ir = update_in(ir.states[name].transitions, &List.delete_at(&1, t_idx))
        %{description: "remove #{tag(transition)} from :#{name}", ir: ir}
      end

    (transition_mutants ++ removal_mutants)
    |> Enum.with_index(1)
    |> Enum.map(fn {mutant, i} ->
      %{mutant | ir: %{mutant.ir | name: Module.concat(ir.name, "Mutant#{i}")}}
    end)
  end

  @doc """
  Gives `count` mutants, selected with a fixed seed.
  """
  @spec sample(IR.t(), non_neg_integer(), integer()) :: [mutant()]
  def sample(ir, count, seed) do
    :rand.seed(:exsss, {seed, 17, 29})
    ir |> all() |> Enum.shuffle() |> Enum.take(count)
  end

  defp transition_mutations(transition, state_names) do
    guard =
      if transition.guard,
        do: [{"remove the guard", &%{&1 | guard: nil}}],
        else: []

    update =
      if transition.update,
        do: [{"remove the update", &%{&1 | update: nil}}],
        else: []

    branches =
      transition.branches
      |> Enum.with_index()
      |> Enum.flat_map(fn {branch, b_idx} ->
        constraint =
          if branch.constraint,
            do: [
              {"remove the where: of branch #{b_idx + 1}",
               &put_branch(&1, b_idx, %{branch | constraint: nil})}
            ],
            else: []

        retarget =
          for target <- state_names, target != branch.next_state do
            {"send branch #{b_idx + 1} to :#{target}",
             &put_branch(&1, b_idx, %{branch | next_state: target})}
          end

        constraint ++ retarget
      end)

    reorder =
      if length(transition.branches) > 1,
        do: [{"reverse the branch order", &%{&1 | branches: Enum.reverse(&1.branches)}}],
        else: []

    retarget_event =
      if transition.kind in [:event, :cast] and transition.to not in [nil, :__same__] do
        for target <- state_names, target != transition.to do
          {"send the step to :#{target}", &%{&1 | to: target}}
        end
      else
        []
      end

    guard ++ update ++ branches ++ reorder ++ retarget_event
  end

  defp put_branch(transition, idx, branch) do
    %{transition | branches: List.replace_at(transition.branches, idx, branch)}
  end

  defp tag(%{message_pattern: pattern}) when is_atom(pattern), do: inspect(pattern)
  defp tag(%{message_pattern: pattern}), do: inspect(elem(pattern, 0))
end
