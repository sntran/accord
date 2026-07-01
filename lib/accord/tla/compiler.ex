defmodule Accord.TLA.Compiler do
  @moduledoc """
  TLA+ compilation orchestrator.

  Chains the TLA+ passes: BuildStateSpace → BuildActions → BuildProperties → Emit.
  Produces `.tla` and `.cfg` file content strings from the protocol IR
  and model configuration.
  """

  alias Accord.IR
  alias Accord.Pass.TLA.{BuildActions, BuildProperties, BuildStateSpace, Emit}
  alias Accord.TLA.ModelConfig

  @type result :: %{
          tla: String.t(),
          cfg: String.t(),
          state_space: Accord.TLA.StateSpace.t(),
          actions: [Accord.TLA.Action.t()],
          properties: [Accord.TLA.Property.t()]
        }

  @doc """
  Compiles a protocol IR to TLA+ module and config file strings.

  Returns `{:error, reports}` when the protocol cannot be faithfully
  expressed in TLA+ — the caller decides whether that aborts compilation
  (`tla: :strict`) or degrades to a warning (`tla: :warn`).
  """
  @spec compile(IR.t(), ModelConfig.t()) :: {:ok, result()} | {:error, [Pentiment.Report.t()]}
  def compile(%IR{} = ir, %ModelConfig{} = config) do
    with {:ok, state_space} <- BuildStateSpace.run(ir, config),
         {:ok, actions} <- BuildActions.run(ir, state_space, config),
         {:ok, properties} <- BuildProperties.run(ir, state_space.sessions),
         {:ok, files} <- Emit.run(state_space, actions, properties) do
      {:ok,
       Map.merge(files, %{
         state_space: state_space,
         actions: actions,
         properties: properties
       })}
    end
  end
end
