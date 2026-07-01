defmodule Accord.Compat.Snapshot do
  @moduledoc """
  Persists a protocol's IR so future versions can be checked against it.

  The CI workflow: snapshot the released contract into the repo
  (`mix accord.compat --snapshot MyApp.Protocol priv/contracts/my_app.ir`),
  and gate changes with
  `mix accord.compat MyApp.Protocol --against priv/contracts/my_app.ir`.
  No version macro needed — the snapshot *is* the released version, and
  it cannot drift from what actually shipped.

  ## Security model

  Snapshots deserialize with `binary_to_term` in unsafe mode, like the
  IR baked into protocol modules: lifted function captures require atom
  and external-fun creation. Snapshots are repository artifacts written
  by this tool — the trust boundary is the repo, as with `.exs` config.
  """

  alias Accord.IR

  @magic "ACCORD-IR-SNAPSHOT-1"

  @doc """
  Writes a protocol's IR snapshot.
  """
  @spec save(module() | IR.t(), Path.t()) :: :ok
  def save(protocol, path) do
    ir =
      case protocol do
        %IR{} = ir -> ir
        mod when is_atom(mod) -> mod.__ir__()
      end

    File.mkdir_p!(Path.dirname(path))
    File.write!(path, @magic <> "\n" <> :erlang.term_to_binary(ir))
    :ok
  end

  @doc """
  Loads a snapshot back into an IR.
  """
  @spec load(Path.t()) :: {:ok, IR.t()} | {:error, term()}
  def load(path) do
    with {:ok, content} <- File.read(path),
         [@magic, binary] <- :binary.split(content, "\n"),
         %IR{} = ir <- :erlang.binary_to_term(binary) do
      {:ok, ir}
    else
      {:error, reason} -> {:error, reason}
      _ -> {:error, :not_a_snapshot}
    end
  rescue
    ArgumentError -> {:error, :not_a_snapshot}
  end
end
