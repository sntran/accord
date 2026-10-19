defmodule Accord.TLA.CheckCache do
  @moduledoc """
  Content-hash cache for `mix accord.check`.

  TLC pays a JVM startup cost per protocol (hundreds of milliseconds
  even for tiny state spaces), which makes "check on every push" feel
  expensive. Specs are emitted deterministically, so a content hash is
  an exact cache key: when the `.tla`, `.cfg`, TLC jar, and deadlock
  setting are unchanged since the last PASSING run, the pass is
  replayed from the cache.

  Only passes are cached — a failing protocol is the one being iterated
  on, and its diagnostics should always be fresh. `--force` bypasses the
  cache entirely.

  Stored as a serialized map at `_build/accord/.check_cache`.
  """

  @type t :: %{String.t() => String.t()}

  @doc """
  Loads the cache, tolerating a missing or corrupt file.
  """
  @spec load() :: t()
  def load do
    case File.read(cache_path()) do
      {:ok, binary} ->
        case safe_decode(binary) do
          %{} = cache -> cache
          _ -> %{}
        end

      {:error, _} ->
        %{}
    end
  end

  @doc """
  Persists the cache.
  """
  @spec save(t()) :: :ok
  def save(cache) do
    path = cache_path()
    File.mkdir_p!(Path.dirname(path))
    File.write!(path, :erlang.term_to_binary(cache))
    :ok
  end

  @doc """
  The cache key for a protocol's current inputs: spec content, cfg
  content, the engine, and whether deadlock checking is enabled.

  The engine is the path of a TLC jar (its path, size and mtime go in
  the key — a TLC upgrade invalidates), or an engine identity from
  `Accord.TLA.Engine.identity/1` (a new checker build invalidates).
  """
  @spec key(Path.t(), Path.t(), String.t(), boolean()) :: String.t()
  def key(tla_path, cfg_path, engine, deadlock?) do
    engine_parts =
      if File.regular?(engine) do
        stat = File.stat!(engine, time: :posix)
        [engine, Integer.to_string(stat.size), Integer.to_string(stat.mtime)]
      else
        [engine]
      end

    :sha256
    |> :crypto.hash(
      [File.read!(tla_path), File.read!(cfg_path)] ++ engine_parts ++ [to_string(deadlock?)]
    )
    |> Base.encode16()
  end

  @doc """
  Whether the cache records a pass for this protocol with these inputs.
  """
  @spec hit?(t(), String.t(), String.t()) :: boolean()
  def hit?(cache, module_name, key), do: Map.get(cache, module_name) == key

  @doc """
  Records a pass.
  """
  @spec put(t(), String.t(), String.t()) :: t()
  def put(cache, module_name, key), do: Map.put(cache, module_name, key)

  defp cache_path do
    Path.join([Mix.Project.build_path(), "accord", ".check_cache"])
  end

  # The cache is build metadata written only by this tool, but decoding
  # defensively costs nothing.
  defp safe_decode(binary) do
    :erlang.binary_to_term(binary, [:safe])
  rescue
    _ -> %{}
  end
end
