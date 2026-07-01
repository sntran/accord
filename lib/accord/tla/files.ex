defmodule Accord.TLA.Files do
  @moduledoc """
  Locations of generated TLA+ artifacts under `_build/accord/`.

  Both the compile-time writer (`Accord.Protocol`) and the check task
  (`mix accord.check`) must agree on where a protocol's `.tla` and `.cfg`
  files live. This module is the single source of that layout.

  The file base name must match the TLA+ MODULE name (PascalCase), so the
  last module segment becomes the file name and the leading segments become
  underscored directories: `Lock.Protocol` → `lock/Protocol.tla`.
  """

  @doc """
  Returns `{tla_path, cfg_path}` for a protocol module.
  """
  @spec paths(module()) :: {Path.t(), Path.t()}
  def paths(module_name) do
    parts = Module.split(module_name)
    dir_parts = parts |> Enum.slice(0..-2//1) |> Enum.map(&Macro.underscore/1)

    base_dir = Path.join([Mix.Project.build_path(), "accord" | dir_parts])
    base_name = List.last(parts)

    {
      Path.join(base_dir, "#{base_name}.tla"),
      Path.join(base_dir, "#{base_name}.cfg")
    }
  end

  @doc """
  Writes the generated `.tla` and `.cfg` content for a protocol module.

  Accepts any map carrying `:tla` and `:cfg` keys (the compiler result
  includes more).
  """
  @spec write(module(), %{:tla => String.t(), :cfg => String.t(), optional(atom()) => term()}) ::
          :ok
  def write(module_name, %{tla: tla, cfg: cfg}) do
    {tla_path, cfg_path} = paths(module_name)

    File.mkdir_p!(Path.dirname(tla_path))
    File.write!(tla_path, tla)
    File.write!(cfg_path, cfg)
    :ok
  end

  @doc """
  Deletes any generated artifacts for a protocol module.

  Called when spec generation fails or is disabled, so a stale spec from a
  previous compile can never be silently verified.
  """
  @spec delete(module()) :: :ok
  def delete(module_name) do
    {tla_path, cfg_path} = paths(module_name)

    File.rm(tla_path)
    File.rm(cfg_path)
    :ok
  end
end
