defmodule Accord.TLA.Files do
  @moduledoc """
  Locations of generated TLA+ artifacts under `_build/accord/`.

  Both the compile-time writer (`Accord.Protocol`) and the check task
  (`mix accord.check`) must agree on where a protocol's `.tla` and `.cfg`
  files live. This module is the single source of that layout.

  The file base name must match the TLA+ MODULE name, which is the full
  concatenated module path so every protocol is unique in the flat
  directory: `Lock.Protocol` → `_build/accord/LockProtocol.tla`.
  """

  @doc """
  Returns `{tla_path, cfg_path}` for a protocol module.
  """
  @spec paths(module()) :: {Path.t(), Path.t()}
  def paths(module_name) do
    base_dir = Path.join(Mix.Project.build_path(), "accord")
    base_name = tla_module_name(module_name)

    {
      Path.join(base_dir, "#{base_name}.tla"),
      Path.join(base_dir, "#{base_name}.cfg")
    }
  end

  @doc """
  The TLA+ MODULE name for a protocol module.

  The full concatenated path keeps the common case unique in the flat
  directory (`Lock.Protocol` and `Queue.Protocol` do not both become
  `Protocol`). It is deliberately *not* injective: two module paths can
  concatenate to the same name (`A.BC` and `AB.C` both → `ABC`), and the
  build directory is case-insensitive on macOS/Windows (`Foo.Bar` and
  `Foo.BAR` collide as files). Those rare collisions are caught loudly by
  `name_collisions/1` before any check trusts an ambiguous artifact,
  rather than silently verifying the wrong spec.
  """
  @spec tla_module_name(module()) :: String.t()
  def tla_module_name(module_name) do
    module_name |> Module.split() |> Enum.join()
  end

  @doc """
  Finds protocol modules whose generated artifacts would collide.

  Two distinct modules collide when their `tla_module_name/1` values are
  equal ignoring case — either an exact concatenation clash or a
  case-only difference that a case-insensitive filesystem cannot tell
  apart. Both would share one flat `.tla`/`.cfg` file, so the last
  compiled wins and a check could verify a spec generated from a
  different module. Returns one `{name, modules}` entry per collision
  (empty when there are none); `modules` is sorted for stable reporting.
  """
  @spec name_collisions([module()]) :: [{String.t(), [module()]}]
  def name_collisions(modules) do
    modules
    |> Enum.uniq()
    |> Enum.group_by(fn mod -> String.downcase(tla_module_name(mod)) end)
    |> Enum.filter(fn {_folded, mods} -> length(mods) > 1 end)
    |> Enum.map(fn {_folded, mods} ->
      sorted = Enum.sort(mods)
      {tla_module_name(hd(sorted)), sorted}
    end)
    |> Enum.sort()
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
