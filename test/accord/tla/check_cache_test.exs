defmodule Accord.TLA.CheckCacheTest do
  use ExUnit.Case, async: true

  alias Accord.TLA.CheckCache

  @moduletag :tmp_dir

  defp write_inputs(tmp_dir, tla_content) do
    tla = Path.join(tmp_dir, "Spec.tla")
    cfg = Path.join(tmp_dir, "Spec.cfg")
    jar = Path.join(tmp_dir, "tla2tools.jar")
    File.write!(tla, tla_content)
    File.write!(cfg, "SPECIFICATION Spec")
    File.write!(jar, "not a real jar")
    {tla, cfg, jar}
  end

  test "identical inputs produce identical keys" do
    {tla, cfg, jar} = write_inputs(System.tmp_dir!(), "---- MODULE Spec ----")

    assert CheckCache.key(tla, cfg, jar, true) == CheckCache.key(tla, cfg, jar, true)
  end

  test "changing the spec changes the key", %{tmp_dir: tmp_dir} do
    {tla, cfg, jar} = write_inputs(tmp_dir, "---- MODULE Spec ----")
    key1 = CheckCache.key(tla, cfg, jar, true)

    File.write!(tla, "---- MODULE Spec ----\nchanged")
    key2 = CheckCache.key(tla, cfg, jar, true)

    refute key1 == key2
  end

  test "the deadlock setting is part of the key", %{tmp_dir: tmp_dir} do
    {tla, cfg, jar} = write_inputs(tmp_dir, "---- MODULE Spec ----")

    refute CheckCache.key(tla, cfg, jar, true) == CheckCache.key(tla, cfg, jar, false)
  end

  test "hit?/put round-trip" do
    cache = CheckCache.put(%{}, "LockProtocol", "abc")

    assert CheckCache.hit?(cache, "LockProtocol", "abc")
    refute CheckCache.hit?(cache, "LockProtocol", "def")
    refute CheckCache.hit?(cache, "OtherProtocol", "abc")
  end

  test "load tolerates a corrupt cache file" do
    # Write garbage where the cache lives, load, and expect empty.
    path = Path.join([Mix.Project.build_path(), "accord", ".check_cache"])
    File.mkdir_p!(Path.dirname(path))
    original = File.read(path)
    File.write!(path, "garbage not a term")

    assert CheckCache.load() == %{}

    # Restore whatever was there.
    case original do
      {:ok, content} -> File.write!(path, content)
      _ -> File.rm(path)
    end
  end
end
