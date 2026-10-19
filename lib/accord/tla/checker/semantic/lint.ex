defmodule Accord.TLA.Checker.Semantic.Lint do
  @moduledoc """
  The warnings of SANY after the semantic checks:

    * W4802: a field of a record constructor has the name of a
      definition or a declaration (`tla2sany.linter.Linter`).
    * W4803, W4804, W4805: the checksums of a PlusCal algorithm and of
      its translation (`pcal.Validator`).

  The checksum of the algorithm is the CRC32 of the PlusCal syntax tree
  that the PlusCal translator makes; this module has no PlusCal
  translator. Thus it finds a changed algorithm only when the recorded
  checksum is not a possible CRC32 text (`Long.toHexString`: lowercase,
  no leading zero, at most 8 digits). The checksum of the translation is
  exact.
  """

  alias Accord.TLA.Checker.Semantic, as: S

  # -- Records (W4802) --

  @doc """
  Checks the record constructors of the modules `mods` (not the
  standard modules). `records`: all the record constructors; `all`: the
  infos of all the modules.
  """
  def check(mods, records, all) do
    by_name = Map.new(all, &{&1.name, &1})

    Enum.each(mods, fn info ->
      own = Enum.filter(records, &(&1.module == info.name))
      ext = extended(info, by_name, MapSet.new()) |> MapSet.delete(info.name)
      others = Enum.filter(records, &(&1.module in ext)) ++ own

      Enum.each(Enum.reverse(own), fn rec ->
        Enum.each(rec.fields, fn {field, rhs} ->
          with %{} = sym <- Map.get(info.ctx, field),
               false <- built_from_decls?(rhs),
               false <- Enum.any?(rec.fields, fn {_, v} -> built_from_decls?(v) end),
               false <-
                 Enum.any?(
                   others,
                   &(same_domain?(&1, rec) and
                       Enum.any?(&1.fields, fn {_, v} -> built_from_decls?(v) end))
                 ) do
            saved = Process.get(:sem_module)
            Process.put(:sem_module, info.name)

            S.warn(
              4802,
              nil,
              "The field name \"#{field}\" in the record constructor is identical to the existing definition or declaration named #{field}, located at #{S.show_pos(sym[:pos])}. The field in the record will not take the value of the #{field} definition or declaration."
            )

            Process.put(:sem_module, saved)
          else
            _ -> :ok
          end
        end)
      end)
    end)
  end

  defp extended(info, by_name, seen) do
    Enum.reduce(Map.get(info, :extends, []), MapSet.put(seen, info.name), fn n, seen ->
      case Map.fetch(by_name, n) do
        {:ok, i} -> if n in seen, do: seen, else: extended(i, by_name, seen)
        :error -> seen
      end
    end)
  end

  defp same_domain?(r1, r2) do
    r1.id == r2.id or
      (length(r1.fields) == length(r2.fields) and
         Enum.all?(r1.fields, fn {f, _} -> Enum.any?(r2.fields, fn {g, _} -> f == g end) end))
  end

  # True if the expression uses (also through definitions) a CONSTANT, a
  # VARIABLE, or a parameter (`Linter.isBuiltFromDeclarations`).
  defp built_from_decls?(node) do
    key = {:lint_built, node[:id]}

    case Process.get(key) do
      nil ->
        r = walk(node, MapSet.new())
        Process.put(key, r)
        r

      r ->
        r
    end
  end

  defp walk(nil, _seen), do: false

  defp walk(%{t: :appl, op: op} = n, seen) do
    found =
      case op do
        %{kind: k} when k in [:constant, :variable, :param, :new] ->
          true

        %{kind: :builtin, name: "BOOLEAN"} ->
          true

        %{name: "Int", mod: "Integers"} ->
          true

        %{name: "Nat", mod: "Naturals"} ->
          true

        %{name: "Real", mod: "Reals"} ->
          true

        %{kind: k, id: id} = d when k in [:def, :fun, :theorem, :instance_def] ->
          if id in seen, do: false, else: walk_def(d, MapSet.put(seen, id))

        _ ->
          false
      end

    found or Enum.any?(n.args || [], &walk(&1, seen)) or
      Enum.any?(Map.get(n, :bounds, []), fn {_, r} -> walk(r, seen) end)
  end

  defp walk(%{t: :let, defs: defs, body: body}, seen) do
    Enum.any?(defs, fn d -> walk(S.def_of(d)[:body], seen) end) or walk(body, seen)
  end

  defp walk(%{t: :label, body: body}, seen), do: walk(body, seen)
  defp walk(_, _seen), do: false

  defp walk_def(%{kind: :instance_def, inst: inst, base_sym: base}, seen) do
    walk_def(base, seen) or Enum.any?(inst.substs, fn {_, e} -> walk(e, seen) end)
  end

  defp walk_def(d, seen), do: walk(S.def_of(d)[:body], seen)

  # -- PlusCal checksums (W4803, W4804, W4805) --

  @doc "Checks the PlusCal checksums of the module `name` in `file`."
  def pluscal(name, file) do
    with {:ok, text} <- File.read(file),
         lines = String.split(text, ~r/\r\n|\r|\n/),
         {first, last} when is_integer(first) <- module_lines(lines),
         mlines = Enum.slice(lines, first..last),
         true <- Enum.any?(mlines, &algorithm_word?/1) do
      validate(name, mlines)
    else
      _ -> :ok
    end
  end

  # The first line and the last line of the module (from the header to
  # the last `====`).
  defp module_lines(lines) do
    first = Enum.find_index(lines, &Regex.match?(~r/^\s*-{4,}\s*MODULE\b/, &1))

    last =
      lines
      |> Enum.with_index()
      |> Enum.filter(fn {l, _} -> Regex.match?(~r/^\s*={4,}/, l) end)
      |> List.last()

    case {first, last} do
      {f, {_, l}} when is_integer(f) and l > f -> {f, l}
      {f, _} when is_integer(f) -> {f, length(lines) - 1}
      _ -> nil
    end
  end

  defp algorithm_word?(line) do
    case :binary.match(line, "algorithm") do
      {i, _} -> i > 0
      :nomatch -> false
    end
  end

  @checksum ~r/\\\* BEGIN TRANSLATION\s+\(\s*((?i)ch(ec)?ksum\(p(lus)?cal\)(?-i))\s*(=\s*"(?<pcal>[0-9A-Fa-f]*)"|\\in\s*STRING)\s*\/\\\s*((?i)ch(ec)?ksum\(tla\+?\)(?-i))\s*(=\s*"(?<tla>[0-9A-Fa-f]*)"|\\in\s*STRING)\s*\)/

  defp validate(name, lines) do
    detabbed = Enum.map(lines, &detab/1)
    closing = Enum.find_index(detabbed, &Regex.match?(~r/^\s*={4,}\s*$/, &1)) || length(detabbed)

    found_begin =
      detabbed
      |> Enum.take(closing)
      |> Enum.any?(&(String.contains?(&1, "--algorithm") or String.contains?(&1, "--fair")))

    begin_t = token_pair(detabbed, 0, "BEGIN", "TRANSLATION")
    end_t = begin_t && token_pair(detabbed, begin_t + 1, "END", "TRANSLATION")

    with true <- found_begin,
         b when is_integer(b) <- begin_t,
         e when is_integer(e) <- end_t,
         %{} = m <- Regex.named_captures(@checksum, Enum.at(detabbed, b)) do
      pcal = Map.get(m, "pcal", "")
      tla = Map.get(m, "tla", "")

      # An empty group: `\in STRING` (no check).
      pcal_div = pcal != "" and not Regex.match?(~r/^(0|[1-9a-f][0-9a-f]{0,7})$/, pcal)

      tla_div =
        tla != "" and
          tla !=
            lines
            |> Enum.slice((b + 1)..(e - 1)//1)
            |> Enum.join()
            |> :erlang.crc32()
            |> Integer.to_string(16)
            |> String.downcase()

      saved = Process.get(:sem_module)
      Process.put(:sem_module, name)

      cond do
        pcal_div and tla_div ->
          S.warn(
            4803,
            nil,
            "Both the PlusCal algorithm and its TLA+ translation in module #{name} have changed since the last translation."
          )

        tla_div ->
          S.warn(
            4805,
            nil,
            "The TLA+ translation in module #{name} has changed since its last translation."
          )

        pcal_div ->
          S.warn(
            4804,
            nil,
            "The PlusCal algorithm in module #{name} has changed since its last translation."
          )

        true ->
          :ok
      end

      Process.put(:sem_module, saved)
    else
      _ -> :ok
    end
  end

  # The first line at or after `from` with `t1`, spaces, and `t2`
  # (`trans.findTokenPair`).
  defp token_pair(lines, from, t1, t2) do
    lines
    |> Enum.with_index()
    |> Enum.drop(from)
    |> Enum.find_value(fn {line, i} ->
      case :binary.match(line, t1) do
        {col, len} ->
          rest = binary_part(line, col + len, byte_size(line) - col - len)
          trimmed = String.trim_leading(rest, " ")
          next = col + len + byte_size(rest) - byte_size(trimmed)

          case :binary.match(line, t2) do
            {^next, _} when trimmed != "" -> i
            _ -> nil
          end

        :nomatch ->
          nil
      end
    end)
  end

  # Tabs to spaces, to the next column that is a multiple of 8.
  defp detab(line) do
    line
    |> String.graphemes()
    |> Enum.reduce("", fn
      "\t", acc -> acc <> String.duplicate(" ", 8 - rem(String.length(acc), 8))
      c, acc -> acc <> c
    end)
  end
end
