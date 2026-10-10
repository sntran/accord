defmodule Accord.CrossCheck.TLAValue do
  @moduledoc """
  TLA+ values as Elixir terms, for the comparison of TLC states with
  explorer states.

  A value is one of:

  - an integer, `true`, or `false`
  - `{:str, binary}` — a string
  - `{:mv, binary}` — a model value, such as `mv1`, `s1`, or `NULL`
  - `{:seq, [value]}` — a sequence
  - `{:set, [value]}` — a set, sorted
  - `{:rec, [{binary, value}]}` — a record, sorted by field
  - `{:fun, [{value, value}]}` — a function, sorted by key

  `parse/1` reads the text that TLC prints. `render/1` writes TLA+ text.
  `from_state/2` converts an explorer state into a map from variable
  name to value.
  """

  alias Accord.Explore.Model

  @type t ::
          integer()
          | boolean()
          | {:str, String.t()}
          | {:mv, String.t()}
          | {:seq, [t()]}
          | {:set, [t()]}
          | {:rec, [{String.t(), t()}]}
          | {:fun, [{t(), t()}]}

  # -- Explorer states --

  @doc """
  Converts an explorer state into a map from TLA+ variable name to value.

  With more than one session, each per-session variable is a function
  from the session model values (`s1`, `s2`, ...) to the value.
  """
  @spec from_state(Model.t(), Model.state()) :: %{String.t() => t()}
  def from_state(%Model{} = model, {sessions, shared}) do
    session_list = Tuple.to_list(sessions)

    per_session =
      [{"state", fn {name, _, _} -> {:str, Atom.to_string(name)} end}] ++
        Enum.map(model.session_tracks, fn track ->
          {Atom.to_string(track), fn {_, tracks, _} -> from_value(model, tracks[track]) end}
        end) ++
        Enum.map(model.counters, fn %{var: var} ->
          {var, fn {_, _, counters} -> Map.fetch!(counters, var) end}
        end)

    session_vars =
      Map.new(per_session, fn {var, get} ->
        value =
          if model.sessions > 1 do
            session_list
            |> Enum.with_index(1)
            |> Enum.map(fn {session, i} -> {{:mv, "s#{i}"}, get.(session)} end)
            |> then(&{:fun, Enum.sort(&1)})
          else
            get.(hd(session_list))
          end

        {var, value}
      end)

    shared_vars =
      Map.new(shared, fn {track, value} -> {Atom.to_string(track), from_value(model, value)} end)

    Map.merge(session_vars, shared_vars)
  end

  @doc """
  Converts one Elixir value of the model into a TLA+ value.
  """
  @spec from_value(Model.t(), term()) :: t()
  def from_value(_model, nil), do: {:mv, "NULL"}
  def from_value(_model, value) when is_boolean(value) or is_integer(value), do: value

  def from_value(model, value) when is_atom(value) do
    if MapSet.member?(model.model_values, value),
      do: {:mv, Atom.to_string(value)},
      else: {:str, Atom.to_string(value)}
  end

  def from_value(_model, value) when is_binary(value), do: {:str, value}

  def from_value(model, list) when is_list(list),
    do: {:seq, Enum.map(list, &from_value(model, &1))}

  def from_value(model, tuple) when is_tuple(tuple),
    do: {:seq, tuple |> Tuple.to_list() |> Enum.map(&from_value(model, &1))}

  def from_value(model, %{} = map) do
    {:rec, map |> Enum.map(fn {k, v} -> {to_string(k), from_value(model, v)} end) |> Enum.sort()}
  end

  # -- Render --

  @doc """
  Writes a value as TLA+ text.
  """
  @spec render(t()) :: String.t()
  def render(true), do: "TRUE"
  def render(false), do: "FALSE"
  def render(n) when is_integer(n), do: Integer.to_string(n)
  def render({:str, s}), do: ~s(") <> String.replace(s, ~s("), ~s(\\")) <> ~s(")
  def render({:mv, name}), do: name
  def render({:seq, items}), do: "<<" <> Enum.map_join(items, ", ", &render/1) <> ">>"
  def render({:set, items}), do: "{" <> Enum.map_join(items, ", ", &render/1) <> "}"

  def render({:rec, fields}),
    do: "[" <> Enum.map_join(fields, ", ", fn {k, v} -> "#{k} |-> #{render(v)}" end) <> "]"

  def render({:fun, []}), do: "<<>>"

  def render({:fun, pairs}),
    do:
      "(" <> Enum.map_join(pairs, " @@ ", fn {k, v} -> "#{render(k)} :> #{render(v)}" end) <> ")"

  # -- Parse --

  @doc """
  Reads a value from the text that TLC prints.
  """
  @spec parse(String.t()) :: {:ok, t()} | {:error, String.t()}
  def parse(text) do
    with {:ok, tokens} <- tokenize(text, []),
         {:ok, value, []} <- value(tokens) do
      {:ok, value}
    else
      {:ok, _value, rest} -> {:error, "unexpected tokens: #{inspect(Enum.take(rest, 5))}"}
      {:error, _} = error -> error
    end
  end

  @doc "Same as `parse/1`, but raises on bad text."
  @spec parse!(String.t()) :: t()
  def parse!(text) do
    case parse(text) do
      {:ok, value} ->
        value

      {:error, reason} ->
        raise ArgumentError, "cannot parse TLA+ value #{inspect(text)}: #{reason}"
    end
  end

  @symbols [":>", "@@", "|->", "<<", ">>", "(", ")", "[", "]", "{", "}", ","]

  defp tokenize("", acc), do: {:ok, Enum.reverse(acc)}

  defp tokenize(<<c, rest::binary>>, acc) when c in [?\s, ?\n, ?\t, ?\r], do: tokenize(rest, acc)

  defp tokenize(<<?", _::binary>> = text, acc) do
    case Regex.run(~r/^"((?:\\.|[^"\\])*)"/s, text) do
      [whole, body] ->
        str = body |> String.replace(~s(\\"), ~s(")) |> String.replace("\\\\", "\\")

        tokenize(binary_part(text, byte_size(whole), byte_size(text) - byte_size(whole)), [
          {:str, str} | acc
        ])

      nil ->
        {:error, "unterminated string"}
    end
  end

  defp tokenize(text, acc) do
    cond do
      sym = Enum.find(@symbols, &String.starts_with?(text, &1)) ->
        tokenize(binary_part(text, byte_size(sym), byte_size(text) - byte_size(sym)), [
          {:sym, sym} | acc
        ])

      match = Regex.run(~r/^-?\d+/, text) ->
        [num] = match
        rest = binary_part(text, byte_size(num), byte_size(text) - byte_size(num))
        tokenize(rest, [{:int, String.to_integer(num)} | acc])

      match = Regex.run(~r/^[A-Za-z_][A-Za-z0-9_]*/, text) ->
        [id] = match
        rest = binary_part(text, byte_size(id), byte_size(text) - byte_size(id))
        tokenize(rest, [{:id, id} | acc])

      true ->
        {:error, "unexpected text: #{String.slice(text, 0, 20)}"}
    end
  end

  defp value([{:int, n} | rest]), do: {:ok, n, rest}
  defp value([{:str, s} | rest]), do: {:ok, {:str, s}, rest}
  defp value([{:id, "TRUE"} | rest]), do: {:ok, true, rest}
  defp value([{:id, "FALSE"} | rest]), do: {:ok, false, rest}
  defp value([{:id, id} | rest]), do: {:ok, {:mv, id}, rest}

  defp value([{:sym, "<<"} | rest]) do
    with {:ok, items, rest} <- list(rest, ">>"), do: {:ok, {:seq, items}, rest}
  end

  defp value([{:sym, "{"} | rest]) do
    with {:ok, items, rest} <- list(rest, "}"), do: {:ok, {:set, Enum.sort(items)}, rest}
  end

  defp value([{:sym, "["} | rest]) do
    with {:ok, fields, rest} <- fields(rest, []), do: {:ok, {:rec, Enum.sort(fields)}, rest}
  end

  defp value([{:sym, "("} | rest]) do
    with {:ok, pairs, rest} <- pairs(rest, []), do: {:ok, {:fun, Enum.sort(pairs)}, rest}
  end

  defp value(tokens), do: {:error, "unexpected #{inspect(Enum.take(tokens, 3))}"}

  defp list([{:sym, close} | rest], close), do: {:ok, [], rest}

  defp list(tokens, close) do
    with {:ok, item, rest} <- value(tokens) do
      case rest do
        [{:sym, ","} | rest] ->
          with {:ok, items, rest} <- list(rest, close), do: {:ok, [item | items], rest}

        [{:sym, ^close} | rest] ->
          {:ok, [item], rest}

        other ->
          {:error, "expected , or #{close} but got #{inspect(Enum.take(other, 3))}"}
      end
    end
  end

  defp fields([{:id, name}, {:sym, "|->"} | rest], acc) do
    with {:ok, v, rest} <- value(rest) do
      case rest do
        [{:sym, ","} | rest] -> fields(rest, [{name, v} | acc])
        [{:sym, "]"} | rest] -> {:ok, Enum.reverse([{name, v} | acc]), rest}
        other -> {:error, "bad record near #{inspect(Enum.take(other, 3))}"}
      end
    end
  end

  defp fields(tokens, _acc), do: {:error, "bad record near #{inspect(Enum.take(tokens, 3))}"}

  defp pairs(tokens, acc) do
    with {:ok, k, [{:sym, ":>"} | rest]} <- value(tokens),
         {:ok, v, rest} <- value(rest) do
      case rest do
        [{:sym, "@@"} | rest] -> pairs(rest, [{k, v} | acc])
        [{:sym, ")"} | rest] -> {:ok, Enum.reverse([{k, v} | acc]), rest}
        other -> {:error, "bad function near #{inspect(Enum.take(other, 3))}"}
      end
    else
      {:ok, _k, other} -> {:error, "expected :> near #{inspect(Enum.take(other, 3))}"}
      error -> error
    end
  end

  # -- State blocks --

  @doc """
  Reads the variable lines of one TLC state into a map.

  The lines have the form `/\\ name = value`, or `name = value` for a
  spec with one variable. A long value can continue on the next lines.
  """
  @spec parse_assignments([String.t()]) :: %{String.t() => t()}
  def parse_assignments(lines) do
    lines
    |> Enum.reduce([], fn line, acc ->
      trimmed = String.trim(line)

      cond do
        trimmed == "" ->
          acc

        match = Regex.run(~r/^\/\\\s+(\w+)\s*=\s*(.*)$/s, trimmed) ->
          [_, name, value] = match
          [{name, value} | acc]

        acc == [] ->
          case Regex.run(~r/^(\w+)\s*=\s*(.*)$/s, trimmed) do
            [_, name, value] -> [{name, value}]
            nil -> acc
          end

        true ->
          [{name, value} | rest] = acc
          [{name, value <> " " <> trimmed} | rest]
      end
    end)
    |> Map.new(fn {name, value} -> {name, parse!(value)} end)
  end
end
