defmodule Accord.TLA.Checker.Config do
  @moduledoc """
  Parses a TLC model config file (`.cfg`).

  The statements are the ones TLC reads:

      SPECIFICATION Spec            INIT Init        NEXT Next
      INVARIANT TypeOK Safe         PROPERTY Live
      CONSTANTS N = 3  Procs = {p1, p2}  Null = Null  Op <- Impl
      CONSTRAINT Bound              ACTION_CONSTRAINT Step
      SYMMETRY Perms                VIEW View        ALIAS Alias
      CHECK_DEADLOCK FALSE          POSTCONDITION Done

  Plural forms (`INVARIANTS`, `PROPERTIES`, `CONSTRAINTS`, ...) are the
  same as the singular forms. A constant value is a number, a string,
  `TRUE`, `FALSE`, a model value (a name), or a set of these values.
  `N = N` declares the model value `N`.
  """

  defstruct specification: nil,
            init: nil,
            next: nil,
            invariants: [],
            properties: [],
            constants: [],
            constraints: [],
            action_constraints: [],
            symmetry: nil,
            view: nil,
            alias: nil,
            postconditions: [],
            check_deadlock: true

  @type constant ::
          {:value, String.t(), term()}
          | {:replace, String.t(), String.t()}
          | {:module_replace, String.t(), String.t(), String.t()}
          | {:module_value, String.t(), String.t(), term()}

  @keywords %{
    "SPECIFICATION" => :specification,
    "INIT" => :init,
    "NEXT" => :next,
    "INVARIANT" => :invariants,
    "INVARIANTS" => :invariants,
    "PROPERTY" => :properties,
    "PROPERTIES" => :properties,
    "CONSTANT" => :constants,
    "CONSTANTS" => :constants,
    "CONSTRAINT" => :constraints,
    "CONSTRAINTS" => :constraints,
    "ACTION_CONSTRAINT" => :action_constraints,
    "ACTION_CONSTRAINTS" => :action_constraints,
    "SYMMETRY" => :symmetry,
    "VIEW" => :view,
    "ALIAS" => :alias,
    "POSTCONDITION" => :postconditions,
    "POSTCONDITIONS" => :postconditions,
    "CHECK_DEADLOCK" => :check_deadlock
  }

  defmodule Error do
    @moduledoc "A config file error."
    defexception [:message]
  end

  @doc "Parses the text of a config file."
  @spec parse(String.t()) :: %__MODULE__{}
  def parse(text) do
    text
    |> strip_comments()
    |> tokens()
    |> statements(%__MODULE__{}, nil)
  end

  defp strip_comments(text) do
    text
    |> remove_block_comments()
    |> String.split("\n")
    |> Enum.map(fn line ->
      case :binary.split(line, "\\*") do
        [before, _] -> before
        [line] -> line
      end
    end)
    |> Enum.join("\n")
  end

  defp remove_block_comments(text) do
    case :binary.split(text, "(*") do
      [before, rest] ->
        case :binary.split(rest, "*)") do
          [_, after_comment] -> remove_block_comments(before <> " " <> after_comment)
          [_] -> before
        end

      [text] ->
        text
    end
  end

  defp tokens(text) do
    ~r/"(?:[^"\\]|\\.)*"|<-|-?\d+|[A-Za-z0-9_]+|[{}\[\],=]/
    |> Regex.scan(text)
    |> List.flatten()
  end

  defp statements([], cfg, _section), do: finish(cfg)

  defp statements([word | rest], cfg, section) do
    case Map.fetch(@keywords, word) do
      {:ok, :check_deadlock} ->
        [value | rest] = rest
        statements(rest, %{cfg | check_deadlock: value == "TRUE"}, nil)

      {:ok, key} when key in [:specification, :init, :next, :symmetry, :view, :alias] ->
        [name | rest] = rest
        statements(rest, Map.put(cfg, key, name), nil)

      {:ok, key} ->
        statements(rest, cfg, key)

      :error ->
        item(section, word, rest, cfg)
    end
  end

  defp item(:constants, name, rest, cfg) do
    case rest do
      ["=", "[", mod, "]" | rest] ->
        {value, rest} = value(rest, name)

        statements(
          rest,
          %{cfg | constants: [{:module_value, mod, name, value} | cfg.constants]},
          :constants
        )

      ["=" | rest] ->
        {value, rest} = value(rest, name)
        statements(rest, %{cfg | constants: [{:value, name, value} | cfg.constants]}, :constants)

      ["<-", "[", mod, "]", target | rest] ->
        c = {:module_replace, mod, name, target}
        statements(rest, %{cfg | constants: [c | cfg.constants]}, :constants)

      ["<-", target | rest] ->
        statements(
          rest,
          %{cfg | constants: [{:replace, name, target} | cfg.constants]},
          :constants
        )

      _ ->
        raise Error, message: "bad constant definition for #{name}"
    end
  end

  defp item(key, name, rest, cfg)
       when key in [:invariants, :properties, :constraints, :action_constraints, :postconditions] do
    statements(rest, Map.update!(cfg, key, &[name | &1]), key)
  end

  defp item(nil, word, _rest, _cfg), do: raise(Error, message: "unexpected #{inspect(word)}")

  defp value(["{" | rest], _name) do
    {elems, rest} = set_values(rest, [])
    {{:set, elems}, rest}
  end

  defp value([token | rest], name), do: {scalar(token, name), rest}

  defp set_values(["}" | rest], acc), do: {Enum.reverse(acc), rest}
  defp set_values(["," | rest], acc), do: set_values(rest, acc)

  defp set_values(["{" | _] = tokens, acc) do
    {v, rest} = value(tokens, nil)
    set_values(rest, [v | acc])
  end

  defp set_values([token | rest], acc), do: set_values(rest, [scalar(token, nil) | acc])

  defp scalar("TRUE", _), do: true
  defp scalar("FALSE", _), do: false

  defp scalar(<<?", _::binary>> = s, _),
    do: s |> String.slice(1..-2//1) |> String.replace(~S(\"), ~S("))

  defp scalar(token, _name) do
    case Integer.parse(token) do
      {n, ""} -> n
      _ -> {:mv, token}
    end
  end

  defp finish(cfg) do
    %{
      cfg
      | invariants: Enum.reverse(cfg.invariants),
        properties: Enum.reverse(cfg.properties),
        constants: Enum.reverse(cfg.constants),
        constraints: Enum.reverse(cfg.constraints),
        action_constraints: Enum.reverse(cfg.action_constraints),
        postconditions: Enum.reverse(cfg.postconditions)
    }
  end
end
