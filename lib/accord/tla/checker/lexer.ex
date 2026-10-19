defmodule Accord.TLA.Checker.Lexer do
  @moduledoc """
  Splits TLA+ source text into tokens.

  A token is `{type, value, line, column}`. Lines and columns start at 1.
  The column counts characters, not bytes, so the alignment of junction
  lists is correct for Unicode text too.

  Token types:

  - `:id` — an identifier (`x`, `Next`, `TRUE`).
  - `:num` — an integer (decimal, `\\b`, `\\o`, or `\\h`).
  - `:dec` — a decimal number such as `1.5`, as a string.
  - `:str` — a string, with its escapes decoded.
  - `:kw` — a keyword (`IF`, `LET`, `WF_`, ...).
  - `:op` — an operator or a punctuation symbol. Synonyms have one name:
    `\\land` and `∧` are `"/\\\\"`, `\\union` is `"\\\\cup"`, `#` is `"/="`.
  - `:module_start` — the line `---- MODULE Name ----`; the value is the
    name.
  - `:module_end` — a line of four or more `=`.
  - `:separator` — a line of four or more `-`.

  The lexer skips comments (`\\*` to the end of the line, and nested
  `(* ... *)`), and all text before the first module and after the end of
  the last module.
  """

  @keywords ~w(ASSUME ASSUMPTION AXIOM BY CASE CHOOSE CONSTANT CONSTANTS COROLLARY
    DEF DEFINE DEFS DOMAIN ELSE ENABLED EXCEPT EXTENDS HAVE HIDE IF IN INSTANCE
    LAMBDA LEMMA LET LOCAL MODULE NEW OBVIOUS OMITTED OTHER PICK PROOF PROPOSITION
    PROVE QED RECURSIVE SF_ SUBSET SUFFICES TAKE THEN THEOREM UNCHANGED UNION USE
    VARIABLE VARIABLES WF_ WITH WITNESS ACTION STATE TEMPORAL ONLY)

  # Backslash operators, by name after the backslash. The value is the
  # canonical operator name.
  @backslash_ops %{
    "in" => "\\in",
    "notin" => "\\notin",
    "cup" => "\\cup",
    "union" => "\\cup",
    "cap" => "\\cap",
    "intersect" => "\\cap",
    "subseteq" => "\\subseteq",
    "subset" => "\\subset",
    "supseteq" => "\\supseteq",
    "supset" => "\\supset",
    "X" => "\\X",
    "times" => "\\X",
    "div" => "\\div",
    "o" => "\\o",
    "circ" => "\\o",
    "land" => "/\\",
    "lor" => "\\/",
    "lnot" => "~",
    "neg" => "~",
    "equiv" => "<=>",
    "leq" => "<=",
    "geq" => ">=",
    "ll" => "\\ll",
    "gg" => "\\gg",
    "prec" => "\\prec",
    "succ" => "\\succ",
    "preceq" => "\\preceq",
    "succeq" => "\\succeq",
    "sqsubset" => "\\sqsubset",
    "sqsupset" => "\\sqsupset",
    "sqsubseteq" => "\\sqsubseteq",
    "sqsupseteq" => "\\sqsupseteq",
    "sqcap" => "\\sqcap",
    "sqcup" => "\\sqcup",
    "uplus" => "\\uplus",
    "oplus" => "(+)",
    "ominus" => "(-)",
    "odot" => "(.)",
    "oslash" => "(/)",
    "otimes" => "(\\X)",
    "bigcirc" => "\\bigcirc",
    "bullet" => "\\bullet",
    "star" => "\\star",
    "cdot" => "\\cdot",
    "sim" => "\\sim",
    "simeq" => "\\simeq",
    "asymp" => "\\asymp",
    "approx" => "\\approx",
    "cong" => "\\cong",
    "doteq" => "\\doteq",
    "propto" => "\\propto",
    "wr" => "\\wr",
    "A" => "\\A",
    "E" => "\\E",
    "forall" => "\\A",
    "exists" => "\\E",
    "AA" => "\\AA",
    "EE" => "\\EE"
  }

  # Symbol operators, longest first. The value is the canonical name.
  @symbols [
    {"-+->", "-+->"},
    {"(\\X)", "(\\X)"},
    {"|->", "|->"},
    {"<=>", "<=>"},
    {"::=", "::="},
    {"...", "..."},
    {"(+)", "(+)"},
    {"(-)", "(-)"},
    {"(.)", "(.)"},
    {"(/)", "(/)"},
    {"==", "=="},
    {"=>", "=>"},
    {"=<", "<="},
    {"<=", "<="},
    {">=", ">="},
    {"/=", "/="},
    {"/\\", "/\\"},
    {"\\/", "\\/"},
    {"=|", "=|"},
    {"..", ".."},
    {":=", ":="},
    {"::", "::"},
    {":>", ":>"},
    {"->", "->"},
    {"<-", "<-"},
    {"<:", "<:"},
    {"<<", "<<"},
    {">>", ">>"},
    {"[]", "[]"},
    {"<>", "<>"},
    {"~>", "~>"},
    {"--", "--"},
    {"-|", "-|"},
    {"++", "++"},
    {"**", "**"},
    {"//", "//"},
    {"^^", "^^"},
    {"%%", "%%"},
    {"&&", "&&"},
    {"||", "||"},
    {"??", "??"},
    {"!!", "!!"},
    {"@@", "@@"},
    {"$$", "$$"},
    {"|-", "|-"},
    {"|=", "|="},
    {"^+", "^+"},
    {"^*", "^*"},
    {"^#", "^#"},
    {"##", "##"},
    {"#", "/="},
    {"'", "'"},
    {"!", "!"},
    {"@", "@"},
    {"^", "^"},
    {"~", "~"},
    {"=", "="},
    {"<", "<"},
    {">", ">"},
    {"+", "+"},
    {"-", "-"},
    {"*", "*"},
    {"/", "/"},
    {"%", "%"},
    {"&", "&"},
    {"|", "|"},
    {"$", "$"},
    {"?", "?"},
    {":", ":"},
    {",", ","},
    {".", "."},
    {"(", "("},
    {")", ")"},
    {"[", "["},
    {"]", "]"},
    {"{", "{"},
    {"}", "}"},
    {"_", "_"},
    {"\\", "\\"}
  ]

  # Unicode forms of the operators.
  @unicode %{
    "∧" => "/\\",
    "∨" => "\\/",
    "¬" => "~",
    "⇒" => "=>",
    "⟹" => "=>",
    "⇔" => "<=>",
    "≡" => "<=>",
    "≜" => "==",
    "∈" => "\\in",
    "∉" => "\\notin",
    "≠" => "/=",
    "≤" => "<=",
    "≥" => ">=",
    "⊆" => "\\subseteq",
    "⊂" => "\\subset",
    "⊇" => "\\supseteq",
    "⊃" => "\\supset",
    "∪" => "\\cup",
    "∩" => "\\cap",
    "×" => "\\X",
    "∘" => "\\o",
    "□" => "[]",
    "◇" => "<>",
    "⋄" => "<>",
    "↝" => "~>",
    "⟨" => "<<",
    "⟩" => ">>",
    "↦" => "|->",
    "→" => "->",
    "←" => "<-",
    "∀" => "\\A",
    "∃" => "\\E",
    "≺" => "\\prec",
    "≻" => "\\succ",
    "⪯" => "\\preceq",
    "⪰" => "\\succeq",
    "⊑" => "\\sqsubseteq",
    "⊒" => "\\sqsupseteq",
    "⊓" => "\\sqcap",
    "⊔" => "\\sqcup",
    "⊎" => "\\uplus",
    "⊕" => "(+)",
    "⊖" => "(-)",
    "⊙" => "(.)",
    "⊘" => "(/)",
    "⊗" => "(\\X)",
    "∼" => "\\sim",
    "≃" => "\\simeq",
    "≈" => "\\approx",
    "≅" => "\\cong",
    "≐" => "\\doteq",
    "∝" => "\\propto",
    "⋆" => "\\star",
    "⋅" => "\\cdot",
    "…" => "...",
    "∷" => "::",
    "≔" => ":=",
    "⊢" => "|-",
    "⊨" => "|=",
    "⊣" => "-|",
    "⫤" => "=|",
    "⇸" => "-+->",
    "⟦" => "[",
    "⟧" => "]"
  }

  defmodule Error do
    @moduledoc "A lexical error, with its position."
    defexception [:message, :line, :column]
  end

  @type token :: {atom(), term(), pos_integer(), pos_integer()}

  @doc """
  Splits `source` into tokens. Raises `Accord.TLA.Checker.Lexer.Error`.
  """
  @spec tokenize(String.t()) :: [token()]
  def tokenize(source) do
    case find_module_start(source) do
      nil -> raise Error, message: "no `---- MODULE Name ----` line", line: 1, column: 1
      {skip, line} -> lex(binary_part(source, skip, byte_size(source) - skip), line, 1, 0, [])
    end
  end

  # The byte offset and line of the first module header.
  defp find_module_start(source) do
    case Regex.run(~r/^[ \t]*-{4,}[ \t]*MODULE[ \t]/m, source, return: :index) do
      [{start, _}] ->
        line = source |> binary_part(0, start) |> String.split("\n") |> length()
        {start, line}

      nil ->
        nil
    end
  end

  # After the end of a top-level module, the file can have more modules
  # (the modules that the first one uses). The text between them is
  # ignored.
  defp next_module(rest, line, acc) do
    case Regex.run(~r/^-{4,}[ \t]*MODULE[ \t]/m, rest, return: :index) do
      [{start, _}] ->
        skipped = binary_part(rest, 0, start)
        lines = skipped |> :binary.matches("\n") |> length()
        lex(binary_part(rest, start, byte_size(rest) - start), line + lines, 1, 0, acc)

      nil ->
        Enum.reverse(acc)
    end
  end

  # depth > 0: inside a block comment. After the last module ends (depth
  # :done), the rest is ignored. A module_end with no open module ends.
  defp lex(<<>>, _line, _col, _open, acc), do: Enum.reverse(acc)

  defp lex(<<"\n", rest::binary>>, line, _col, open, acc), do: lex(rest, line + 1, 1, open, acc)
  defp lex(<<"\r", rest::binary>>, line, col, open, acc), do: lex(rest, line, col, open, acc)

  # A tab goes to the next column of 8 (as the JavaCC lexer of SANY).
  defp lex(<<?\t, rest::binary>>, line, col, open, acc),
    do: lex(rest, line, div(col - 1, 8) * 8 + 9, open, acc)

  defp lex(<<c, rest::binary>>, line, col, open, acc) when c in [?\s, ?\f],
    do: lex(rest, line, col + 1, open, acc)

  defp lex(<<"\\*", rest::binary>>, line, _col, open, acc) do
    case :binary.split(rest, "\n") do
      [_, after_nl] -> lex(after_nl, line + 1, 1, open, acc)
      [_] -> Enum.reverse(acc)
    end
  end

  defp lex(<<"(*", rest::binary>>, line, col, open, acc) do
    {rest, line, col} = skip_comment(rest, line, col + 2, 1)
    lex(rest, line, col, open, acc)
  end

  defp lex(<<"-", _::binary>> = bin, line, col, open, acc) do
    case module_line(bin) do
      {:start, name, len} ->
        lex(drop(bin, len), line, col + len, open + 1, [{:module_start, name, line, col} | acc])

      :none ->
        case dashes(bin) do
          n when n >= 4 ->
            lex(drop(bin, n), line, col + n, open, [{:separator, nil, line, col} | acc])

          _ ->
            symbol(bin, line, col, open, acc)
        end
    end
  end

  defp lex(<<"=", _::binary>> = bin, line, col, open, acc) do
    case count_char(bin, ?=) do
      n when n >= 4 ->
        acc = [{:module_end, nil, line, col} | acc]

        if open <= 1,
          do: next_module(drop(bin, n), line, acc),
          else: lex(drop(bin, n), line, col + n, open - 1, acc)

      _ ->
        symbol(bin, line, col, open, acc)
    end
  end

  defp lex(<<?", rest::binary>>, line, col, open, acc) do
    {str, rest, len} = string(rest, [], 1)
    lex(rest, line, col + len, open, [{:str, str, line, col} | acc])
  end

  defp lex(<<"\\", rest::binary>> = bin, line, col, open, acc) do
    case number_prefix(rest) do
      {value, len} ->
        lex(drop(bin, len + 1), line, col + len + 1, open, [{:num, value, line, col} | acc])

      nil ->
        # The name of a backslash operator has only letters, so that
        # `_\prec_` gives `_`, `\prec`, `_`.
        case letters(rest) do
          {"", _} ->
            symbol(bin, line, col, open, acc)

          {name, after_word} ->
            case Map.fetch(@backslash_ops, name) do
              {:ok, op} ->
                len = String.length(name) + 1
                lex(after_word, line, col + len, open, [{:op, op, line, col} | acc])

              :error ->
                symbol(bin, line, col, open, acc)
            end
        end
    end
  end

  defp lex(<<c, _::binary>> = bin, line, col, open, acc)
       when c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_ do
    {w, rest} = word(bin)
    len = String.length(w)

    cond do
      w == "_" ->
        symbol(bin, line, col, open, acc)

      String.match?(w, ~r/^\d+$/) ->
        case rest do
          <<".", d, _::binary>> when d in ?0..?9 ->
            {frac, rest2} = word(binary_part(rest, 1, byte_size(rest) - 1))
            text = w <> "." <> frac
            lex(rest2, line, col + String.length(text), open, [{:dec, text, line, col} | acc])

          _ ->
            lex(rest, line, col + len, open, [{:num, String.to_integer(w), line, col} | acc])
        end

      String.starts_with?(w, "WF_") or String.starts_with?(w, "SF_") ->
        kw = binary_part(w, 0, 3)
        tail = binary_part(w, 3, byte_size(w) - 3)
        acc = [{:kw, kw, line, col} | acc]
        acc = if tail == "", do: acc, else: [{:id, tail, line, col + 3} | acc]
        lex(rest, line, col + len, open, acc)

      w in @keywords ->
        lex(rest, line, col + len, open, [{:kw, w, line, col} | acc])

      true ->
        lex(rest, line, col + len, open, [{:id, w, line, col} | acc])
    end
  end

  defp lex(<<c, _::binary>> = bin, line, col, open, acc) when c < 128,
    do: symbol(bin, line, col, open, acc)

  defp lex(bin, line, col, open, acc) do
    case unicode(bin) do
      {op, len_bytes} ->
        lex(drop(bin, len_bytes), line, col + 1, open, [{:op, op, line, col} | acc])

      nil ->
        symbol(bin, line, col, open, acc)
    end
  end

  defp symbol(bin, line, col, open, acc) do
    case Enum.find(@symbols, fn {text, _} -> String.starts_with?(bin, text) end) do
      {"]", _} ->
        # `]_` and `>>_` start a subscript: `[A]_v`, `<<A>>_v`.
        case bin do
          <<"]_", _::binary>> ->
            lex(drop(bin, 2), line, col + 2, open, [{:op, "]_", line, col} | acc])

          _ ->
            lex(drop(bin, 1), line, col + 1, open, [{:op, "]", line, col} | acc])
        end

      {">>", _} ->
        case bin do
          <<">>_", _::binary>> ->
            lex(drop(bin, 3), line, col + 3, open, [{:op, ">>_", line, col} | acc])

          _ ->
            lex(drop(bin, 2), line, col + 2, open, [{:op, ">>", line, col} | acc])
        end

      {text, op} ->
        len = byte_size(text)
        lex(drop(bin, len), line, col + len, open, [{:op, op, line, col} | acc])

      nil ->
        <<c::utf8, _::binary>> = bin

        raise Error,
          message: "unexpected character #{inspect(<<c::utf8>>)}",
          line: line,
          column: col
    end
  end

  defp unicode(bin) do
    Enum.find_value(@unicode, fn {char, op} ->
      if String.starts_with?(bin, char), do: {op, byte_size(char)}
    end)
  end

  defp drop(bin, n), do: binary_part(bin, n, byte_size(bin) - n)

  defp letters(bin), do: letters(bin, 0, bin)

  defp letters(<<c, rest::binary>>, n, bin) when c in ?a..?z or c in ?A..?Z,
    do: letters(rest, n + 1, bin)

  defp letters(rest, n, bin), do: {binary_part(bin, 0, n), rest}

  defp word(bin) do
    len = word_len(bin, 0)
    {binary_part(bin, 0, len), binary_part(bin, len, byte_size(bin) - len)}
  end

  defp word_len(<<c, rest::binary>>, n)
       when c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_,
       do: word_len(rest, n + 1)

  defp word_len(_, n), do: n

  defp dashes(bin), do: count_char(bin, ?-)

  defp count_char(<<c, rest::binary>>, c), do: 1 + count_char(rest, c)
  defp count_char(_, _), do: 0

  # `---- MODULE Name ----`: gives the name and the length of the header.
  defp module_line(bin) do
    case Regex.run(~r/^-{4,}[ \t]*MODULE[ \t]+(\w+)[ \t]*-{4,}/, bin) do
      [whole, name] -> {:start, name, byte_size(whole)}
      nil -> :none
    end
  end

  # `\b101`, `\o17`, `\h1F`.
  defp number_prefix(<<p, rest::binary>>) when p in [?b, ?B, ?o, ?O, ?h, ?H] do
    {base, re} =
      case p do
        x when x in [?b, ?B] -> {2, ~r/^[01]+/}
        x when x in [?o, ?O] -> {8, ~r/^[0-7]+/}
        _ -> {16, ~r/^[0-9a-fA-F]+/}
      end

    case Regex.run(re, rest) do
      [digits] ->
        {after_digits, _} = word(rest)

        if after_digits == digits,
          do: {String.to_integer(digits, base), 1 + byte_size(digits)},
          else: nil

      nil ->
        nil
    end
  end

  defp number_prefix(_), do: nil

  defp string(<<?", rest::binary>>, acc, len),
    do: {acc |> Enum.reverse() |> IO.iodata_to_binary(), rest, len + 1}

  defp string(<<"\\", c, rest::binary>>, acc, len) do
    ch =
      case c do
        ?n -> "\n"
        ?t -> "\t"
        ?r -> "\r"
        ?f -> "\f"
        ?" -> "\""
        ?\\ -> "\\"
        other -> <<?\\, other>>
      end

    string(rest, [ch | acc], len + 2)
  end

  defp string(<<"\n", _::binary>>, _acc, _len),
    do: raise(Error, message: "a string must end on its line", line: nil, column: nil)

  defp string(<<c::utf8, rest::binary>>, acc, len), do: string(rest, [<<c::utf8>> | acc], len + 1)

  defp string(<<>>, _acc, _len),
    do: raise(Error, message: "unterminated string", line: nil, column: nil)

  defp skip_comment(<<"*)", rest::binary>>, line, col, 1), do: {rest, line, col + 2}

  defp skip_comment(<<"*)", rest::binary>>, line, col, d),
    do: skip_comment(rest, line, col + 2, d - 1)

  defp skip_comment(<<"(*", rest::binary>>, line, col, d),
    do: skip_comment(rest, line, col + 2, d + 1)

  defp skip_comment(<<"\n", rest::binary>>, line, _col, d), do: skip_comment(rest, line + 1, 1, d)

  defp skip_comment(<<_::utf8, rest::binary>>, line, col, d),
    do: skip_comment(rest, line, col + 1, d)

  defp skip_comment(<<_, rest::binary>>, line, col, d), do: skip_comment(rest, line, col + 1, d)

  defp skip_comment(<<>>, line, col, _d),
    do: raise(Error, message: "unterminated comment", line: line, column: col)
end
