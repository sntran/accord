defmodule Accord.Spec do
  @moduledoc """
  A contract in a TLA+ file, for a runtime monitor.

  A protocol module (`use Accord.Protocol`) writes the contract in
  Elixir, and accord makes the TLA+ specification from it. `Accord.Spec`
  goes the other way: the contract is a TLA+ module that you write (or
  that you have already), and accord monitors a real process against it.

      defmodule Lock.Contract do
        use Accord.Spec, file: "lock.tla"
      end

      {:ok, monitor} = Accord.Spec.Monitor.start_link(Lock.Contract, upstream: server)
      :ok = Accord.Spec.Monitor.call(monitor, {:acquire, :c1})

  The same TLA+ module is the input of the model checker
  (`Accord.TLA.Checker`, or `mix accord.check --extra lock.tla`), so the
  monitor and the model check use one specification.

  ## From messages to actions

  Each message through the monitor names an action of the
  specification. The callbacks of this behaviour make the map:

  - `c:handle_call/2` — a call and its reply.
  - `c:handle_cast/1` — a cast.
  - `c:handle_info/1` — a message that the server pushes to the client
    (see `Accord.Spec.Monitor.event/2`).

  Each callback gives `{:action, name, args}` (the TLA+ action and its
  arguments, as Elixir terms) or `:ignore` (the message is not part of
  the contract; the monitor forwards it and does not change its state).

  The default callbacks match by name. The tag of the message, in
  CamelCase, is the action; the other elements are the arguments. For a
  call, the reply is the last argument:

  | Message                    | Reply   | Action                |
  |----------------------------|---------|-----------------------|
  | `{:acquire, :c1}` (call)   | `:ok`   | `Acquire(c1, "ok")`   |
  | `:status` (call)           | `3`     | `Status(3)`           |
  | `{:release, :c1}` (cast)   |         | `Release(c1)`         |
  | `{:granted, :c2}` (event)  |         | `Granted(c2)`         |

  Override a callback for a message that does not match by name. The
  defaults stay for the other messages if you call `super/2`:

      @impl true
      def handle_call({:get, key}, {:ok, value}), do: {:action, "Get", [key, value]}
      def handle_call(:ping, _reply), do: :ignore
      def handle_call(request, reply), do: super(request, reply)

  ## Values

  `Accord.Spec.Value.to_tla/2` changes Elixir terms into TLA+ values: an
  atom is a model value of the config when the config has one with its
  name, else a string; a tuple is a TLA+ tuple, a list a sequence, a map
  a function (a record when its keys are atoms), and a `MapSet` a set.

  ## Blame

  The monitor keeps the set of the states of the specification that the
  run can be in. A message that the specification does not allow is a
  violation:

  - A call: when the action has no step for any reply, the request was
    not allowed in the current states: the client is to blame. When the
    action has steps, but none for this reply, the server is to blame.
  - A cast: the client is to blame.
  - An event: the server is to blame.
  - An `INVARIANT` of the config that is false in a next state: the
    specification itself is to blame (`:property`).

  To find the replies that an action allows, the monitor leaves the last
  parameter open (see `Accord.TLA.Checker.Machine`). When the action reads
  the reply before it gives the reply a value, the monitor cannot find the
  allowed replies, and it blames the server.

  ## Options of `use Accord.Spec`

  - `:file` (required) — the `.tla` file, relative to the file of the
    module that uses `Accord.Spec`.
  - `:config` — the `.cfg` file (default: the `.tla` path with the
    extension `.cfg`, else a `CONFIG` section in the `.tla` file).
  - `:paths` — more directories for the modules that the module uses.

  Accord parses the module at compile time, so a syntax error in the
  TLA+ file is a compile error.
  """

  @type action :: {:action, String.t(), [term()]} | :ignore

  @doc "Maps a call and its reply to an action."
  @callback handle_call(request :: term(), reply :: term()) :: action()

  @doc "Maps a cast to an action."
  @callback handle_cast(request :: term()) :: action()

  @doc "Maps a message that the server pushes to an action."
  @callback handle_info(message :: term()) :: action()

  defmacro __using__(opts) do
    file = Keyword.fetch!(opts, :file)
    dir = Path.dirname(__CALLER__.file)
    path = Path.expand(file, dir)
    config = if c = Keyword.get(opts, :config), do: Path.expand(c, dir)
    paths = opts |> Keyword.get(:paths, []) |> Enum.map(&Path.expand(&1, dir))

    case Accord.TLA.Checker.Machine.load(path, config: config, paths: paths) do
      {:ok, _} ->
        :ok

      {:error, message} ->
        raise CompileError,
          file: __CALLER__.file,
          line: __CALLER__.line,
          description: "cannot load the TLA+ contract #{file}: #{message}"
    end

    resources =
      [path | if(config, do: [config], else: [])] ++
        if(File.exists?(Path.rootname(path) <> ".cfg"),
          do: [Path.rootname(path) <> ".cfg"],
          else: []
        )

    quote do
      @behaviour Accord.Spec

      for resource <- unquote(Enum.uniq(resources)), do: @external_resource(resource)

      @doc false
      def __accord_spec__ do
        %{file: unquote(path), config: unquote(config), paths: unquote(paths)}
      end

      @impl Accord.Spec
      def handle_call(request, reply), do: Accord.Spec.match_call(request, reply)

      @impl Accord.Spec
      def handle_cast(request), do: Accord.Spec.match(request)

      @impl Accord.Spec
      def handle_info(message), do: Accord.Spec.match(message)

      defoverridable handle_call: 2, handle_cast: 1, handle_info: 1
    end
  end

  @doc """
  The default map of a cast or an event: the tag in CamelCase is the
  action, and the other elements are its arguments.
  """
  @spec match(term()) :: action()
  def match(message) do
    case message do
      tag when is_atom(tag) and tag not in [nil, true, false] ->
        {:action, action_name(tag), []}

      tuple when is_tuple(tuple) and tuple_size(tuple) > 0 and is_atom(elem(tuple, 0)) ->
        [tag | args] = Tuple.to_list(tuple)
        {:action, action_name(tag), args}

      _ ->
        :ignore
    end
  end

  @doc """
  The default map of a call: as `match/1`, with the reply as the last
  argument.
  """
  @spec match_call(term(), term()) :: action()
  def match_call(request, reply) do
    case match(request) do
      {:action, name, args} -> {:action, name, args ++ [reply]}
      :ignore -> :ignore
    end
  end

  @doc ~S"""
  The action name of a message tag: `:acquire` gives `"Acquire"`, and
  `:get_value` gives `"GetValue"`.
  """
  @spec action_name(atom()) :: String.t()
  def action_name(tag), do: tag |> Atom.to_string() |> Macro.camelize()
end
