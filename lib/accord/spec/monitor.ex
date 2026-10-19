defmodule Accord.Spec.Monitor do
  @moduledoc """
  A runtime monitor for a TLA+ contract (see `Accord.Spec`).

      Client ──call──▶ [Monitor] ──call──▶ Server
                           │
                  TLA+ states of the run;
                  on violation: log / reject / crash

  The monitor is a proxy process. It forwards each call and cast to the
  server (`:upstream`), and each event of the server to the client
  (`:downstream`). For each message, it finds the action with the
  callbacks of the contract module, and computes the next states of the
  specification with `Accord.TLA.Checker.Machine`.

  A call is checked when the reply comes back: the reply is an argument
  of the action. A cast is checked before the monitor forwards it, and an
  event before the monitor sends it to the client.
  """

  use GenServer

  require Logger

  alias Accord.Spec.Value, as: SpecValue
  alias Accord.TLA.Checker.Machine
  alias Accord.Violation

  @type violation_policy :: :log | :reject | :crash | {module(), atom()}

  defstruct [
    :contract,
    :machine,
    :model_values,
    :upstream,
    :downstream,
    :policy,
    :call_timeout,
    states: []
  ]

  # -- Public API --

  @doc """
  Starts a monitor for the contract module `contract`.

  ## Options

  - `:upstream` (required) — the pid of the server.
  - `:downstream` — the pid that gets the events of the server (see
    `event/2`). With `nil`, the monitor checks the events and drops them.
  - `:violation_policy` — `:log` | `:reject` | `:crash` | `{mod, fun}`.
    Default `:crash`.
  - `:call_timeout` — the timeout of a call to the server, in ms.
    Default 5000.
  - `:name` — a name for the monitor process.
  """
  @spec start_link(module(), keyword()) :: GenServer.on_start()
  def start_link(contract, opts) do
    {name, opts} = Keyword.pop(opts, :name)
    gen_opts = if name, do: [name: name], else: []
    GenServer.start_link(__MODULE__, {contract, opts}, gen_opts)
  end

  @doc """
  Sends a call to the server through the monitor. Gives the reply of the
  server, or `{:accord_violation, violation}` when the policy rejects the
  call.
  """
  @spec call(GenServer.server(), term(), timeout()) :: term()
  def call(monitor, request, timeout \\ 5_000),
    do: GenServer.call(monitor, {:accord_call, request}, timeout)

  @doc "Sends a cast to the server through the monitor."
  @spec cast(GenServer.server(), term()) :: :ok
  def cast(monitor, request), do: GenServer.cast(monitor, {:accord_cast, request})

  @doc """
  Sends an event of the server to the client through the monitor. The
  server calls this function in place of `send/2`.
  """
  @spec event(GenServer.server(), term()) :: :ok
  def event(monitor, message), do: GenServer.cast(monitor, {:accord_event, message})

  @doc """
  The states of the specification that the run can be in, as maps from
  variable names to Elixir terms (see `Accord.Spec.Value.from_tla/1`).
  """
  @spec states(GenServer.server()) :: [map()]
  def states(monitor), do: GenServer.call(monitor, :accord_states)

  # -- Callbacks --

  @impl true
  def init({contract, opts}) do
    spec = contract.__accord_spec__()

    case Machine.load(spec.file, config: spec.config, paths: spec.paths) do
      {:ok, machine} ->
        case Machine.init_states(machine) do
          {:ok, []} ->
            {:stop, {:accord_spec, "the initial predicate allows no state"}}

          {:ok, states} ->
            {:ok,
             %__MODULE__{
               contract: contract,
               machine: machine,
               model_values: Machine.model_values(machine),
               upstream: Keyword.fetch!(opts, :upstream),
               downstream: Keyword.get(opts, :downstream),
               policy: Keyword.get(opts, :violation_policy, :crash),
               call_timeout: Keyword.get(opts, :call_timeout, 5_000),
               states: states
             }}

          {:error, message} ->
            {:stop, {:accord_spec, message}}
        end

      {:error, message} ->
        {:stop, {:accord_spec, message}}
    end
  end

  @impl true
  def handle_call(:accord_states, _from, data) do
    {:reply, Enum.map(data.states, &state_map(data, &1)), data}
  end

  def handle_call({:accord_call, request}, _from, data) do
    case upstream_call(data, request) do
      {:ok, reply} ->
        check_call(data, request, reply)

      :timeout ->
        v =
          violation(
            data,
            :server,
            :timeout,
            nil,
            [],
            {:call, request, nil},
            "the server did not reply in time"
          )

        case policy(v, data) do
          :stop -> {:stop, {:protocol_violation, v}, {:accord_violation, v}, data}
          _ -> {:reply, {:accord_violation, v}, data}
        end
    end
  end

  defp upstream_call(data, request) do
    {:ok, GenServer.call(data.upstream, request, data.call_timeout)}
  catch
    :exit, {:timeout, _} -> :timeout
  end

  defp check_call(data, request, reply) do
    case data.contract.handle_call(request, reply) do
      :ignore ->
        {:reply, reply, data}

      {:action, name, args} ->
        case advance(data, name, args, {:call, request, reply}) do
          {:ok, data} ->
            {:reply, reply, data}

          {:violation, v} ->
            case policy(v, data) do
              :stop -> {:stop, {:protocol_violation, v}, {:accord_violation, v}, data}
              :pass -> {:reply, reply, data}
              :reject -> {:reply, {:accord_violation, v}, data}
            end
        end
    end
  end

  @impl true
  def handle_cast({:accord_cast, request}, data) do
    case data.contract.handle_cast(request) do
      :ignore ->
        GenServer.cast(data.upstream, request)
        {:noreply, data}

      {:action, name, args} ->
        checked(data, advance(data, name, args, {:cast, request}), fn ->
          GenServer.cast(data.upstream, request)
        end)
    end
  end

  def handle_cast({:accord_event, message}, data) do
    case data.contract.handle_info(message) do
      :ignore ->
        deliver(data, message)
        {:noreply, data}

      {:action, name, args} ->
        checked(data, advance(data, name, args, {:event, message}), fn ->
          deliver(data, message)
        end)
    end
  end

  defp checked(data, result, forward) do
    case result do
      {:ok, data} ->
        forward.()
        {:noreply, data}

      {:violation, v} ->
        case policy(v, data) do
          :stop ->
            {:stop, {:protocol_violation, v}, data}

          :pass ->
            forward.()
            {:noreply, data}

          :reject ->
            {:noreply, data}
        end
    end
  end

  defp deliver(%{downstream: nil}, _message), do: :ok
  defp deliver(%{downstream: pid}, message), do: send(pid, message)

  # -- Steps --

  # The next states of the action from all the current states.
  defp advance(data, name, args, message) do
    values = Enum.map(args, &SpecValue.to_tla(&1, data.model_values))

    results =
      if Machine.arity(data.machine, name) == nil,
        do: [],
        else: Enum.map(data.states, &Machine.step(data.machine, &1, name, values))

    case Enum.find(results, &match?({:error, _}, &1)) do
      {:error, error} ->
        {:violation, violation(data, :property, :spec_error, name, args, message, error)}

      nil ->
        next =
          results
          |> Enum.flat_map(fn {:ok, steps} -> Enum.map(steps, &elem(&1, 0)) end)
          |> Enum.uniq()

        if next == [] do
          {:violation, no_step(data, name, args, values, message)}
        else
          invariants(data, next, name, args, message)
        end
    end
  end

  defp invariants(data, next, name, args, message) do
    Enum.reduce_while(next, {:ok, %{data | states: next}}, fn state, acc ->
      case Machine.check_invariants(data.machine, state) do
        :ok ->
          {:cont, acc}

        {:violated, inv} ->
          v =
            violation(
              data,
              :property,
              :invariant_violated,
              name,
              args,
              message,
              "the invariant #{inv} is false"
            )

          {:halt,
           {:violation, %{v | context: Map.put(v.context, :next_state, state_map(data, state))}}}

        {:error, error} ->
          {:halt,
           {:violation, violation(data, :property, :spec_error, name, args, message, error)}}
      end
    end)
  end

  # No step: for a call, the server is to blame when the action allows
  # some other reply.
  defp no_step(data, name, args, values, {:call, _, _} = message) do
    opened =
      if values != [] and Machine.arity(data.machine, name) == length(values) do
        Enum.map(
          data.states,
          &Machine.step(data.machine, &1, name, Enum.drop(values, -1), open: true)
        )
      else
        []
      end

    cond do
      Machine.arity(data.machine, name) == nil ->
        violation(
          data,
          :client,
          :invalid_message,
          name,
          args,
          message,
          "the specification has no action #{name}"
        )

      Enum.any?(opened, &match?({:ok, [_ | _]}, &1)) ->
        allowed =
          for {:ok, steps} <- opened, {_, r} <- steps, uniq: true, do: SpecValue.from_tla(r)

        v =
          violation(
            data,
            :server,
            :invalid_reply,
            name,
            args,
            message,
            "the specification does not allow this reply"
          )

        %{v | expected: allowed}

      Enum.any?(opened, &match?({:error, _}, &1)) ->
        violation(
          data,
          :server,
          :invalid_reply,
          name,
          args,
          message,
          "the action #{name} does not allow this reply"
        )

      true ->
        violation(
          data,
          :client,
          :invalid_message,
          name,
          args,
          message,
          "the action #{name} is not enabled"
        )
    end
  end

  defp no_step(data, name, args, _values, {:cast, _} = message) do
    violation(data, :client, :invalid_message, name, args, message, not_enabled(data, name))
  end

  defp no_step(data, name, args, _values, {:event, _} = message) do
    violation(data, :server, :invalid_event, name, args, message, not_enabled(data, name))
  end

  defp not_enabled(data, name) do
    if Machine.arity(data.machine, name) == nil,
      do: "the specification has no action #{name}",
      else: "the action #{name} is not enabled"
  end

  defp violation(data, blame, kind, name, args, message, text) do
    {msg, reply} =
      case message do
        {:call, request, reply} -> {request, reply}
        {_, m} -> {m, nil}
      end

    %Violation{
      blame: blame,
      kind: kind,
      protocol: data.contract,
      state: nil,
      message: msg,
      reply: reply,
      context: %{
        action: name,
        args: args,
        reason: text,
        states: Enum.map(data.states, &state_map(data, &1))
      }
    }
  end

  defp state_map(data, state) do
    data.machine |> Machine.to_map(state) |> Map.new(fn {k, v} -> {k, SpecValue.from_tla(v)} end)
  end

  defp policy(v, data) do
    case data.policy do
      :crash ->
        :stop

      :log ->
        Logger.error(
          "Accord.Spec violation: #{inspect(v.blame)} #{inspect(v.kind)}: #{v.context.reason}"
        )

        :pass

      :reject ->
        Logger.error(
          "Accord.Spec violation: #{inspect(v.blame)} #{inspect(v.kind)}: #{v.context.reason}"
        )

        :reject

      {mod, fun} ->
        apply(mod, fun, [v])
        :reject
    end
  end
end
