defmodule Accord.SpecTest do
  use ExUnit.Case, async: true

  @moduletag :capture_log

  alias Accord.Spec.Monitor
  alias Accord.TLA.Checker

  @spec_file Path.expand("../support/specs/Lock.tla", __DIR__)

  defmodule Contract do
    use Accord.Spec, file: "../support/specs/Lock.tla"
  end

  defmodule CustomContract do
    use Accord.Spec, file: "../support/specs/Lock.tla"

    @impl true
    def handle_call({:take, client}, reply), do: {:action, "Acquire", [client, reply]}
    def handle_call(:ping, _reply), do: :ignore
    def handle_call(request, reply), do: super(request, reply)
  end

  # A lock server. With `bug: :always_ok`, it says "ok" to a client when
  # the lock is busy. With `bug: :release_any`, any client can release.
  defmodule LockServer do
    use GenServer

    def start_link(opts), do: GenServer.start_link(__MODULE__, opts)

    @impl true
    def init(opts), do: {:ok, %{holder: nil, bug: Keyword.get(opts, :bug)}}

    @impl true
    def handle_call({tag, c}, _from, %{holder: nil} = s) when tag in [:acquire, :take],
      do: {:reply, :ok, %{s | holder: c}}

    def handle_call({tag, _c}, _from, %{bug: :always_ok} = s) when tag in [:acquire, :take],
      do: {:reply, :ok, s}

    def handle_call({tag, _c}, _from, s) when tag in [:acquire, :take], do: {:reply, :busy, s}

    def handle_call({:release, c}, _from, %{holder: c} = s), do: {:reply, :ok, %{s | holder: nil}}

    def handle_call({:release, _}, _from, %{bug: :release_any} = s),
      do: {:reply, :ok, %{s | holder: nil}}

    def handle_call({:release, _}, _from, s), do: {:reply, :error, s}
    def handle_call(:ping, _from, s), do: {:reply, :pong, s}
  end

  defp start(contract, server_opts \\ [], opts \\ []) do
    {:ok, server} = LockServer.start_link(server_opts)

    {:ok, monitor} =
      Monitor.start_link(contract, opts ++ [upstream: server, violation_policy: :reject])

    monitor
  end

  test "the model checker checks the same module" do
    assert {:ok, %{distinct_states: n}} = Checker.check(@spec_file)
    assert n > 0
  end

  test "default callbacks match messages to actions by name" do
    assert Accord.Spec.match({:release, :c1}) == {:action, "Release", [:c1]}
    assert Accord.Spec.match(:get_value) == {:action, "GetValue", []}
    assert Accord.Spec.match_call({:acquire, :c1}, :ok) == {:action, "Acquire", [:c1, :ok]}
    assert Accord.Spec.match("text") == :ignore
  end

  test "a correct run has no violation" do
    m = start(Contract)
    assert Monitor.call(m, {:acquire, :c1}) == :ok
    assert Monitor.call(m, {:acquire, :c2}) == :busy
    assert Monitor.states(m) == [%{"holder" => "c1", "grants" => 1}]
    assert Monitor.call(m, {:release, :c1}) == :ok
    assert Monitor.states(m) == [%{"holder" => "none", "grants" => 1}]
  end

  test "a reply that the action does not allow blames the server" do
    m = start(Contract, bug: :always_ok)
    assert Monitor.call(m, {:acquire, :c1}) == :ok

    assert {:accord_violation, v} = Monitor.call(m, {:acquire, :c2})
    assert v.blame == :server
    assert v.kind == :invalid_reply
    assert v.expected == ["busy"]
    assert v.context.action == "Acquire"
  end

  test "a request that the action does not allow blames the client" do
    m = start(Contract, bug: :release_any)
    assert Monitor.call(m, {:acquire, :c1}) == :ok

    assert {:accord_violation, v} = Monitor.call(m, {:release, :c2})
    assert v.blame == :client
    assert v.kind == :invalid_message
    # The monitor keeps the states from before the violation.
    assert Monitor.states(m) == [%{"holder" => "c1", "grants" => 1}]
  end

  test "an action that the module does not define blames the client" do
    m = start(Contract)
    assert {:accord_violation, v} = Monitor.call(m, :ping)
    assert v.blame == :client
    assert v.context.reason =~ "no action Ping"
  end

  test "overridden callbacks map other messages" do
    m = start(CustomContract)
    assert Monitor.call(m, :ping) == :pong
    assert Monitor.call(m, {:take, :c1}) == :ok
    assert Monitor.call(m, {:acquire, :c2}) == :busy
    assert Monitor.states(m) == [%{"holder" => "c1", "grants" => 1}]
  end

  test "events of the server are checked" do
    {:ok, server} = LockServer.start_link([])

    {:ok, m} =
      Monitor.start_link(Contract,
        upstream: server,
        downstream: self(),
        violation_policy: :reject
      )

    assert Monitor.call(m, {:acquire, :c1}) == :ok
    Monitor.event(m, {:granted, :c1})
    assert_receive {:granted, :c1}

    # c2 does not have the lock: the server is to blame, and the client
    # does not get the event.
    Monitor.event(m, {:granted, :c2})
    _ = Monitor.states(m)
    refute_received {:granted, :c2}
  end

  test "the crash policy stops the monitor" do
    Process.flag(:trap_exit, true)
    m = start(Contract, [bug: :always_ok], violation_policy: :crash)
    assert Monitor.call(m, {:acquire, :c1}) == :ok
    assert {:accord_violation, %{blame: :server}} = Monitor.call(m, {:acquire, :c2})
    assert_receive {:EXIT, ^m, {:protocol_violation, _}}
  end

  test "a contract file with a syntax error does not compile" do
    dir = Path.join(System.tmp_dir!(), "accord-spec-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    File.write!(Path.join(dir, "Bad.tla"), "---- MODULE Bad ----\nInit == x = \n====\n")

    code = """
    defmodule Accord.SpecTest.Bad do
      use Accord.Spec, file: #{inspect(Path.join(dir, "Bad.tla"))}
    end
    """

    assert_raise CompileError, ~r/cannot load the TLA\+ contract/, fn ->
      Code.compile_string(code)
    end
  end
end
