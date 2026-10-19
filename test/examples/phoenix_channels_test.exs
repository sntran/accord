defmodule Accord.Examples.PhoenixChannelsTest do
  use ExUnit.Case, async: false

  @moduletag :capture_log

  alias Accord.Examples.PhoenixChannels.{Channel, Endpoint, SlipstreamClient, Tap, WsClient}
  alias Accord.Test.TLACheck

  setup_all do
    Application.put_env(:accord, Endpoint,
      adapter: Bandit.PhoenixAdapter,
      http: [ip: {127, 0, 0, 1}, port: 0],
      server: true,
      secret_key_base: String.duplicate("a", 64),
      pubsub_server: Accord.Examples.PhoenixChannels.PubSub
    )

    start_supervised!({Phoenix.PubSub, name: Accord.Examples.PhoenixChannels.PubSub})
    start_supervised!(Endpoint)
    start_supervised!(Tap)

    {:ok, {_ip, port}} = Bandit.PhoenixAdapter.server_info(Endpoint, :http)
    %{port: port}
  end

  setup do
    Tap.reset()
    :ok
  end

  describe "live monitoring of a real Phoenix endpoint" do
    test "a normal session against a correct channel produces no violations", %{port: port} do
      # The monitor must be faithful: a legitimate join / push+reply / leave
      # session raises nothing.
      sock = WsClient.connect(port)
      WsClient.join(sock, "room:lobby", "1")
      WsClient.push(sock, "1", "room:lobby", "ping", "2")
      WsClient.leave(sock, "1", "room:lobby", "3")
      # Await the three replies so every encode! has run before draining.
      _ = WsClient.recv_many(sock, 3)

      assert Tap.violations() == []
      WsClient.close(sock)
    end

    test "a channel that replies twice to one request is blamed on the server", %{port: port} do
      # BuggyChannel.handle_in("work", ...) calls reply/2 twice for one ref.
      # Phoenix sends both; the monitor catches the second (nothing pending).
      sock = WsClient.connect(port)
      WsClient.join(sock, "buggy:1", "1")
      WsClient.push(sock, "1", "buggy:1", "work", "2")
      _ = WsClient.recv_many(sock, 3)

      violations = Tap.violations()
      assert Enum.any?(violations, &(&1.blame == :server and &1.kind == :guard_failed))
      refute Enum.any?(violations, &(&1.blame == :client))
      WsClient.close(sock)
    end

    test "pushing before joining a topic is blamed on the client", %{port: port} do
      # The client sends a custom event on a topic it never joined. Phoenix
      # answers "unmatched topic"; the monitor flags the premature push.
      sock = WsClient.connect(port)
      WsClient.push(sock, nil, "room:lobby", "ping", "1")
      _ = WsClient.recv_many(sock, 1)

      violations = Tap.violations()
      assert Enum.any?(violations, &(&1.blame == :client and &1.kind == :invalid_message))
      WsClient.close(sock)
    end

    test "a stale join_ref is surfaced as client blame (Phoenix drops it silently)", %{port: port} do
      # After joining with join_ref "1", the client sends a push with a stale
      # join_ref "999" (as a rejoined-but-not-updated client would). Phoenix
      # silently drops it — no reply, no log. accord surfaces it. The follow-up
      # valid ping's reply is a barrier so the stale push is observed first.
      sock = WsClient.connect(port)
      WsClient.join(sock, "room:lobby", "1")
      _ = WsClient.recv_many(sock, 1)
      WsClient.push(sock, "999", "room:lobby", "ping", "5")
      WsClient.push(sock, "1", "room:lobby", "ping", "6")
      _ = WsClient.recv_many(sock, 1)

      violations = Tap.violations()
      assert Enum.any?(violations, &(&1.blame == :client and &1.message == :stale_message))
      WsClient.close(sock)
    end

    test "a server-initiated push mid-session is not a violation", %{port: port} do
      # `subscribe` triggers a server push (server_event) and a reply; both are
      # legitimate, so the session stays clean.
      sock = WsClient.connect(port)
      WsClient.join(sock, "room:lobby", "1")
      WsClient.push(sock, "1", "room:lobby", "subscribe", "2")
      _ = WsClient.recv_many(sock, 3)

      assert Tap.violations() == []
      WsClient.close(sock)
    end
  end

  describe "conformance of an independent client library (Slipstream)" do
    # Slipstream is a third-party Elixir channels client, unrelated to the raw
    # WsClient the other tests use. A clean run means the monitor is faithful
    # across implementations — and confirms Slipstream conforms to the protocol.
    setup %{port: port} do
      uri = "ws://127.0.0.1:#{port}/socket/websocket?vsn=2.0.0"
      {:ok, pid} = SlipstreamClient.start_link(parent: self(), uri: uri)
      assert_receive {:slipstream, :connected}, 3000
      on_exit(fn -> if Process.alive?(pid), do: GenServer.stop(pid) end)
      %{client: pid}
    end

    test "a normal session raises no violations", %{client: pid} do
      SlipstreamClient.join_topic(pid, "room:lobby")
      assert_receive {:slipstream, {:joined, "room:lobby"}}, 3000
      SlipstreamClient.push_event(pid, "room:lobby", "ping")
      assert_receive {:slipstream, {:reply, _ref, {:ok, _}}}, 3000
      SlipstreamClient.leave_topic(pid, "room:lobby")
      assert_receive {:slipstream, {:left, "room:lobby"}}, 3000

      assert Tap.violations() == []
    end

    test "two concurrent channels raise no violations", %{client: pid} do
      SlipstreamClient.join_topic(pid, "room:a")
      assert_receive {:slipstream, {:joined, "room:a"}}, 3000
      SlipstreamClient.join_topic(pid, "room:b")
      assert_receive {:slipstream, {:joined, "room:b"}}, 3000
      SlipstreamClient.push_event(pid, "room:a", "ping")
      assert_receive {:slipstream, {:reply, _, {:ok, _}}}, 3000
      SlipstreamClient.push_event(pid, "room:b", "ping")
      assert_receive {:slipstream, {:reply, _, {:ok, _}}}, 3000

      assert Tap.violations() == []
    end
  end

  describe "model checking" do
    @describetag :tmp_dir

    test "the channel lifecycle verifies", %{tmp_dir: tmp_dir} do
      TLACheck.assert_passes(Channel.Protocol, tmp_dir: tmp_dir)
    end
  end
end
