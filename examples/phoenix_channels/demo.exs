# Run with: mix run examples/phoenix_channels/demo.exs
#
# accord as a live conformance monitor for Phoenix Channels — the realtime
# protocol under Channels and LiveView, which has no conformance tooling. A real
# Phoenix endpoint runs with the tapping serializer wired in (one line of config);
# a raw WebSocket client drives it. The monitor checks every channel message and
# assigns blame.
#
# It shows: a normal session raises nothing; a channel that replies twice to one
# request is blamed on the server (an obligation Phoenix does not enforce for you);
# a push before join is blamed on the client; and a stale join_ref — which Phoenix
# silently drops — is surfaced.

alias Accord.Examples.PhoenixChannels.{Channel, Endpoint, PubSub, Tap, WsClient}

Application.put_env(:accord, Endpoint,
  adapter: Bandit.PhoenixAdapter,
  http: [ip: {127, 0, 0, 1}, port: 0],
  server: true,
  secret_key_base: String.duplicate("a", 64),
  pubsub_server: PubSub
)

{:ok, _} = Phoenix.PubSub.Supervisor.start_link(name: PubSub)
{:ok, _} = Endpoint.start_link()
{:ok, _} = Tap.start_link()
{:ok, {_ip, port}} = Bandit.PhoenixAdapter.server_info(Endpoint, :http)

compiled = Channel.Protocol.__compiled__()

report = fn label, violations ->
  IO.puts("== #{label} ==")

  case violations do
    [] ->
      IO.puts("accord: no violations — the traffic conformed to the spec.\n")

    list ->
      for v <- list, do: IO.puts(Accord.Violation.Report.format(v, compiled))
      IO.puts("")
  end
end

# Normal session against a correct channel.
Tap.reset()
sock = WsClient.connect(port)
WsClient.join(sock, "room:lobby", "1")
WsClient.push(sock, "1", "room:lobby", "ping", "2")
WsClient.leave(sock, "1", "room:lobby", "3")
_ = WsClient.recv_many(sock, 3)
report.("normal session (correct channel)", Tap.violations())
WsClient.close(sock)

# A channel that replies twice to one request.
Tap.reset()
sock = WsClient.connect(port)
WsClient.join(sock, "buggy:1", "1")
WsClient.push(sock, "1", "buggy:1", "work", "2")
_ = WsClient.recv_many(sock, 3)
report.("channel replies twice to one request", Tap.violations())
WsClient.close(sock)

# A push before joining the topic.
Tap.reset()
sock = WsClient.connect(port)
WsClient.push(sock, nil, "room:lobby", "ping", "1")
_ = WsClient.recv_many(sock, 1)
report.("push before join", Tap.violations())
WsClient.close(sock)

# A stale join_ref, which Phoenix silently drops.
Tap.reset()
sock = WsClient.connect(port)
WsClient.join(sock, "room:lobby", "1")
_ = WsClient.recv_many(sock, 1)
WsClient.push(sock, "999", "room:lobby", "ping", "5")
WsClient.push(sock, "1", "room:lobby", "ping", "6")
_ = WsClient.recv_many(sock, 1)
report.("stale join_ref (Phoenix drops it silently)", Tap.violations())
WsClient.close(sock)

IO.puts("""
The normal session raised nothing. The double reply was blamed on the server —
an obligation Phoenix leaves to your channel code. The premature push was blamed
on the client. The stale join_ref, which Phoenix drops with no reply and no log,
was surfaced by the monitor — the "why did my events stop arriving?" bug, made
visible with blame.\
""")
