defmodule Accord.Examples.Http2.EchoServer do
  @moduledoc """
  A tiny cleartext (h2c) Bandit server for the tap-proxy demo and test: it reads
  the full request body and echoes it back with a 200. `start_link/0` returns the
  ephemeral port it listened on.

  Cleartext HTTP/2 works because Bandit sniffs the connection preface and switches
  to its HTTP/2 handler even without TLS/ALPN (`Bandit.InitialHandler`), so the
  tap proxy can read the plaintext frame layer.
  """

  defmodule EchoPlug do
    @moduledoc false
    @behaviour Plug

    import Plug.Conn

    @impl true
    def init(opts), do: opts

    @impl true
    def call(conn, _opts) do
      {:ok, body, conn} = read_body(conn)
      send_resp(conn, 200, body)
    end
  end

  @doc "Start a cleartext HTTP/2 echo server; returns `{:ok, pid, port}`."
  @spec start_link() :: {:ok, pid(), :inet.port_number()}
  def start_link do
    {:ok, pid} = Bandit.start_link(plug: EchoPlug, scheme: :http, port: 0)
    {:ok, {_ip, port}} = ThousandIsland.listener_info(pid)
    {:ok, pid, port}
  end
end
