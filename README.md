# Accord

Protocol contracts for Elixir: one specification, checked twice.

Accord resurrects the idea from Joe Armstrong's UBF ("Getting Erlang to talk
to the outside world", Erlang Workshop 2002): declare the protocol between
two parties as a typed state machine, put a contract checker between them,
and let it assign blame when either side breaks the rules. Accord compiles
that declaration into two artifacts:

- A **runtime monitor** — a gen_statem proxy that validates every call,
  cast, and server-push event, and assigns blame on violations: `:client`,
  `:server`, or `:property` (labeled with your protocol's role names).
- A **TLA+ specification** — model-checked exhaustively with TLC, including
  N interleaved client sessions against shared server state. Counterexamples
  map back to your Elixir source.

The contract is the design tool: write it first, let TLC find the
interleaving you didn't think of, then keep the monitor between your
processes so reality never drifts from the design.

## The flagship example

A worker leases jobs from a queue with fencing tokens; the visibility
timeout *arrives* as a server event (from `examples/job_queue/`):

```elixir
defmodule JobQueue.Protocol do
  use Accord.Protocol

  initial :idle

  track :fence, :non_neg_integer, default: 0, domain: 0..3
  track :holding, :non_neg_integer, default: 0, domain: 0..3

  state :idle do
    on :checkout do
      branch({:job, token :: pos_integer()},
        goto: :working,
        where: fn {:job, token}, tracks -> token > tracks.fence end
      )

      branch :empty, goto: :idle

      update fn _msg, reply, tracks ->
        case reply do
          {:job, token} -> %{tracks | fence: token, holding: token}
          :empty -> tracks
        end
      end
    end

    on :stop, reply: :stopped, goto: :stopped
  end

  state :working do
    on {:ack, token :: pos_integer()} do
      guard fn {:ack, token}, tracks -> token == tracks.holding end
      branch :done, goto: :idle
      update fn _msg, _reply, tracks -> %{tracks | holding: 0} end
    end

    # The lease expiry is pushed by the queue, through the monitor.
    event {:lease_expired, token :: pos_integer()} do
      guard fn {:lease_expired, token}, tracks -> token == tracks.holding end
      goto :idle
      update fn {:lease_expired, _token}, tracks -> %{tracks | holding: 0} end
    end
  end

  state :stopped, terminal: true

  property :lease_iff_working do
    invariant :working, fn _msg, tracks -> tracks.holding > 0 end
    invariant :idle, fn _msg, tracks -> tracks.holding == 0 end
  end

  property :every_checkout_settles do
    correspondence :checkout, [:ack, :lease_expired]
  end
end
```

Forget `holding: 0` in the expiry handler and `mix accord.check` finds the
double-processing bug in three actions, before any implementation exists:

```
✗ JobQueue.ProtocolLeakyLease — invariant LeaseIffWorkingIdle violated
  State 1: checkout → {:job, 1}     fence = 1, holding = 1
  State 2: lease_expired(1)         state = idle, holding = 1   ← the worker
                                     still thinks it owns the job
```

At runtime the monitor answers "who leaked the lease" mechanically — a
worker acking with a stale token is client blame on the guard; a queue
re-issuing fence token 1 is server blame on the `where:` constraint, with a
diagnostic pointing at the clause:

```
error: server reply violated its where: constraint
   ╭─[examples/job_queue/protocol.ex:30:14]
30 │       branch({:job, token :: pos_integer()},
   •              ──────────────┬───────────────
   •                            ╰── where: constraint defined here
32 │         where: fn {:job, token}, tracks -> token > tracks.fence end
   ╰─────
     note: sent :checkout, got {:job, 1}
```

## Multi-session model checking

The bugs that motivate fencing tokens live *between* clients. With
`sessions: 2` and shared tracks, TLC interleaves two sessions against the
server's state:

```elixir
track :holder, :term, default: nil, shared: true
track :fence_token, :non_neg_integer, default: 0, shared: true

property :mutual_exclusion do
  exclusive :locked
end
```

For the guarded distributed lock TLC proves mutual exclusion exhaustively.
Drop the `holder == nil` conjunct from the acquire constraint and TLC
produces the two-sessions-both-locked counterexample — with fence tokens
still perfectly monotonic. Fencing alone is not a lock, and now that fact is
mechanical.

Per-session tracks get the dual check: `distinct :holding, empty: 0` states
that no two sessions ever hold the same lease. The fencing constraint makes
it provable; without the constraint TLC hands both workers token 1 in two
steps.

Shared tracks are ghost state: verified by TLC, observed per-session at
runtime (the server is the ground truth). The asymmetry is declared, never
silent — see `docs/architecture.md` for the full runtime-vs-TLC table.

## Examples

Four pedagogical examples, each with a seeded design bug pinned by a real
TLC run and blame stories pinned by monitor tests — see
[examples/](examples/):

1. **circuit_breaker** — the intro: branching, `where:`, liveness under
   per-action fairness.
2. **payment** — cumulative money guards, the full property algebra.
3. **job_queue** — the flagship above.
4. **genstage_demand** — the documented "never exceed demand" rule as an
   enforceable server-push contract.

Two more run the monitor against real third-party servers (dev/test deps
only): **phoenix_channels** model-checks the Phoenix Channels lifecycle and
taps a live Phoenix endpoint through a wrapping serializer, and **http2**
wires the stream monitor between a raw client and a live Bandit to catch
RFC 9113 divergences — see [`docs/case-study-phoenix-channels.md`](docs/case-study-phoenix-channels.md)
and [`docs/case-study-http2-bandit.md`](docs/case-study-http2-bandit.md).

## Core concepts

- **States and transitions** — the session state machine: `on` (call with
  typed reply branches), `cast` (client fire-and-forget), `event`
  (server push, may change state).
- **Tracks** — typed accumulators updated on transitions; `shared: true`
  marks server-side state for multi-session checking.
- **Guards and `where:` constraints** — enabling conditions on messages and
  reply refinements, enforced at runtime and modeled as preconditions.
- **Properties** — invariants, action properties, liveness (with
  `assuming:` fairness), correspondence, bounds, ordering, precedence,
  reachability, and cross-session `exclusive`.
- **Blame** — derived from message direction; the sender is at fault.
  Role names (`role :consumer`) label it in diagnostics.
- **Model config** — finite domains inline (`domain:` on tracks, a
  `model do ... end` block) or in `.accord_model.exs`.

## Model checking workflow

```bash
mix accord.tla MyApp.Protocol           # print the generated spec
mix accord.check                        # model-check all protocols
mix accord.check MyApp.Protocol         # one protocol
mix accord.check --strict               # fail protocols with tla: :off
mix accord.check --no-deadlock          # disable deadlock detection
```

Spec generation is strict by default: anything the model cannot faithfully
express is a compile error with a source span (`tla: :warn` downgrades it
and deletes the stale spec — an outdated spec is never verified). Deadlock
checking is on: terminal states self-stutter, so a reported deadlock is a
real stuck state. Checks the model cannot express (`ordered`, `precedence`,
keyed correspondence) are labeled runtime-only in the spec and in the check
output.

TLC requires Java and `tla2tools.jar`. Set the `TLA2TOOLS_JAR` environment
variable, place it at `~/.tla/tla2tools.jar`, or in the project root.

## Rolling upgrades

Servers and clients deploy at different times; for a window, old clients
talk to the new contract. `mix accord.compat` makes that window a CI
property instead of a hope:

```bash
mix accord.compat --snapshot MyApp.Protocol priv/protocol-v1.ir   # on release
mix accord.compat MyApp.Protocol --against priv/protocol-v1.ir    # on every PR
```

The check is a static simulation over both contracts: arguments may only
widen, replies may only narrow, server pushes must stay understood, and
autonomous movement (state timeouts) must not change (C001–C010; guard
changes are advisories). The snapshot is the released contract — it cannot
drift from what shipped.

## Installation

Add `accord` to your dependencies in `mix.exs`:

```elixir
def deps do
  [
    {:accord, "~> 0.1.0"}
  ]
end
```

## License

MIT - see [LICENSE](LICENSE) for details.
