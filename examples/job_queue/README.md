# Job queue with leases and fencing tokens

The flagship: an SQS/Oban-shaped worker↔queue lease protocol —
checkout, heartbeat, ack/nack, a visibility timeout that *arrives* as a
server event, and Kleppmann's fencing-token critique made executable.

## What it exercises

- Reply refinement: the checkout branch's `where: token > tracks.fence`
  is the fencing rule, enforced at runtime (server blame on a re-issued
  token) and as a TLC action precondition.
- A real server push: `event {:lease_expired, token}` flows through the
  monitor, guarded (`token == tracks.holding`), validated, and forwarded
  downstream. A mismatched expiry is a server violation.
- `correspondence :checkout, [:ack, :nack, :lease_expired]` — every
  lease settles, however it ends.
- `ordered :ack, by: :token` (runtime-only — labeled in the spec),
  paired local invariants (`lease_iff_working`), `forbidden`, and an
  action property (fence monotonic).

Liveness is *not* asserted here on purpose: correspondence emits its
counter bound as a TLA+ `CONSTRAINT`, and TLC checks liveness only over
constrained states (a bounded, `⚠`-flagged verdict). The circuit_breaker
example shows liveness where it is cleanly discharged by a `state_timeout`.

## What TLC finds

`protocol_leaky_lease.ex` seeds the expiry handler forgetting
`holding: 0`. The counterexample takes **three actions**: checkout →
`{:job, 1}`, the expiry event fires, and the worker is `:idle` with
`holding = 1` — it still believes it owns a job the queue will hand to
someone else. Double processing, found exhaustively before any code ran.

```
mix accord.check Accord.Examples.JobQueue.Protocol
```

The cross-worker claim — no two workers hold the same lease — is
checkable with `distinct :holding, empty: 0` at `sessions: 2`: see the
DistributedQueue fixture (`test/support/protocols/distributed_queue.ex`),
where TLC proves the fencing constraint makes leases unique, and hands
both workers token 1 in two steps when the constraint is dropped. The
mutual-exclusion variant lives in the DistributedLock fixture.

## What the monitor adds

- Stale ack after an expiry → `:guard_failed`, client blame, span on the
  guard — "who leaked the lease" answered mechanically.
- A queue re-issuing fence token 1 (`StaleTokenServer`) →
  `:constraint_failed`, server blame, the moment the stale lease is
  handed out.
- An expiry push for a token the worker no longer holds → server blame.

```
mix run examples/job_queue/demo.exs
```

Or open [notebook.livemd](notebook.livemd) in Livebook for the interactive
walkthrough — protocol, blame diagnostics, the TLC counterexample, and a
trace-validation round trip.
