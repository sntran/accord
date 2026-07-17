# Job queue with leases and fence tokens

A worker leases a job from the queue:

- `checkout` — take a job; the queue replies `{:job, token}`
- `heartbeat(token)` — keep the lease; must present the current token
- `ack(token)` / `nack(token)` — finish or return the job
- the queue can push `{:lease_expired, token}` when a lease times out

Each checkout returns a token strictly larger than any issued before (a
fence token), so a worker holding an expired lease can be told apart from
the one holding the current lease.

## What the protocol declares

- The checkout reply is constrained by `where: token > tracks.fence`, so
  the issued token always increases.
- Tracks for the highest token issued so far (`fence`) and the token this
  worker holds (`holding`).
- The expiry is a server-pushed event, guarded so it only applies to the
  token the worker currently holds.
- Properties: the held token never exceeds the fence, a lease is held only
  while working, and every checkout is settled — by ack, nack, or expiry.

Liveness is not asserted here: `correspondence` emits a state constraint
that makes a liveness verdict only cover bounded runs (`mix accord.check`
flags this with `⚠`). The circuit_breaker example shows liveness where a
state timeout discharges it cleanly.

## The seeded bug

`protocol_leaky_lease.ex` forgets to clear `holding` when a lease expires.
Model checking finds it:

    mix accord.check Accord.Examples.JobQueue.Protocol

The counterexample, in three steps: checkout `{:job, 1}`, the expiry
fires, and the worker is back in `:idle` still believing it holds token 1
— a job the queue will hand to someone else.

## What the demo shows

    mix run examples/job_queue/demo.exs

- The normal flow: checkout, heartbeat, ack.
- The queue pushing a lease-expired event.
- A client acking after its lease expired (`invalid_message`, client
  blame).
- A queue reissuing token 1 instead of increasing it
  (`constraint_failed`, server blame).

The cross-worker rule — no two workers hold the same lease — is checked
separately in `test/support/protocols/distributed_queue.ex`, where model
checking proves it with `sessions: 2`.

Or open [notebook.livemd](notebook.livemd) in Livebook for an interactive
walkthrough.
