# Examples

Runnable, model-checked protocol examples in pedagogical order. Each ships a
correct server, at least one seeded design bug that real TLC catches (pinned
in `test/examples/`), and a `demo.exs` showing the blame stories.

| # | Example | Teaches | Seeded bug TLC finds |
|---|---------|---------|----------------------|
| 1 | [circuit_breaker](circuit_breaker/) | branching + `where:`, tracks, invariants, liveness with `assuming:` | flapping breaker (recovery forgets the counter) |
| 2 | [payment](payment/) | cumulative guards, the full property algebra | double capture (per-call guard) |
| 3 | [job_queue](job_queue/) | **flagship** — fencing tokens, server-push expiry events, correspondence | double processing (expiry leaks the lease) |
| 4 | [genstage_demand](genstage_demand/) | server-push as the contract itself | over-delivery (demand goes negative) |

For the multi-session dimension — two workers interleaved against shared
state, `exclusive` mutual exclusion — see the `DistributedLock` fixture at
`test/support/protocols/distributed_lock.ex`: TLC proves mutual exclusion at
`sessions: 2` and produces the two-sessions-both-locked counterexample when
the holder guard is dropped.

Run any demo:

```
mix run examples/job_queue/demo.exs
```

Model-check everything (needs `tla2tools.jar` — see `mix help accord.check`):

```
mix accord.check
```

The examples compile in dev and test, so a DSL change that breaks one breaks
CI. The seeded bugs are pinned by `:tlc`-tagged tests that run real TLC.
