# Circuit breaker

The intro example: closed/open/half-open with a trip threshold of 3,
recognizable to anyone who has run `fuse` or hand-rolled a breaker around a
flaky downstream.

## What it exercises

- Reply-shape-driven branching: `:ok` / `:error` / `:tripped` pick the next
  state, refined by `where:` constraints on the failure counter.
- A `failures` track with an inline model domain (`domain: 0..4`).
- Local invariant (`threshold_respected`), `forbidden` (counter overshoot),
  `precedence` (no probe without a trip), `reachable`, and liveness with
  per-action fairness (`assuming: [:attempt_reset]` — "someone keeps
  polling", the obligation a future state-timeout feature would discharge).

## What TLC finds

`protocol_stuck_counter.ex` seeds the classic flapping-breaker bug: the
half-open success branch forgets `failures: 0`. TLC's counterexample: trip
(failures 0 → 3), probe, recover — the breaker is `:closed` with
`failures = 3`, violating `threshold_respected`. In production this breaker
instantly re-trips on the first post-recovery error.

```
mix accord.check Accord.Examples.CircuitBreaker.Protocol
```

## What the monitor adds

- A client probing (`:attempt_reset`) while the breaker is closed →
  `:invalid_message`, client blame.
- A server replying `:error` at the threshold instead of `:tripped`
  (`MislabelingServer`) → `:constraint_failed`, server blame, span on the
  `where:` clause. Same contract rule, caught at the reply boundary.

```
mix run examples/circuit_breaker/demo.exs
```
