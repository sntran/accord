# Circuit breaker

The intro example: closed/open/half-open with a trip threshold of 3,
recognizable to anyone who has run `fuse` or hand-rolled a breaker around a
flaky downstream.

## What it exercises

- Reply-shape-driven branching: `:ok` / `:error` / `:tripped` pick the next
  state, refined by `where:` constraints on the failure counter.
- A `failures` track with an inline model domain (`domain: 0..4`).
- A protocol constant (`const :threshold, 3`) shared by the constraints
  and the invariant — declared once, substituted at compile time.
- A state timeout (`state_timeout 30_000, goto: :half_open`): the
  cooldown fires on its own, and its automatic weak fairness discharges
  the `breaker_recovers` liveness property with no `assuming:` needed.
- Local invariant (`threshold_respected`), `forbidden` (counter
  overshoot), `precedence` (no probe without a trip), and `reachable`.

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
