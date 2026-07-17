# Circuit breaker

The breaker sits in front of a flaky downstream and has three states:

- `closed` — passes requests through and counts consecutive failures
- `open` — rejects every request
- `half_open` — lets a single probe request through

It trips (`closed` → `open`) after 3 failures in a row. After a 30s
cooldown it moves to `half_open` on its own; a successful probe closes it,
a failed probe opens it again.

## What the protocol declares

- The reply (`:ok` / `:error` / `:tripped`) selects the next state, and
  `where:` constraints on the failure counter decide which reply is valid
  at each count.
- A `failures` track (0..4) and the trip threshold as a constant
  (`const :threshold, 3`), used by both the constraints and the invariant.
- A state timeout (`state_timeout 30_000, goto: :half_open`) for the
  cooldown.
- Properties: the failure count never passes the threshold, there is no
  probe without a trip, and the breaker eventually recovers from `open`.

## The seeded bug

`protocol_stuck_counter.ex` forgets to reset `failures` to 0 when a
half-open probe succeeds. Model checking finds it:

    mix accord.check Accord.Examples.CircuitBreaker.Protocol

The counterexample: trip (failures 0 → 3), probe, recover — the breaker is
back in `closed` but with `failures = 3`, so the next single error trips
it again.

## What the demo shows

    mix run examples/circuit_breaker/demo.exs

- Normal operation: three failures trip the breaker, then it rejects.
- A client sending a message the current state does not accept
  (`invalid_message`, client blame).
- A server replying `:error` on the failure that should trip, instead of
  `:tripped` (`constraint_failed`, server blame).
