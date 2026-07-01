# Payment lifecycle

authorize → partial captures → finalize / void → refunds. The
property-algebra showcase: everything here works end to end with no
planned extensions.

## What it exercises

- Cumulative guards carrying the money rules (`captured + amount <=
  authorized`, `refunded + amount <= captured`).
- Global invariants (`never_overcapture`, `never_overrefund`), an action
  property (money only flows forward), `precedence`
  (authorize-before-capture), a local invariant on a terminal state
  (void means no money moved), and three `reachable` checks.
- Inline model config (`domain:` on tracks, `model do ... end` for the
  message amount).

## What TLC finds

`protocol_percall_guard.ex` seeds the classic double-capture: the guard
checks `amount <= authorized` per call instead of cumulatively. TLC's
counterexample reads like an incident postmortem: authorize(4),
capture(3), capture(3) — captured 6 > authorized 4. The guard *is* the
model; a wrong guard is a wrong state space.

```
mix accord.check Accord.Examples.Payment.Protocol
```

## What the monitor adds

- `{:capture, 3}` against a 2-unit authorization → `:guard_failed`,
  client blame, span on the guard.
- `{:refund, 1}` while still `:authorized` → `:invalid_message` with the
  valid-message list — "you refunded before finalizing" caught in test,
  not in month-end reconciliation.
- `Accord.Test.FaultyServer` injections (`:wrong_reply_type`,
  `:timeout`) → server blame.

```
mix run examples/payment/demo.exs
```
