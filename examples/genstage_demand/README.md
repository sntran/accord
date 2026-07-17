# GenStage demand contract

The GenStage producer/consumer demand rule as an enforceable contract:

- `ask(n)` — the consumer asks for up to `n` events (increases demand)
- the producer pushes `{:events, n}` — but must never send more than the
  outstanding demand

## What the protocol declares

- `{:events, n}` is a server-pushed event whose guard is `n <=
  tracks.demand` — the demand rule.
- A `demand` track (0..6), with `bounded :demand, max: 6` and a global
  invariant that demand never goes negative.
- A terminal push (`event :producer_done`) ends the subscription from the
  producer side.

## The seeded bug

`protocol_unbounded.ex` drops the guard on the events push. Model checking
finds it:

    mix accord.check Accord.Examples.Demand.Protocol

The counterexample, in three steps: the producer pushes more events than
were asked for and drives `demand` negative.

## What the demo shows

    mix run examples/genstage_demand/demo.exs

- The normal flow: ask for 3, the producer emits 2 (within demand).
- A producer pushing 3 events against demand of 1 (`guard_failed`, server
  blame — the event direction makes it the producer's fault).
