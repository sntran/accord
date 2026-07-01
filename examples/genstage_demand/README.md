# GenStage demand contract

The shortest example with the largest argument: the documented
producer/consumer rule — "never emit more events than demanded" — as an
enforceable, model-checkable contract. Before server-push events existed
in accord, this contract was inexpressible.

## What it exercises

- `event {:events, n}` — the producer pushes through the monitor, and
  the event guard `n <= tracks.demand` *is* the documented rule.
- `bounded :demand, max: 6` (the max_demand cap) plus a global
  invariant (`demand >= 0`).
- A terminal push (`event :producer_done`) ending the subscription from
  the server side.

## What TLC finds

`protocol_unbounded.ex` drops the guard: TLC interleaves asks and
pushes and drives `demand` negative in three actions. The
counterexample is the GenStage documentation rule, mechanically derived
from its absence.

```
mix accord.check Accord.Examples.Demand.Protocol
```

## What the monitor adds

An over-eager producer pushing 3 events against demand of 1
(`OverEagerProducer`) → `:guard_failed` with **server** blame — the
event direction determines fault. Today this bug surfaces as a
`Broadway`/`GenStage` consumer crash or silent buffer bloat; here it is
attributed at the boundary.

```
mix run examples/genstage_demand/demo.exs
```
