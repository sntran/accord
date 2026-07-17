# Payment lifecycle

A card payment moves through these steps:

- `authorize(n)` — reserve up to `n` on the card
- `capture(n)` — take money; captures accumulate and must not exceed the
  authorized amount
- `finalize` — close captures; refunds are only allowed afterward
- `refund(n)` — return money; refunds must not exceed what was captured
- `void` — cancel before any money moved

## What the protocol declares

- Guards carry the money rules: `captured + amount <= authorized` on
  capture, `refunded + amount <= captured` on refund.
- Tracks for the authorized, captured, and refunded amounts, with inline
  domains.
- Properties: captures never exceed the authorization, refunds never
  exceed captures, money only moves forward, and capture only happens
  after authorize.

## The seeded bug

`protocol_percall_guard.ex` checks `amount <= authorized` per call instead
of against the running total. Model checking finds it:

    mix accord.check Accord.Examples.Payment.Protocol

The counterexample: authorize(4), capture(3), capture(3) — captured 6
exceeds authorized 4.

## What the demo shows

    mix run examples/payment/demo.exs

- The normal flow: authorize, two captures, finalize, refund.
- A client capturing more than authorized (`guard_failed`, client blame).
- A client refunding before finalizing (`invalid_message`, client blame).
