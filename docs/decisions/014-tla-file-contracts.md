# ADR-014: Contracts in TLA+ files

## Status

Accepted

## Context

An accord contract is an Elixir module (`use Accord.Protocol`). Accord
makes a TLA+ specification from it (ADR-005). Many teams already write
TLA+ specifications by hand. They want to monitor their Elixir
processes against those specifications, and to model-check the same
files, without a second contract in Elixir.

A TLA+ specification has no messages. It has actions, and an action can
have parameters. A monitor must map each message of a process to an
action with arguments.

## Decision

**Add `Accord.Spec`, a behaviour for contracts in a TLA+ file, and
`Accord.Spec.Monitor`, a proxy process that monitors a server against
it.**

- `use Accord.Spec, file: "lock.tla"` loads the module at compile time
  (a TLA+ error is a compile error) and makes the default callbacks.
- The callbacks map messages to actions: `handle_call(request, reply)`,
  `handle_cast(request)`, and `handle_info(message)` (an event of the
  server). Each gives `{:action, name, args}` or `:ignore`. These are the
  callbacks of an OTP behaviour, not a map in the options, so that a
  contract can use pattern matching and `super/2`.
- The default callbacks match by name: the tag of the message, in
  CamelCase, is the action, and the other elements are the arguments.
  For a call, the reply is the last argument.
- The monitor keeps a set of states of the specification, because an
  action can allow more than one next state for the same arguments. It
  computes the next states with `Accord.TLA.Checker.Machine`, with the
  rules of TLC.
- Blame comes from the direction of the message, as in ADR-008. For a
  call, the monitor runs the action again with the last parameter open:
  the action then gives the values of the reply that it allows (as it
  gives the values of primed variables). When it allows no reply, the
  request was wrong (client). When it allows other replies, the reply
  was wrong (server).
- An `INVARIANT` of the config that is false in a next state blames the
  specification (`:property`).

## Consequences

- One TLA+ file is the contract for the monitor and the input of the
  model checker.
- A call is checked when the reply comes back, so the server sees a
  wrong request before the monitor reports it. A cast and an event are
  checked before the monitor forwards them.
- When an action reads the reply before it gives the reply a value, the
  open run cannot find the allowed replies; the monitor then blames the
  server.
- The monitor does not check liveness properties.
