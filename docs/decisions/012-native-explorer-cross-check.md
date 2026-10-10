# ADR-012: Native explorer and cross-check with TLC

## Status

Accepted

## Context

TLC is the only model checker of accord. It needs Java and `tla2tools.jar`.
TLC checks the generated TLA+ spec. It cannot find a defect in the
translation from the protocol to TLA+: if `BuildActions` drops an update,
TLC checks the wrong protocol and reports no error. Trace validation
(ADR-010) finds some of these defects, but only on the traces that a test
records.

The protocol already has an executable form: the IR has the guards, the
updates, and the `where:` constraints as Elixir functions. The monitor
runs them. A model checker that runs the same functions on the same
finite domains does not need the TLA+ translation.

## Decision

**Add a native explicit-state model checker (`Accord.Explore`), and a
cross-check (`Accord.CrossCheck`) that compares it with TLC.**

- `Accord.Explore.Model` makes an executable model from the IR and the
  model config. It runs the protocol functions, and it follows the rules
  of the monitor (for example, a reply goes to the first branch that
  accepts it). It uses the declared abstractions of the TLA+ model: the
  finite domains, lists as placeholder lists, untimed state timeouts,
  sessions, and shared tracks.
- `Accord.Explore` does a breadth-first search with the rules of TLC: a
  state outside the state constraint is not explored but is checked; an
  action property is checked on all steps; a deadlock is a state with no
  successor. It checks the safety properties of the spec, and then each
  liveness property on the full state graph, under the fairness of that
  property (Tarjan's algorithm, with the Emerson-Lei method for strong
  fairness).
- The explorer does not depend on the TLA+ passes. The boundary test
  pins this. So a defect in the translation makes the two checkers
  disagree.
- `Accord.CrossCheck` runs both checkers on the same model. TLC is the
  reference. It compares the state graph (`-dump dot`: the states, the
  steps, the count, the depth), the symmetry-reduced count, and the
  verdict of each safety check. When both checkers find a violation,
  both traces must have the minimum length, and each trace must replay
  in the other checker.
- A corpus that passes in both checkers proves little. So the
  cross-check also runs on mutants of each protocol
  (`Accord.CrossCheck.Mutant`) and on random protocols
  (`Accord.CrossCheck.RandomProtocol`).
- `mix accord.explore` checks protocols without Java. `mix
  accord.crosscheck` runs the cross-check.

## Consequences

- The first runs found five differences between the monitor and the
  TLA+ spec. Two of them made TLC miss real bugs: an update that ignored
  an earlier argument read the wrong argument in the spec, and an update
  arm for a two-value reply was dropped from the spec. All five are now
  fixed. `test/support/probes/` has one protocol for each, and the
  cross-check tests check that the two checkers agree on them. See
  `docs/cross-check.md`.
- The explorer follows the monitor. If the spec differs from the monitor
  again, `mix accord.explore` and `mix accord.check` give different
  results, and the cross-check shows where.
- Two correct checkers can find different liveness counterexamples, so
  the cross-check does not compare lasso lengths. It replays each lasso
  in the other checker instead.
- The explorer's symmetry reduction is only
  over sessions, not over model-value symmetry sets (the full model is
  still correct, but larger). It supports a user state constraint
  only as a conjunction of `track op integer` terms. It reports a model
  that it cannot evaluate, and does not check it.
- Each TLC run pays JVM startup. A cross-check of one protocol does about
  five runs. The cross-check is a tool for development and CI, not for
  each test run.
