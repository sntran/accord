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
  successor. It checks the safety properties of the spec. It does not
  check liveness yet.
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
  TLA+ spec. `test/support/probes/` has one protocol for each, and
  `test/accord/cross_check_test.exs` pins each difference. See
  `docs/cross-check.md`.
- Two of the differences make TLC miss real bugs: an update that ignores
  an earlier argument reads the wrong argument in the spec, and an update
  arm for a two-value reply is dropped from the spec.
- The explorer follows the monitor where the spec differs from it. So
  `mix accord.explore` and `mix accord.check` can give different results
  on a protocol that uses one of these forms.
- The explorer does not check liveness. Its symmetry reduction is only
  over sessions, not over model-value symmetry sets (the full model is
  still correct, but larger). It supports a user state constraint
  only as a conjunction of `track op integer` terms. It reports a model
  that it cannot evaluate, and does not check it.
- Each TLC run pays JVM startup. A cross-check of one protocol does about
  five runs. The cross-check is a tool for development and CI, not for
  each test run.
