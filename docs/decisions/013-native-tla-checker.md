# ADR-013: A TLA+ model checker in Elixir

## Status

Accepted

## Context

After ADR-012, accord can check a protocol without Java (`mix
accord.explore`). But the explorer does not read TLA+. It runs the
protocol functions. These parts of accord still need TLC, and so Java:

- `mix accord.check`, which checks the generated `.tla` and `.cfg` files;
- `mix accord.check --extra`, which checks hand-written TLA+ modules;
- `Accord.TLA.TraceSpec` and `Accord.Test.TraceCheck`, which replay a
  runtime trace against the spec (ADR-010);
- `Accord.Test.TLACheck`, and the reference of `mix accord.crosscheck`.

TLA+ is a text language. A checker for it is a lexer, a parser, an
evaluator, and a search. The rules of TLC for these steps are in the
TLC source, and TLC has a large test suite of models with their
expected results.

## Decision

**Add a TLA+ model checker in Elixir (`Accord.TLA.Checker`), and make it
the default engine. TLC stays as an optional reference.**

- The checker has its own lexer, parser (with the layout rules of `/\`
  and `\/` lists), and evaluator. The standard modules (Naturals,
  Integers, Sequences, FiniteSets, Bags, TLC, TLCExt, Json, and others)
  and many community modules are in Elixir. Other modules come from
  `.tla` files.
- The checker follows the rules of TLC, not only the semantics of TLA+.
  The two can differ: for example, TLC generates next states from the
  conjuncts from left to right, splits the next-state action into named
  actions, counts the generated states per action, and checks the
  invariants of a state before it puts the state in the queue. The
  result of a check (the verdict, the counts of states, the depth, and
  the error trace) must be the same as the result of TLC.
- Before a check, the checker does the semantic checks of SANY (the
  parser of TLC): names, arguments, `INSTANCE` substitutions, levels,
  labels, and proofs (`Accord.TLA.Checker.Semantic`). A module that SANY
  rejects is rejected, with the same error code.
- `Accord.TLA.Engine` runs a check with the native checker (default) or
  with TLC (`:engine` option, or `ACCORD_TLA_ENGINE`). Both engines give
  the same result shape, so the callers did not change.
- Conformance: the checker runs the test models of TLC (from the TLC
  test suite, with the expected results of each Java test), the error
  modules of the tests of SANY, and the models of the TLA+ Examples
  repository (with the counts of their manifests). The models that it does not run are in a list, each with
  its reason (see `docs/tla-conformance.md`).

## Consequences

- No part of accord needs Java. TLC is necessary only for a comparison
  (`--engine tlc`, `mix accord.crosscheck --reference tlc`).
- The cache key of `mix accord.check` has the engine and a fingerprint
  of the checker modules, so a new build of the checker does not use the
  results of an old one.
- The native checker is slower than TLC: it is an interpreter on one
  process. The models of accord are small, so this is not a problem for
  `mix accord.check`. Some large Examples take minutes.
- When the checker and TLC give different results on a model, one of
  them has a defect. The conformance runs compare them on many models.
  A new difference is a bug in the native checker until the TLC source
  shows that TLC is wrong.
- Some TLC features are out of scope: checkpoints and recovery,
  distributed TLC, the debugger, and the trace exploration files
  (`_TTrace_`). The depth-first mode (`-dfid`) gives the results of TLC
  with a breadth-first search to the same depth. Results that depend on
  the interleaving of the threads of several workers can differ.
