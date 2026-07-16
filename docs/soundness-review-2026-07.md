# Soundness review of the July 2026 redesign decisions

An adversarial audit of every semantic decision in the redesign, conducted 2026-07-02,
after the final tranche landed. Five review dimensions (TLA+ semantic core, runtime↔model
fidelity, compat + subtyping, trace-validation oracle, trust/workflow) were attacked
independently; every HIGH finding below was reproduced empirically — real TLC runs,
executable probes — not just argued statically. Probe scripts referenced here lived in
`/tmp` and are reproducible from the descriptions.

The framing question for each decision: *when the tool says ✓ (or "compatible", or
"replays"), is the claim true — and when it cannot be, is the asymmetry declared?*

> **Status (updated 2026-07-16):** fixes have begun landing in fix-order. **H5**
> (arity bypass) fixed in `dbcb551` — wrong-shape messages are now the `:malformed_message`
> violation, never forwarded. **C1** (update extractor) fixed in `86780ee` — non-reply case
> scrutinees and `when`-guarded arms are now E042, not silent mis-translations. The
> remaining findings below are open; each carries its own status note when resolved.

## Verdict summary

The redesign's *fail-closed instincts held*: caching, stale-spec lifecycle, trace-replay
membership, Terminating/deadlock, multi-session emission, symmetry suppression for `~>`
liveness, correspondence parity, and the compat direction discipline all survived attack,
most with empirical confirmation. The failures cluster in three places: **the update
extractor can silently mis-translate** (the exact class E042 exists to prevent), **TLC
warnings are swallowed** (liveness under state constraints, symmetry via `--extra`), and
**Compat reasons about types where the runtime resolves values in order**.

---

## Critical — false ✓ (tool claims verified; runtime violates)

### C1. Update extractor silently mis-extracts nested `case` and `when`-guarded arms — FIXED (`86780ee`)

`Accord.Pass.TLA.BuildActions.extract_update_body/3` ignores the case *scrutinee*
(`{:case, _, [_expr, [do: clauses]]}` — `_expr` is never checked against the reply
variable), and `resolve_case_for_branch/3` cannot see `when`-guarded arms (a
`{:when, ...}` node matches neither the tag-pattern check nor the wildcard check, so the
arm is skipped and a later arm or the wildcard is taken instead).

Two empirically confirmed shapes, both compiling without any diagnostic under
`tla: :strict`:

- **Nested case** — `case reply do {:ok, n} -> case n do 1 -> %{tracks | count: 0};
  _ -> %{tracks | count: count + 1} end ... end`: the inner case is resolved *as if it
  dispatched on the reply type*; no arm type-matches, the wildcard arm wins, and the
  emitted action is unconditionally `count' = count + 1`. The reset arm vanishes.
- **Guard clauses** — `{:ok, n} when n > 2 -> reset; {:ok, _} -> increment`: the
  `when`-arm is invisible; only the increment is emitted.

In both cases the model *has no transition* corresponding to real runtime behavior, so an
invariant such as "count never resets" gets a TLC ✓ the runtime violates. This is worse
than the `UNCHANGED`-vacuity E042 warns about — it is a *wrong* update, silently.
(`case` on the *message* is usually rejected only by luck: its arm patterns happen not to
type-match the reply; add a wildcard arm and it silently resolves for every branch.)

The sharpest witness — a **`forbidden` invariant that TLC proves and the runtime
violates** (verified end-to-end): reply type is the bare carrier `integer()`, and the
update is `case reply do n when n > 2 -> %{tracks | big: true}; _ -> tracks end` with
`forbidden fn tracks -> tracks.big end`. The `when`-arm that *sets* `big` is invisible to
`resolve_case_for_branch/3`, and the `_ -> tracks` identity arm wins, so the emitted
action drops `big` from its primed map entirely (`RollFromSToS` primes only `state`). The
model never assigns `big`, `~(big)` holds vacuously, TLC ✓. At runtime, server reply `3`
sets `big = true` and `never_big` fires `:invariant_violated`. Same root cause as the
`when`-arm hole above, in the *setter*-dropped direction — and it shows the false ✓ reaches
`forbidden`, not just `invariant`.

**Fix:** `extract_update_body` must verify the case scrutinee is the reply variable
(anything else → E042); `resolve_case_for_branch` must treat `when`-guarded arms as
untranslatable (E042) rather than skipping them; add regression fixtures for both shapes.
Trace validation would catch these only when a sampled trace exercises the dropped arm —
`mix accord.check` alone prints the false ✓.

### C2. Liveness verified under a state constraint — TLC's own "dangerous" warning is swallowed

Correspondence checks emit `CONSTRAINT StateConstraint` (the counter bound); nothing
prevents or flags co-occurrence with a `liveness` property. TLC prints
*"Declaring state or action constraints during liveness checking is dangerous: Please
read section 14.3.5 … of Specifying Systems"* — and `TLCParser`/`mix accord.check` have
no warning handling at all, so the user sees an unqualified ✓.

Empirically constructed false ✓: a protocol whose open/open/… loop violates
`in_state(:a) ~> in_state(:done)` under its own fairness checks green, because every
violating lasso climbs `open_pending` past the *builtin* `correspondence_counter: -1..3`
bound and the truncated graph contains no violating cycle. The **flagship job_queue
example is affected**: its cfg carries both `CONSTRAINT StateConstraint` and
`PROPERTY WorkerFinishes`, and TLC prints the danger warning on every run. (Its ✓ happens
to be correct — the counter never exceeds 1 in a single session — but the tool cannot
know that, and says nothing.)

**Fix (layered):** surface TLC warnings in check output; emit a W-code when a temporal
property co-occurs with any `CONSTRAINT`; document that a liveness ✓ under a constraint
covers only behaviors confined to the bound (a materially weaker claim than the safety
analogue).

### C3. `Compat.check` reply matching ignores the old client's first-match rule and all track evolution

Two independent holes, each yielding `compatible?: true` with zero errors for protocols
where deployed old clients desync and then eat *client*-blamed violations:

- **Order/value-blindness** (`check_replies/6`): each new branch is matched to the first
  old branch whose *whole type* is a supertype. The runtime resolves *values* in
  declaration order. With legal overlapping branches (specific-before-general is the
  documented fall-through idiom; E020 only forbids duplicate message tags), a new branch
  contained in a *later* old branch passes even though some of its values first-match an
  *earlier* old branch with a different target. Even a pure branch *reorder* — same
  branch set — checks clean while flipping the resolution of overlapping values.
- **Update-function invisibility**: `IR.Transition.update` is compared nowhere. Branch
  resolution is conditioned on tracks via `where:`, and tracks evolve only via updates —
  the DistributedQueue fencing idiom with the update's `fence: token` write removed
  checks fully clean while old and new sessions diverge on the second checkout.

**Fix:** branch matching must be order- and overlap-aware (for each new branch, every
earlier old branch not provably disjoint from it must share its target — this needs a
conservative `disjoint?/2` companion to `subtype?/2`); update-AST changes (and track
default changes) should at minimum get the C010 advisory treatment. Until then, ADR-011's
"a clean result is trustworthy" holds only for protocols with non-overlapping,
constraint-free branches.

---

## High — silent wrong-✓ or unsound as declared

### H1. `Files.tla_module_name/1` collides on module-path boundaries

`Module.split |> Enum.join` maps `A.BC` and `AB.C` to the same `ABC` (verified), so both
share one spec file and one cache entry; each is ✓-reported against whichever compiled
last. Case-insensitive filesystems (macOS default) add a `Foo.BAR`/`Foo.Bar` variant.
Directly falsifies ADR-007's "every listed protocol was verified against a spec generated
from its current source." **Fix:** an unambiguous join (escape + separator, or a short
hash suffix) plus a collision assertion at compile or check time.

### H2. `--extra` cfg merging reintroduces SYMMETRY (and CONSTRAINT) under user liveness

`merged_extra_cfg` inherits the generated cfg's `SYMMETRY`/`CONSTRAINT` lines into a
user-authored module's cfg without scanning the user's TLA+ for temporal operators — the
exact combination `Emit.active_symmetry/2` suppresses for generated specs. TLC warns
("might cause TLC to miss violations") and proceeds; accord prints ✓. **Fix:** scan the
extra module (or its properties) before inheriting; surface TLC warnings (same plumbing
as C2).

### H3. Per-property fairness assumptions pool into one global `FairSpec`

`assuming:` is documented per-property, but all properties share one
`SPECIFICATION FairSpec` containing the *union* of every property's fairness conjuncts —
plus blanket `WF_vars(Next)` if any sibling lacks `assuming:`. Each liveness property is
therefore checked under assumptions it did not declare and can ✓ on a sibling's fairness.
**Fix:** encode per-property fairness as an implication in the property itself
(`PROPERTY (WF_vars(A) /\ …) => (P ~> Q)`) instead of strengthening the spec.

### H4. Atom rendering is incoherent across emission sites (loud, but late and misleading)

Three renderings of the same atom in one pipeline: guard literals go through `inspect/1`
(`:fast` — a SANY parse error at check time, violating ADR-007's compile-time-diagnostic
contract); atom track *defaults* render as strings (`"slow"`); atom track *domains* as
model values (`{mv1, mv2, mv3}`). Any atom-typed track with a non-nil default yields a
spurious TypeInvariant counterexample on a *correct* protocol; any atom literal in a
guard yields a raw parser stack trace. Unexercised by the entire suite only because every
fixture uses nil defaults and never compares atoms in guards.

**Coupling warning:** today the DSL's inability to express atom comparisons *accidentally
protects* symmetry soundness (asymmetric formulas mentioning symmetry-set model values
cannot be written). Whichever consistent rendering is chosen must land together with a
validation pass that symmetry-set values do not appear asymmetrically in formulas — and
note the raw-string `state_constraint` and `--extra` surfaces can already express such
formulas today (H2).

### H5. Arity-mismatch client messages bypass validation and reach the server unblamed — FIXED (`dbcb551`)

`Monitor.check_message_types/4` (`monitor.ex:534-535`) returns `:ok` — accept — whenever
`length(args) != length(types)`. A message whose tag matches a transition but whose tuple
arity does not is therefore forwarded to the upstream server **with no type check and no
`:client` blame**. Verified end-to-end: against `on {:put, n :: integer()}`, the call
`{:put, :not_an_int, :extra, :more}` returns the server's normal reply, the server
receives the malformed term, and `ViolationCollector` drains *zero* violations. Catching
malformed client messages and assigning blame is the monitor's entire job, so this is a
runtime-enforcement hole, not a modeling asymmetry: the contract's "malformed client
message ⇒ `:client` blame" guarantee is silently false for any wrong-arity message.
(`{:put, :nan}` — correct arity, wrong element type — is still correctly blamed; only
arity mismatch escapes.) The comment-free `:ok` branch reads as "not this transition", but
there is no other transition to fall to, so accept is the wrong default. **Fix:** an arity
mismatch on a tag-matched transition is an `invalid_message` (or dedicated arity)
violation with `:client` blame; add a regression fixture. This is a monitor bug
independent of the TLA+ pipeline — worth fixing before the criticals since it is one line
and directly weakens deployed runtime guarantees.

---

## Medium

- **M1. Trace oracle scope is narrower than ADR-010 claims.** Replay is one-directional
  (only *stricter*-than-runtime translations can diverge; a **dropped guard** never
  rejects a trace — ADR-010:39-40 is false as worded); the replay cfg keeps only
  `SPECIFICATION` + `CONSTANT`s, so property/invariant/correspondence translation is
  entirely un-oracled (dropping `CONSTRAINT` is *necessary and correct*, but unstated);
  messages, replies, and action identity are unpinned (three garbage-message steps
  replayed fine in probing — same-effect actions mask each other's guard bugs). Honest
  claim: *a coverage-dependent conformance oracle for `BuildActions`' strict direction.*
- **M2. Heterogeneous term-typed slots.** `validate_terms` accepts an integer in a
  `term()` slot; the derived `term` domain is observed-atoms-only; TLC throws a
  RuntimeException that `TraceCheck` renders as message-less "failed with error"
  (`{:ok, spec} =` also crashes with a bare MatchError on `{:error, {:unsupported_term,
  _}}`). Should be an explicit `validate_terms` rejection, like pids.
- **M3. `Type.Check` literal clause uses `==`.** `check(3.0, {:literal, 3}) = :ok` while
  `subtype?({:literal, 3}, :integer)` holds and `check(3.0, :integer)` fails — the
  property-tested soundness law is violated with witness `3.0`. Fix: `===`. Related:
  improper lists (`[1 | 2]`) crash `check_list/3` with FunctionClauseError in the
  monitor's reply path — a crash where a blamed violation belongs.
- **M4. `div`/`rem` render as `\div`/`%`,** which differ from Erlang semantics on
  negative operands (truncation/dividend-sign vs floor/non-negative) — silent
  wrong-verdict potential; the builtin `integer` domain includes negatives. Restrict to
  provably non-negative operands or reject (E041).
- **M5. Compat gaps (all verified):** event *removal* is unflagged (old clients driven by
  the push hang — flag or document as out of scope); `check_events` skips old-terminal
  states entirely (new server pushes into a session old clients consider over);
  C009 exempts duration-only timeout changes while the docs say "must not change the
  session's autonomous movement"; C010 fires spuriously on branch-count changes
  (positional zip of constraint lists) — misleading text, and accidentally load-bearing
  as the only signal for branch-structure changes.
- **M6. Snapshot versions the container, not the schema.** The magic string is checked
  but `%IR{} = binary_to_term(...)` matches any map tagged `Accord.IR`; nested structs
  are never validated. Schema drift produces a blend of KeyError crashes and *silent*
  wrong verdicts (catch-all readers like `timeout_target/1` treat missing fields as
  absent features). Fix: embed and check an IR schema version.
- **M7. Event-only states are model-deadlock-free under an undeclared cooperative-server
  assumption.** A state whose only exits are server pushes never deadlocks in the model
  but can strand a real session forever. Needs a runtime-vs-TLC table row and/or a
  W-warning. (The README's "a reported deadlock is a real stuck state" stays true — the
  gap is the unreported direction.)
- **M8. Process gaps:** CI runs `mix test --only tlc` but never `mix accord.check`
  (workflow surface — discovery, cache, `--extra`, exit codes — has zero CI coverage);
  the `subtype?/2` "property test" is a fixed whitelist of six pairs with canonical-value
  generators (no floats, binaries, improper lists, unions, or random type pairs — none of
  M3's witnesses are generatable), overstating ADR-011's "property-tested" claim.
- **M9. Action properties ignore the model's stuttering exemption — conforming servers
  get blamed** (verified). `build_property` for `:action` emits `[][pred]_<<tracks>>`,
  whose `_<<tracks>>` subscript exempts steps that leave all tracks unchanged; the monitor
  (`check_single` for `:action`) applies `pred` to *every* transition. So a pure-query
  transition that changes no track — e.g. a `:peek` under `action fn o, n -> n.level >
  o.level end` — is a legal stutter in the model (TLC ✓) but fires `:action_violated`
  (`:property` blame) at runtime. Runtime is *stricter* than the model: it blames a server
  the spec certifies. This bites any protocol pairing an action property with query-like
  transitions (the payment example's money-monotonicity is the shape at risk). **Fix:** the
  monitor's action check must exempt transitions that leave the property's tracked vars
  unchanged, mirroring `_<<vars>>`; or the emission must drop the subscript to match the
  runtime (choose one semantics and pin it both directions with a fixture).

## Low

- Exit-code conflation: crash and finding both exit 1 in `accord.check --strict` and
  `accord.compat` (fail-closed, but CI can't distinguish; use a distinct code for
  operational errors).
- `--snapshot` silently overwrites an existing snapshot (the released contract) — no
  `--force`, no prompt.
- `discover_protocols` rescues all exceptions to `[]` → a discovery crash becomes a
  vacuous exit-0 "No Accord protocols found."
- `--extra` writes into `_build/accord/` unguarded (can clobber a generated spec until
  next recompile) and TLC resolves EXTENDS against stale artifacts of deleted protocols.
- Exerciser gate race: `ViolationCollector.property_violations()` drains *before* the
  monitor stops; a straggler state-timeout's property violation is missed while its trace
  event is sampled (no false replay result; gate airtightness only).
- Hand-built trace hazards: `Terminating` accepts fabricated terminal self-loop records;
  `prev_state`/`seq` are never cross-validated; `Trace[1]` is synthesized from the IR, so
  corruption of a trace's first record is undetectable. Real monitor traces immune.
- Track names `s`/`si`/`sj` collide with session/quantifier binders at `sessions ≥ 2` —
  loud SANY "Multiply-defined symbol", but should be an E-code at compile.
- Order comparisons on nil-able tracks emit TLA that fails loudly at TLC eval
  (`NULL` vs integer) — correct outcome, wrong layer.
- `distinct …, empty: nil` on a spec with no nil tracks would reference an undeclared
  `NULL` (loud SANY error).
- `assuming:` fairness nuance: the tag's WF lands on *every branch action* of that tag —
  i.e. "the server eventually returns each declared reply", an assumption the runtime
  cannot enforce (documented at docstring level; keep it in mind when reading ✓s).

## Verified sound under attack (empirical unless noted)

- **Terminating**: `\A`-quantified at sessions:N with `UNCHANGED vars` over *all*
  variables; one terminal + one stuck session correctly deadlocks; guard-exhaustion
  deadlock detection is real.
- **SYMMETRY suppression** for `~>` liveness covers both user sets and auto
  `Permutations(Sessions)`, definition and cfg from one function; `[][A]_v` action
  properties under SYMMETRY are checked during exploration and violations are caught
  (differential probe) — sound for the always-symmetric formulas the DSL can express.
- **Multi-session fairness** is conservative: `WF(\E s : A(s))` is weaker than
  per-session WF, and TLC finds the starvation lasso rather than masking it (probed both
  directions).
- **Sessioned emission**: TypeInvariant/Init function-typing, EXCEPT updates, `\A s`
  properties, `exclusive` and `distinct` formulas (empty-exempt, both orders), W003
  covering shared tracks + both check kinds, sessions:1 byte-identity.
- **Correspondence parity**: identical open/close-on-state-change rule in both pipelines;
  keyed correspondence is W004 runtime-only; monitor's stray-close reset reports once.
- **CheckCache**: fail-closed everywhere — parser accepts only the exact success line;
  killed/garbage/OOM runs are never cached; extras are never cached; deadlock flag and
  jar identity are in the key; corrupt cache degrades to re-verification.
- **Stale-spec lifecycle**: discovery enumerates compiled beams (deleted protocols'
  stale specs are ignored, not ✓-reported); `:warn` deletes stale artifacts and bakes the
  failure into `__tla_status__/0`; `@external_resource` registered even for
  not-yet-existing model files.
- **const**: expansion-time registration; every unsupported context fails at compile
  (nothing escapes into lifted closures); literals enforced.
- **Trace replay membership direction**: no mid-trace stutter (`ti' = ti + 1` forced),
  completion self-loop gated on `ti = Len`, all pins conjoined per step, deadlock-on,
  divergence index semantics verified against pinned tests.
- **Trace capture discipline**: events only on applied transitions (every rejection path
  audited); the property-violation gate keeps violating runs out of the sample; exerciser
  ETS/stop-order/record-on-success-only all hold.
- **Subtyping vs the actual runtime check**: string↔binary (both `is_binary`), sign-aware
  literals, integer chain, tuple/tagged/union rules, false-leaning catch-all — sound
  except M3.
- **Compat direction discipline**: `--against` = `check(snapshot, module)`; positional
  `Old New`; the dual direction pinned as a different question; anystate folding; cast
  handling; C009 add/remove/retarget.
- **NULL/boolean rendering**: `CONSTANT NULL` declared when needed; nil-able domains get
  `\union {NULL}`; equality semantics match runtime; booleans `BOOLEAN`/`TRUE`/`FALSE`
  end-to-end.

## What this does to the headline claims

| Claim | Status after audit |
|---|---|
| ADR-002/007 "TLC checks what the monitor enforces; infidelity is loud" | Broken by C1 (silent mis-extraction), H4 (loud-but-late atoms), M4 (`div`/`rem`); otherwise held |
| ADR-008/009 multi-session + ghost-state honesty | Held (empirically); add M7's event-only-state row |
| ADR-010 "trace validation is a conformance oracle for the compiler" | Overclaimed — narrow to *strict-direction action-translation oracle* (M1, M2) |
| ADR-011 "a clean compat result is trustworthy" | Broken by C3 until branch matching is value-aware and updates are at least advisory |
| "✓ is never stale, never vacuous" (check workflow) | Held except H1 (name collision) and the swallowed-TLC-warning channel (C2/H2) |
| ADR-003 "malformed messages ⇒ correct runtime blame" | Broken by H5 (wrong-arity messages forwarded unblamed) and M9 (conforming servers blamed for stutters) |

## Recommended fix order

1. **H5** — one-line monitor fix (arity mismatch ⇒ `:client` blame, not accept); directly
   restores a deployed runtime guarantee. Do first: smallest, highest deployed impact.
2. **C1** — extractor scrutinee + `when` handling (small, surgical, removes the worst
   false-✓ class) with regression fixtures.
3. **C2 + H2 shared plumbing** — surface TLC warnings in `TLCParser`; W-code for
   `CONSTRAINT`+temporal and for `--extra` SYMMETRY/CONSTRAINT inheritance.
4. **H1** — module-name disambiguation + collision assertion.
5. **C3** — `disjoint?/2`, order-aware reply matching, update-change advisory; demote
   ADR-011's claim until landed.
6. **H4** — one consistent atom rendering (+ symmetry-usage validation, per the coupling
   note) and E044 coverage for model-value domains.
7. **H3** — fairness-as-implication encoding.
8. **M9** — action-property stuttering exemption (pin both directions with a fixture).
9. The remaining mediums, then the lows, mostly docs/diagnostics.
