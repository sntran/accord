# Native explorer and cross-check

Accord has two model checkers for the same finite model:

- **TLC** checks the generated TLA+ spec (`mix accord.check`). It needs
  Java and `tla2tools.jar`.
- **The native explorer** (`Accord.Explore`, `mix accord.explore`) runs
  the protocol functions directly. It needs only Elixir.

The **cross-check** (`Accord.CrossCheck`, `mix accord.crosscheck`) runs
both and compares the results. TLC is the reference. A difference shows
a defect in the explorer, or in the translation from the protocol to
TLA+. See ADR-012 for the decision.

## The native explorer

```elixir
result = Accord.Explore.run(MyApp.Protocol)
result.distinct                       # the number of distinct states
result.violations["TypeInvariant"]    # nil, or the first violation
```

The explorer builds an executable model from the IR and the model config
(`Accord.Explore.Model`). It calls the same guards, updates, and `where:`
constraints as the runtime monitor. It does not read the TLA+ spec.

The model uses the abstractions of the TLA+ model:

- Message arguments and reply values come from the model domains.
- A list in a reply is a list of placeholder values, with a length in
  `0..max_list_length`.
- A state timeout can fire at any time while its state is active.
- With `sessions: N`, the model has N sessions. A shared track has one
  value for all sessions.

Where the monitor and the spec are different, the model follows the
monitor. For example, a call reply goes to the first branch whose type
matches and whose `where:` holds.

The search is breadth-first, and it follows the rules of TLC:

- A state outside the state constraint is not explored and not counted.
  The explorer still checks the invariants on it.
- An action property is checked on every step that changes a track,
  also on a step into a state outside the constraint.
- A state is a deadlock only if it has no successor at all.
- For each check, the explorer keeps the first violation. This trace has
  the minimum length.

The explorer checks `TypeInvariant`, invariants, local invariants,
`forbidden`, `bounded`, unkeyed `correspondence`, `exclusive`,
`distinct`, action properties, and deadlock. It does not check liveness
yet.

### Options

| Option | Default | Effect |
|--------|---------|--------|
| `symmetry:` | `false` | Count two states that differ only in the order of the sessions as one. No traces. |
| `deadlock:` | `true` | Check for deadlock. |
| `stop:` | `:never` | `:first` stops at the first violation, as TLC does. |
| `max_states:` | `1_000_000` | Stop at this number of states. Then `complete` is false. |
| `collect_states:` | `false` | Put all states in the result. |
| `config:` | the protocol config | Use a different `%Accord.TLA.ModelConfig{}`. |

### Limits

- No liveness.
- Symmetry reduction only over sessions, not over model-value symmetry
  sets. The full model is still correct, but larger.
- A user `state_constraint` must be a conjunction of `track op integer`
  terms, for example `"pending =< 3 /\ count >= 0"`. Other constraints
  raise `Accord.Explore.Model.UnsupportedFailure`.
- A protocol function that raises an error stops the search, as an
  evaluation error stops TLC.

## The cross-check

```
mix accord.crosscheck                       # all protocols
mix accord.crosscheck MyApp.Protocol        # one protocol
mix accord.crosscheck --mutants 5           # and 5 mutants of each
mix accord.crosscheck --random 50 --seed 1  # 50 random protocols
mix accord.crosscheck --keep                # keep the TLC files
```

For each protocol, the cross-check compares:

1. **The state graph.** TLC dumps its graph (`-dump dot`). The states,
   the steps between them, the state count, and the search depth must be
   the same. Two models can have the same states but different steps,
   so the steps are compared too.
2. **The symmetry-reduced count**, for a model with two or more
   sessions.
3. **Each safety check.** TLC runs one time for each check, with only
   that check. The verdicts must be the same. When both find a
   violation:
   - both traces must have the same length (both searches are
     breadth-first, so both traces have the minimum length);
   - the explorer must replay the TLC trace, and its last step must
     violate the check;
   - TLC must replay the explorer trace (a replay module that `EXTENDS`
     the spec), and its last step must violate the check.

A model larger than `--max-states` is not complete. Then the cross-check
compares only the checks that the explorer finds violated, because TLC
stops at the first violation. The other comparisons are inconclusive.

Each result is one of:

- `✓` match
- `✗` mismatch — a defect in one of the two checkers or in the translation
- `?` inconclusive — for example, an infinite model or a TLC timeout
- `-` skipped — liveness, and checks that are runtime-only

### Mutants and random protocols

A protocol that passes in both checkers proves little. Two generators
make more test cases:

- `Accord.CrossCheck.Mutant` changes the IR of a protocol: it removes a
  guard, an update, a `where:`, or a transition, sends a branch to a
  different state, or reverses the branch order. Many mutants have
  violations and deadlocks, so their counterexamples are compared too.
- `Accord.CrossCheck.RandomProtocol` writes random protocol source from a
  seed: states, tracks, calls, casts, events, state timeouts, guards,
  updates, `where:` constraints, properties, and sometimes two sessions
  with shared tracks. The same seed gives the same source. It also uses
  the forms in the next section.

## Differences that the cross-check found, and their fixes

The first cross-check runs found five differences between the monitor
and the TLA+ spec. All five are now fixed in `Accord.Pass.TLA.BuildActions`
and `Accord.TLA.GuardCompiler`. Each has a probe protocol in
`test/support/probes/`, and `test/accord/cross_check_test.exs` checks that
its state graph is the same in the explorer and in TLC. The random
protocols also use all five forms.

### 1. An update read the wrong message argument (TLC could miss bugs)

```elixir
on {:put, a :: non_neg_integer(), b :: non_neg_integer()} do
  update fn {:put, _a, b}, _reply, tracks -> %{tracks | x: b} end
end
```

The spec had `x' = msg_a`. The translation dropped the underscore names
from the update head and then bound the other names by position, so `b`
got the position of `a`. The same occurred for event updates.

**Fix:** a name in a function head binds to the argument at its own
position. An ignored position binds nothing. This also applies to guard
heads and cast `where:` heads, so a head can use a name that is
different from the declared name. Probe:
`Accord.Test.Probe.UnderscoreArgs.Protocol`.

### 2. An update arm for a reply with two values was dropped (TLC could miss bugs)

```elixir
branch {:ok, a :: non_neg_integer(), b :: non_neg_integer()}, goto: :ready

update fn :get, reply, tracks ->
  case reply do
    {:ok, a, _b} -> %{tracks | x: a}
    _ -> tracks
  end
end
```

The spec had `UNCHANGED x` for both branches. The case-arm match knew
only two-element patterns (`{tag, value}`), so it fell to the `_` arm,
and an invariant over `x` held in TLC for no reason.

**Fix:** a reply pattern has one existential for each position that is
read, and the case-arm match compares the tag and the size. The arms are
tried in their order, as in Elixir. An arm that matches only some replies
of a branch (a literal against a general type, such as `{:ok, 0}` against
`{:ok, n :: integer()}`) cannot be selected statically, so it is an E042
error, not a guess. Probe: `Accord.Test.Probe.TripleReply.Protocol`.

### 3. Two call branches that accepted the same reply

```elixir
branch({:ok, n :: pos_integer()}, goto: :high, where: fn {:ok, n}, _ -> n > 1 end)
branch({:ok, n :: pos_integer()}, goto: :low)
```

The monitor gives `{:ok, 2}` to the first branch only. The spec made one
action for each branch, so `{:ok, 2}` could also go to `:low`. TLC then
explored steps that the monitor does not allow. This could give a false
counterexample, or hide a deadlock.

**Fix:** a branch action has a first-match precondition: for each
earlier branch that can accept the same reply, the reply fails that
branch's type or its `where:`. The action for `:low` has
`~((reply_n > 1))`. A branch after an equal branch without `where:`
never runs (`FALSE`). Probe: `Accord.Test.Probe.OverlapBranches.Protocol`.

### 4. Two cast branches whose `where:` predicates overlapped

The same as 3, for `cast` branches. **Fix:** a cast branch action has
the negation of each earlier `where:` as a precondition. Probe:
`Accord.Test.Probe.OverlapCast.Protocol`.

### 5. `div/2` and `rem/2` on negative numbers

Elixir rounds toward zero: `div(-1, 2) == 0` and `rem(-1, 2) == -1`. The
spec used `\div` and `%`, which round down: `-1 \div 2 = -1` and
`-1 % 2 = 1`. The two models had the same number of states but different
states.

**Fix:** the translation computes `\div` and `%` on the absolute values
and sets the sign as Elixir does. Probe:
`Accord.Test.Probe.DivRem.Protocol`.

### Three smaller defects

- Unary minus (`-x`, and a negative literal such as `-2` in an
  expression) had no translation. It was a loud E041 error. It now
  translates to `-(x)`.
- `Accord.TLA.TLCParser` read the first count line of TLC output. A long
  run prints progress lines with interim counts first, so `mix
  accord.check` could report too few states. It now reads the last line.
- An unknown `state` option, such as `state :waiting, state_timeout: ...`,
  was dropped with no message. It is now a compile error that tells you
  to use `state_timeout ms, goto: :state` in the state block.

## TLC notes

- TLC writes its standard modules (`TLC.tla`, `Integers.tla`) into
  `java.io.tmpdir`. Two TLC processes that share it can fail to parse.
  The cross-check gives each TLC run its own temporary directory.
- TLC reports an invariant that is a constant `FALSE` as an error, with
  no trace. The cross-check reads it as a violation of the initial state.
