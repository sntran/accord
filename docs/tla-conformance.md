# Conformance of the native TLA+ checker

`Accord.TLA.Checker` must give the same results as TLC and its parser,
SANY. This document tells how we test this, gives the results, and lists
each test that we do not run, with the reason.

## How we test

We use four sets of tests with known results.

1. **The test suite of TLC.** The TLC repository (`tlaplus/tlaplus`,
   directory `tlatools/org.lamport.tlatools`) has Java tests in `test/`
   for the models in `test-model/`. Each test gives the model, the
   arguments of TLC, the expected exit status, and usually the expected
   counts of states (`TLC_STATS`: generated, distinct, left on the
   queue). A script reads the Java tests, runs the native checker on each
   model with the same arguments, and compares:

   - the exit status (for example `VIOLATION_SAFETY`,
     `FAILURE_SPEC_EVAL`, or `ERROR_SPEC_PARSE`),
   - the counts of generated and distinct states, when the test gives
     them,
   - the number of initial states, when the test gives it, and
   - the values of the first state of the error trace, when the test
     gives them (`RandomSubsetATest`, `RandomSubsetBTest`).

   The script also reads the subclasses of the base test cases of TLC
   (for example `SuiteTestCase`, `SuiteETestCase`,
   `AbstractCoverageTest`, `AbstractExampleTestCase`), and gives each
   subclass the model and the arguments that its base class gives.

   The script gives the checker the options that the test harness of TLC
   gives to TLC: `-seed 1` (or the seed of the test), `-fp 0`,
   `-coverage 1` (unless the test turns it off), the number of workers of
   the test, and the system properties that the test sets.

2. **The tests of SANY.** The same repository has two sets of modules
   for the semantic checks of SANY (directory
   `test/tla2sany/semantic`):

   - `error_corpus`: each module has one error or warning, and its file
     name gives the code (for example `E4205_Test.tla` or
     `W4801_Test.tla`). The test passes when the checker gives that
     code: an error for an `E` module, a warning and no error for a `W`
     module (as `SemanticErrorCorpusTests.java`).
   - `corpus`: modules without errors.

   We also ported the cases of `TestLevelChecking.java` and
   `TestSubexpressionSelectors.java` to ExUnit
   (`test/accord/tla/checker/semantic_test.exs`).

3. **SANY on all the modules.** We run SANY and the semantic checks of
   the checker on each `.tla` file of `test-model/` (TLC) and of
   `specifications/` (TLA+ Examples): 1081 files. For each file, the two
   tools must agree: both find an error, or both find no error.

4. **The TLA+ Examples repository.** The repository
   (`tlaplus/Examples`) has a `manifest.json` for each specification,
   with the expected result and the counts of states of each model. The
   script runs each model in exhaustive-search mode that TLC checks in
   30 seconds or less, and compares the result and the counts.

We also use TLC as an oracle for single questions: when a result is not
clear, we run TLC on the same model and compare the output.

## Results

### TLC test suite

The TLC repository has 669 Java test files. 35 of them test parts of
TLC that have no model (for example its parser of arguments or its value
classes). The other files, with the subclasses of the base test cases,
give 634 tests with a model. The script runs 541 of them and does not
run 93 (see below).

| Result | Tests |
|---|---|
| Same exit status and same counts of states as TLC | 540 |
| Different | 1 |

The tests that pass include the tests that expect an error of SANY
(`ERROR_SPEC_PARSE`), for example `ETest1`, `ETest2`, `ETest5`,
`ETest16`, `Test210`, and `Test212` to `Test217`. The checker finds
these errors with its port of the semantic checks of SANY (see below).

The test that fails is `Github971cTest`. It runs TLC with two workers
and a state queue that stops one worker until the other worker is
ahead, to make one interleaving of the threads. Its expected counts
(13 states generated) come from that interleaving. The checker has one
process and gives 10 states generated, which is the result of TLC with
one worker (we ran TLC to make sure).

The runs that pass include the modes and options of TLC that the tests
use: random simulation (`-simulate`, also with the experimental liveness
check of the simulator), `-continue`, `-dfid` (as a breadth-first search
to the same depth), `-workers` (for the registers of `TLCSet`),
`-coverage` (for `TLCGet("spec")`), time-bound checking
(`-Dtlc2.TLC.stopAfter`), and the liveness checks that TLC does during
the search (the side effects of `TLCSet` and `Print` in fairness
conditions occur in the same order and the same number of times).

### SANY tests

| Set | Result |
|---|---|
| `error_corpus` (114 errors, 7 warnings) | 121 of 121 give the expected code |
| `corpus` | 27 of 28 have no errors |
| `TestLevelChecking` (51 cases) | 51 of 51 |
| `TestSubexpressionSelectors` (3 cases) | 3 of 3 (same code, message, and position) |

The module of `corpus` that has an error is `NegativeOpTest.tla`. It
defines the operator `-.` two times. The test of SANY does not run this
module (`Assume.assumeFalse` in `SemanticCorpusTests.java`), and SANY
also reports this error. The test of SANY also checks that each name of
the modules of `corpus` refers to the definition that a `RefersTo`
comment gives; we do not check these references.

The other Java tests of `tla2sany` (for example `TestErrors.java`,
`TestContext.java`, `IncrementalSemanticParseTests.java`) test the Java
classes of SANY, not a module. We do not port them.

### SANY on all the modules

On the 1081 files, the checker and SANY agree on 1078. On the other 3
files:

- `sany/NestedModuleLetInstance.tla`: SANY reports that the module
  `LetInner` has two definitions, and the checker accepts the file. The
  test of SANY for this file (`NestedModuleInstanceTest`) says that this
  report is a bug of SANY, and has `@Ignore`. The checker gives the
  result that the test expects.
- `suite/test36.tla` and `BagsTest.tla`: SANY reports errors only when
  its library path (`-DTLA-Library`) has the directory of TLAPS, which
  has a different `Bags` module. With the standard modules, SANY and the
  checker accept the two files.

The checks of SANY that the checker has:

- names: unknown operators and modules, names defined two times,
  built-in names, numbers of arguments, operator arguments, `LAMBDA`,
  `@`, record fields, `EXTENDS` and `INSTANCE` (substitutions, conflicts
  of names), `RECURSIVE` (errors 4200 to 4294);
- levels: the port of the level checker of SANY (`LevelNode.java` and
  the `levelCheck` methods), with the levels of the arguments of the
  built-in operators, Leibniz checks of substitutions, operator
  arguments of operator arguments, recursive operators, and the checks
  of temporal formulas (errors 4205, 4206, 4244 to 4247, 4272, 4273,
  4290, 4310 to 4315);
- labels, subexpression names, and proofs (errors 4330 to 4357);
- warnings: conflicts of names from `EXTENDS` and `INSTANCE` (4800,
  4801), record fields with the name of a definition (4802), and the
  checksums of PlusCal translations (4803 to 4805).

The checksum of a PlusCal algorithm is the CRC32 of the syntax tree that
the PlusCal translator makes. The checker has no PlusCal translator.
Thus it finds a changed algorithm only when the recorded checksum is not
a possible CRC32 text (lowercase hexadecimal, no leading zero, at most
8 digits). The checksum of the translation is exact.

When the semantic checks find an error, the checker stops with the
status `ERROR_SPEC_PARSE` and a report in the form of SANY, as TLC does.

### TLA+ Examples

The script selects 140 models: the models in exhaustive-search mode
that the manifests give a run time of 30 seconds or less for (with TLC).

| Result | Models |
|---|---|
| Same result and same counts of states as the manifest, in 120 seconds or less | 125 |
| Same result and same counts of states, in more than 120 seconds (up to 25 minutes) | 7 |
| Not finished (time or memory limit) | 8 |
| Different | 0 |

The 7 slow models are `MCCRDT`, `BufferedRandomAccessFile`,
`MCCheckpointCoordinationFailure`, `MCDisruptor_MPMC`, `MCbtree`,
`FastPaxos`, and `EWD998PCal`. The 8 models that do not finish are
`GameOfLife`, `MCQuicksort`, and `TLCSailfish1` (not finished in 25
minutes), and `MCBakery`,
`MultiPaxos_MC_small`, `MCLamportMutex`, `CoffeeCan1000Beans`, and
`MCNanoMedium` (more than 3 GB of memory). The checker keeps each state
as an Elixir term, which takes more memory than the fingerprints and
the compact states of TLC.

## Tests that the script does not run

Each of these tests checks a part of TLC that is not model checking of a
model, or a mode that the checker does not have.

| Reason | Tests |
|---|---|
| The test checks the trace exploration spec (`_TTrace_` files) that TLC writes after a violation. The checker does not write these files. | 19 tests whose name ends in `_TTraceTest`, and their base class `TTraceModelCheckerTestCase` |
| The test has `@Ignore` in TLC: it is known to fail or to be too slow for TLC itself. | ActionCompositionDistributiveATest, ActionCompositionDistributiveBTest, April20aTest, April20bTest, April21Test, April22Test, April25Test, April29Test, April29dTest, ChooseTableauSymmetryTest, Github1198eTest, Github1198gTest, Github297Test, Github607Test, May09Test, May09dTest, NQTest, NQaTest, OneBitMutexTest, SymmetryModelCheckerTest3, SymmetryModelCheckerTest3a, SymmetryModelCheckerTestLong, SymmetryModelCheckerTestLonga, SymmetryTableauModelCheckerTest, TLCGetNonDeterminismTest, TableauSymmetryTest, Test61, UnicodeFunctionFingerprintTest, UnicodeRecordFingerprintTest, UnicodeStringDiskStateQueueTest, UnicodeStringFingerprintTest |
| The build of TLC does not run the test (`customBuild.xml` excludes it). Three of these test Java module overrides (`UserModuleOverride*`); the others are slow PlusCal tests or tests of a mode. | BidirectionalTransitions1BTest, BidirectionalTransitions2CTest, DetlefsTest, InitEvalOrderTest, MacroQuicksortTest, MacroRealQuicksortTest, PcalPaxosTest, SimpleMultiProcTest, StackTestTest, StarkMutexTest, TestPCandStackTest, UserModuleOverrideAnnotationTest, UserModuleOverrideFromJarTest, UserModuleOverrideTest |
| The class is a base class of other tests. The build of TLC runs only its subclasses, and the script runs them too. | AbstractCoverageTest, SuiteETestCase, SuiteTestCase |
| The class is not a test (a base class or a helper). Its subclasses run. | AbstractExampleTestCase, AssertExpressionStack, DepthFirstTerminate, DistributedTrace, LivenessConstraintWarning, LivenessSymmetryWarning, RandomSubset |
| The test runs the debugger of TLC (the Debug Adapter Protocol). | Debug02Test, Debug03SimTest, Debug03Test, Debug04SimTest, Debug05SimTest, EWD840DebuggerSimTest, EWD840DebuggerTest, EWD840ErrorActionDebuggerTest, EWD840ErrorDebuggerTest, EWD998ChanDebuggerTest, EWD998TraceDebuggerTest, EchoDebuggerTest, ExpressionBreakpointTest |
| The test runs distributed TLC (a TLC server and remote workers). | DistributedDoInitFunctorEvalExceptionTest, DistributedDoInitFunctorInvariantContinueTest, DistributedDoInitFunctorInvariantTest |
| The test calls Java methods of TLC values directly. | EvaluatingValueTest |
| The test recovers a checkpoint that TLC wrote (`-recover`). The checker does not read the checkpoint files of TLC. | CodePlexBug08EWD840FL2FromCheckpointTest |

## Known differences

These differences do not change a verdict or a count of states in the
tests above. They can change the text of the output.

- **The order of variables in a trace.** TLC prints the variables of a
  state in the order of the symbol table of its parser (a hash table).
  The checker prints them in the order of their declaration. The order
  also goes into the fingerprint of a state, which seeds the random
  values of the next-state relation (`RandomElement`, `RandomSubset`):
  with more than one variable, these values can be different from TLC.
- **The order of strings.** TLC orders strings and model values by the
  order in which it first makes them. The checker gives the same order
  for the strings of the config and of the modules. TLC also makes some
  strings when it starts (for example the names of the fields of
  `TLCGet` records); the checker does not know this order.
- **Several workers.** The checker has one process. The option
  `:workers` gives each worker its own registers (`TLCSet`, `TLCGet`),
  and the workers take the states in turn. A result that depends on the
  interleaving of the threads of TLC can be different.
- **Positions of errors.** The semantic checks give the line and the
  column of the start of the name or the expression with the error, or
  no position. SANY also gives the end of the range.
- **Speed.** The checker is an interpreter on one process. It is slower
  than TLC, by a factor of about 5 to 50.
