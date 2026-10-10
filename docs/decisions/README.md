# Architectural decision records

This directory contains architectural decision records (ADRs) for the accord2 project. Each record captures a significant design decision, the context that led to it, and its consequences.

| ADR | Decision |
|-----|----------|
| [001](001-gen-statem-proxy.md) | The monitor is a gen_statem proxy process that intercepts messages between client and server, enabling blame assignment without modifying user code. |
| [002](002-ir-as-source-of-truth.md) | A single IR feeds both the runtime monitor and TLA+ verification pipelines, ensuring the model checks exactly what the monitor enforces. |
| [003](003-ternary-blame.md) | Blame is `:client`, `:server`, or `:property` because temporal property violations are not attributable to either party in a single interaction. |
| [004](004-closure-lifting.md) | DSL closures are lifted to named function captures because the compiler's temporary module does not exist at runtime, breaking `term_to_binary` serialization. |
| [005](005-tla-plus-verification.md) | TLA+ is used for model checking because it provides exhaustive state space exploration, temporal property checking, and an established formal methods ecosystem. |
| [006](006-pentiment-error-reporting.md) | Errors use pentiment for source-annotated diagnostics with labeled code spans, making violations actionable for both humans and tooling. |
| [007](007-strict-tla-compilation.md) | TLA+ spec generation failures abort compilation by default (`tla: :strict`); anything the model cannot express is a loud diagnostic, and stale specs are never verified. |
| [008](008-roles-events-direction-blame.md) | Protocols are two-party with direction-derived blame; the `event` primitive validates server pushes through the monitor and models them as TLA+ actions. |
| [009](009-multi-session-ghost-state.md) | Multi-session model checking with ghost shared state: `sessions: N` and `shared:` tracks are verified by TLC, not runtime-enforced; the asymmetry is declared loudly. |
| [010](010-trace-validation.md) | Runtime traces replay against the generated spec via TLC — the only check that can catch accord's own TLA+ compiler mistranslating the protocol. |
| [011](011-compat-checking.md) | Rolling-upgrade safety via static compatibility checking (`Accord.Compat`) against IR snapshots — the consumer shipped instead of a version macro. |
| [012](012-native-explorer-cross-check.md) | A native explorer runs the protocol functions on the finite model without TLC, and a cross-check compares it with TLC to find defects in either checker or in the TLA+ translation. |
