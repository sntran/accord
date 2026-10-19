# Standard modules of SANY

These files are the standard modules of SANY, the parser of TLC, from
the directory `tlatools/org.lamport.tlatools/src/tla2sany/StandardModules`
of the repository `tlaplus/tlaplus` (MIT license, see `LICENSE`).

`Accord.TLA.Checker.StandardModules` reads them at compile time. The
semantic checks (`Accord.TLA.Checker.Semantic`) use them for the names,
the arities, and the levels of the operators of the standard modules.
The model checker does not evaluate these definitions: it has native
versions of the operators.
