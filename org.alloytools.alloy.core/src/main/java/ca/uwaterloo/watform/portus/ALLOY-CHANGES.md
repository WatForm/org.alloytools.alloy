# Changes Portus makes to the Alloy core

- Added the `ca.uwaterloo.watform.portus` package for the main Portus codebase.
- Added the `org.alloytools.fortress.core` bundle as a wrapper over Fortress.
- Added the `org.alloytools.fortress.core` bundle as a dependency of `org.alloytools.alloy.core`.
- Included `org.alloytools.fortress.core` in the `org.alloytools.alloy.dist` JAR.
- Made the `ScopeComputer` class public so Portus's translation process can use it, and made it not final 
  so it can be mocked in unit tests. Also make `ScopeComputer.compute` public so we can use it.
- Added public `getBitwidth` and `getMaxSeq` methods in `ScopeComputer`, because the information is
  accessible from `sig2scope(SIGINT)` anyways and we need the bitwidth and max sequence length directly.
- Added Mockito 4.3.1 as a test dependency, as well as its dependencies ByteBuddy and Objenesis.
- Made Expr's primary constructor protected so `ExprElementOf` can call it.
- Made `Type.make(Sig.PrimSig)` public, so our tests can call it.
- Added a `CommandRunner` interface that abstracts "something that can run an Alloy command",
  and added an adapter class `TranslateAlloyToKodkod.Runner` which adapts `TranslateAlloyToKodkod`
  to that interface.
- Made `A4Options.SatSolver` not final and added a `commandRunner()` method that returns the
  `CommandRunner` to use when running commands with the `SatSolver`. Added a subclass
  `FortressOptions.FortressSmtSolver` that uses `TranslateAlloyToFortress` instead and added
  static `SatSolver` constants for it.
- Added a `FortressOptions` field to `A4Options`.
- Extracted `AlloySolution` interface from `A4Solution`, and used it instead of `A4Solution`
  outside the `edu.mit.csail.sdg.translator` package as much as possible, so that `FortressSolution`
  can implement it and allow the Alloy Analyzer to visualize Fortress solutions.
- Also used `AlloySolution` in `A4SolutionWriter`, `A4Tuple`, and `A4TupleSet` to make them
  generic between Fortress and Kodkod solutions. Made `A4Solution`'s `atom2name` and `atom2sig`
  methods public so they can be added to `AlloySolution`.
- Made `A4TupleSet`'s constructor public so that Portus can call it.
- Small modifications in `SimpleCLI` to support dumping SMTLIB from the command line.
- Added `keySet()` in `Env` so that `VarMappingContext` doesn't have to keep track of it itself.
- Made `Err`'s constructor public so that `ErrorNoPortusSupport` can be defined in the Portus package.
- Added condition in `SimpleReporter.SimpleTask2.run` exempting Portus solutions from a Kodkod-specific bugfix
  related to getting the next interpretation.
- Made some changes in `A4Solution` (adding `evalModel`, `getFullFormula`) and `TranslateAlloyToKodkod`
  (adding `model2kodkod` and associated constructor) to enable extracting the full formula of the model which
  is sent to Kodkod for correctness testing purposes. Made `A4Solution`'s constructor, `addSig`, `addField`,
  `addRel`, `solve` public (removed unnecessary `throws IOException` on `solve`), added `getUniverse`
  for the same reason.
