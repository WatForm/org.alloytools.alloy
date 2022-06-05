# Changes Portus makes to the Alloy core

- Added the `ca.uwaterloo.watform.portus` package for the main Portus codebase.
- Added the `org.alloytools.fortress.core` bundle as a wrapper over Fortress.
- Added the `org.alloytools.fortress.core` bundle as a dependency of `org.alloytools.alloy.core`.
- Made the `ScopeComputer` class public so Portus's translation process can use it, and made it not final 
  so it can be mocked in unit tests. Also make `ScopeComputer.compute` public so we can use it.
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
- Extracted `SolutionInterface` interface from `A4Solution`, and use it instead of `A4Solution`
  outside the `edu.mit.csail.sdg.translator` package as much as possible, so that `FortressSolution`
  can implement it and allow the Alloy Analyzer to visualize Fortress solutions.
- Made `A4TupleSet`'s constructor public so that Portus can call it.
