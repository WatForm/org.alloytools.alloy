# Changes Portus makes to the Alloy core

- Added the `ca.uwaterloo.watform.portus` package for the main Portus codebase.
- Added the `org.alloytools.fortress.core` bundle as a wrapper over Fortress.
- Added the `org.alloytools.fortress.core` bundle as a dependency of `org.alloytools.alloy.core`.
- Made the `ScopeComputer` class public so Portus's translation process can use it, and made it not final 
  so it can be mocked in unit tests.
- Added Mockito 4.3.1 as a test dependency, as well as its dependencies ByteBuddy and Objenesis.
- Made Expr's primary constructor protected so `ExprElementOf` can call it.
- Made `Type.make(Sig.PrimSig)` public, so our tests can call it.
