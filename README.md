# Mark Jones' Typing Haskell in Haskell

Based on the Nov 23, 2000 version from [https://web.cecs.pdx.edu/~mpj/thih/](https://web.cecs.pdx.edu/~mpj/thih/).

Modified to build with Haskell 2010 and to use stack.

- fixed imports
- changed `TIMonad` to be a `State` monad.
- moved test code to `tests` directory (currently not running, though)


----------------------------------------------------------------------------

                  Typing Haskell in Haskell: README

                           Mark P Jones
                          mpj@cse.ogi.edu

                 Pacific Software Research Center
           Department of Computer Science and Engineering
        Oregon Graduate Insitute of Science and Technology

             Thanksgiving Day 2000 (November 23, 2000)

This package contains source code for a Haskell typechecker that is
written in Haskell.  This is a revised version of the program that was
presented at the 3rd Haskell Workshop in Paris on October 1, 1999.
These files have been tested using the Hugs 98 interpreter, but should
be readily adapted to other Haskell 98 systems.  These programs are
distributed as Free Software under the terms in the file "License" that
is included in the distribution of this software, copies of which may
be obtained from: http://www.cse.ogi.edu/~mpj/thih/.

Please note that further revisions to this software may already be
planned or in progress.

The following list describes each of the files in the distribution:


  Readme
    This file
  License
    The license for distribution and use of this software

  TypingHaskellInHaskell.hs
    A single file version of the typechecker, containing just the
    definitions in the paper, together with minimal definitions
    for constants that were elided from the presentation.  The
    purpose of this file is simply to allow me to check that the
    program in the paper is type correct (according to Hugs 98,
    and according to the type checker itself; see below).

  A more realistic version of the typchecker, broken in to separate
  modules (roughly following the structure of the paper), together
  with additional code used for debugging and pretty printing.


    Assump.hs
      Assumption lists.
    Debug.hs
      A simple debug function that was used during testing.  It is
      not actually used in the distributed code.
    Id.hs
      Identifiers.
    Infer.hs
      Captures the general form of many type inference judgements.
    Kind.hs
      Kinds.
    Lit.hs
      Literals.
    Pat.hs
      Patterns.
    PPrint.hs
      A pretty printing library, which builds on the pretty printing
      library included in the standard Hugs distribution.
    Pred.hs
      Predicates and qualified types.
    Scheme.hs
      Type schemes.
    Subst.hs
      Substitutions.
    Testbed.hs
      A simple test bed, providing functions to type check a collection
      of binding groups, and output or save the results.
    TIMain.hs
      Type inference for expressions, binding groups, etc.
    TIMonad.hs
      The definition of a simple monad for type inference.
    TIProg.hs
      Type inference for top-level programs.
    Type.hs
      Types.
    Unify.hs
      Unification.

  The remaining files provide test data of one form or another, based
  where necessary on Haskell coded included in the Hugs distribution:

    Static.hs
      Definitions for use in describing the static (types + classes)
      component of a module.

    HaskellPrims.hs
      Typing assumptions for Hugs primitives that are used in the Prelude.

    StaticPrelude.hs
      Describes the static environment (types + classes) for the Prelude.
    SourcePrelude.hs
      An encoding of the standard Prelude library as Haskell data that
      can be fed into the type checker.
    HaskellPrelude.hs
      A set of typing assumptions for Prelude functions, generated
      automatically by running the savePrelude function in SourcePrelude.hs.

    StaticMaybe.hs
      Describes the static environment (types + classes) for the Maybe library.
    SourceMaybe.hs
      An encoding of the standard Maybe library as a Haskell data structure.
    HaskellMaybe.hs
      Typing assumptions for the Maybe library, generated by running the
      saveMaybe function in SourceMaybe.hs.

    StaticList.hs
      Describes the static environment (types + classes) for the List library.
    SourceList.hs
      An encoding of the standard List library as a Haskell data structure.
    HaskellList.hs
      Typing assumptions for the List library, generated by running the
      saveList function in SourceList.hs.

    StaticMonad.hs
      Describes the static environment (types + classes) for the Monad library.
    SourceMonad.hs
      An encoding of the standard Monad library as a Haskell data structure.
    HaskellMonad.hs
      Typing assumptions for the Monad library, generated by running the
      saveMonad function in SourceMonad.hs.

    StaticThih.hs
      Describes the static environment (types + classes) for the typechecker.
    SourceThih.hs
      An encoding of the typechecker as a Haskell data structure.
    HaskellThih.hs
      Typing assumptions for the typechecker, generated by running the
      saveThih function in SourceMaybe.hs.

    StaticTest.hs
      Describes the static environment (types + classes) for the test program.
    SourceTest.hs
      An encoding of misc Haskell functions as a Haskell data structure.
    HaskellTest.hs
      Typing assumptions generated by running the saveTest function in
      SourceTest.hs.

Simple example of use:

    Prelude> :l SourcePrelude
    SourcePrelude> main
    ... wait a while for the inferred list of typings to be displayed ...

------------------------------------------------------------------------------
