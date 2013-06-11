Mechanized Metatheory for a Lambda-Calculus with Trust Types
=============================================================


This is a formalization, in Coq proof assistant, of a Church-style type system for a lambda-calculus with
trust types as proposed in "Trust in lambda-calculus.". The formalization includes:
   - A type soundness proof using a small-step call-by-value semantics.
   - Proof of the erasure and simulation theorems.
   - Definition of syntax directed type system and a proof of its sound and completeness with
     relation to the original type system (i.e. the one published in "Trust in lambda-calculus").
   - Proof of the decidability of the typing problem given by the syntax directed type system.
     From this proof, is possible to extract a certified typechecker for the language.

Module Structure
----------------

The formalization is composed by the following modules:

1 - Utils: This module contains some utilities like tactics and definitions about identifiers
           that are used by several modules.
2 - Ty: Definition of type and trust annotation syntax.
3 - Syntax: Definition of term syntax.
4 - Context: Definitions related to typing contexts and lemmas about them.
5 - Semantics: Definition of the small step operational semantics. This module
               contains the proof that the proposed semantics is deterministic.
6 - Subtype: Definition of the trust annotation ordering and subtype relation.
             This module also provide several lemmas about these two ordering relations.
7 - TypeSystem: This module defines the non-syntax directed type system, the proof of
                type soundness and their related lemmas, the syntax directed type system
	        and its proof of soundness and completeness with respect to the 
	        non-syntax directed one.
8 - TypeChecker: This module proves the decidability of the typing problem for
                 the lambda calculus with trust types. From this proof, we can
		 extract the certified type checker.
9 - Simulation: This module provides definitions and proofs of erasure and
                simulations theorems.
10 - Stlc: Definitions of the simply typed lambda calculus. This is used
           in the formalization of erasure and simulations properties.
11 - Extraction: This module contains commands to extract the certified type checker.
                 By default, it generate the Haskell code of the type checker in
		 the "dist" directory.

Extracting the Certified Type-checker
-------------------------------------

The current distribuition comes with a makefile that compile all modules and extract the
Haskell type-checker code in the "dist" directory. This behavior can be changed by
simple modifications on the Extraction module, as follows:

* Changing the extraction directory: Just change the parameter of Cd command to the appropriate 
directory. The directory must exist.

* Changing the language to generate code. Coq supports extraction to OCaml, Haskell and Scheme.
  If you want to generate the type checker code in OCaml, just change the Recursive Extraction command 
  in the Extraction module to: Recursive Extraction Ocaml. To generate Scheme change the same command
  to Recursive Extraction Scheme.