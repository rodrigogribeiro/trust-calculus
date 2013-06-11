(* Extracting the certified type checker.
   We extract the type checker as a Haskell program.

   The extracted code can be found at dist directory.
 *)

Require Import TypeChecker.

Extraction Language Haskell.

Cd "dist".

Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumor   => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].


Recursive Extraction Library TypeChecker.
