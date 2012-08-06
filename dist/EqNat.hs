module EqNat where

import qualified Prelude
import qualified Datatypes


eq_nat_decide :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Prelude.Bool
eq_nat_decide n =
  Datatypes.nat_rec (\m ->
    case m of {
     Datatypes.O -> Prelude.True;
     Datatypes.S n0 -> Prelude.False}) (\n0 iHn m ->
    case m of {
     Datatypes.O -> Prelude.False;
     Datatypes.S n1 -> iHn n1}) n

beq_nat :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_bool
beq_nat n m =
  case n of {
   Datatypes.O ->
    case m of {
     Datatypes.O -> Datatypes.Coq_true;
     Datatypes.S n0 -> Datatypes.Coq_false};
   Datatypes.S n1 ->
    case m of {
     Datatypes.O -> Datatypes.Coq_false;
     Datatypes.S m1 -> beq_nat n1 m1}}

