module Utils where

import qualified Prelude
import qualified Compare_dec
import qualified Datatypes
import qualified EqNat
import qualified Logic
import qualified Peano_dec
import qualified Specif


type Coq_id =
  Datatypes.Coq_nat
  -- singleton inductive, whose constructor was Id
  
id_rect :: (Datatypes.Coq_nat -> a1) -> Coq_id -> a1
id_rect f i =
  f i

id_rec :: (Datatypes.Coq_nat -> a1) -> Coq_id -> a1
id_rec =
  id_rect

beq_id :: Coq_id -> Coq_id -> Datatypes.Coq_bool
beq_id i i' =
  EqNat.beq_nat i i'

eq_id_dec :: Coq_id -> Coq_id -> Prelude.Bool
eq_id_dec i i' =
  id_rec (\n i'0 ->
    Specif.sumbool_rec (\_ -> Logic.eq_rec_r i'0 Prelude.True n) (\_ ->
      Prelude.False) (Peano_dec.eq_nat_dec n i'0)) i i'

lt_eq_lt_id_dec :: Coq_id -> Coq_id -> Prelude.Maybe Prelude.Bool
lt_eq_lt_id_dec i1 i2 =
  case Compare_dec.lt_eq_lt_dec i1 i2 of {
   Prelude.Just s ->
    case s of {
     Prelude.True -> Prelude.Just Prelude.True;
     Prelude.False -> Logic.eq_rec_r i2 (Prelude.Just Prelude.False) i1};
   Prelude.Nothing ->
    case Compare_dec.lt_dec i2 i1 of {
     Prelude.True -> Prelude.Nothing;
     Prelude.False -> Logic.coq_False_rec}}

type Coq_relation x = ()

ex_falso_quodlibet :: a1
ex_falso_quodlibet =
  Prelude.error "AXIOM TO BE REALIZED"

