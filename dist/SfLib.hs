module SfLib where

import qualified Prelude
import qualified Datatypes
import qualified EqNat
import qualified Logic
import qualified Peano_dec
import qualified Specif


ble_nat :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_bool
ble_nat n m =
  case n of {
   Datatypes.O -> Datatypes.Coq_true;
   Datatypes.S n' ->
    case m of {
     Datatypes.O -> Datatypes.Coq_false;
     Datatypes.S m' -> ble_nat n' m'}}

type Coq_relation x = ()

next_nat_rect :: Datatypes.Coq_nat -> a1 -> Datatypes.Coq_nat -> a1
next_nat_rect n f n0 =
  f

next_nat_rec :: Datatypes.Coq_nat -> a1 -> Datatypes.Coq_nat -> a1
next_nat_rec n f n0 =
  next_nat_rect n f n0

empty_relation_rect :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> a1
empty_relation_rect n n0 =
  Prelude.error "absurd case"

empty_relation_rec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> a1
empty_relation_rec n n0 =
  empty_relation_rect n n0

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
beq_id id1 id2 =
  EqNat.beq_nat id1 id2

type Coq_partial_map a = Coq_id -> Datatypes.Coq_option a

empty :: Coq_partial_map a1
empty x =
  Datatypes.None

extend :: (Coq_partial_map a1) -> Coq_id -> a1 -> Coq_id ->
          Datatypes.Coq_option a1
extend gamma x t x' =
  case beq_id x x' of {
   Datatypes.Coq_true -> Datatypes.Some t;
   Datatypes.Coq_false -> gamma x'}

eq_id_dec :: Coq_id -> Coq_id -> Prelude.Bool
eq_id_dec i i' =
  id_rec (\n i'0 ->
    Specif.sumbool_rec (\_ -> Logic.eq_rec_r i'0 Prelude.True n) (\_ ->
      Prelude.False) (Peano_dec.eq_nat_dec n i'0)) i i'

