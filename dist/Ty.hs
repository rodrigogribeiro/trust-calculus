module Ty where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified Peano
import qualified Specif


data Coq_secty =
   Trust
 | Untrust

secty_rect :: a1 -> a1 -> Coq_secty -> a1
secty_rect f f0 s =
  case s of {
   Trust -> f;
   Untrust -> f0}

secty_rec :: a1 -> a1 -> Coq_secty -> a1
secty_rec =
  secty_rect

secty_eq_dec :: Coq_secty -> Coq_secty -> Prelude.Bool
secty_eq_dec s s' =
  secty_rec (\s'0 ->
    case s'0 of {
     Trust -> Prelude.True;
     Untrust -> Prelude.False}) (\s'0 ->
    case s'0 of {
     Trust -> Prelude.False;
     Untrust -> Prelude.True}) s s'

data Coq_ty =
   Coq_ty_bool Coq_secty
 | Coq_arrow Coq_ty Coq_ty Coq_secty

ty_rect :: (Coq_secty -> a1) -> (Coq_ty -> a1 -> Coq_ty -> a1 -> Coq_secty ->
           a1) -> Coq_ty -> a1
ty_rect f f0 t =
  case t of {
   Coq_ty_bool s -> f s;
   Coq_arrow t0 t1 s -> f0 t0 (ty_rect f f0 t0) t1 (ty_rect f f0 t1) s}

ty_rec :: (Coq_secty -> a1) -> (Coq_ty -> a1 -> Coq_ty -> a1 -> Coq_secty ->
          a1) -> Coq_ty -> a1
ty_rec =
  ty_rect

ty_eq_dec :: Coq_ty -> Coq_ty -> Prelude.Bool
ty_eq_dec t t' =
  ty_rec (\s0 t'0 ->
    case t'0 of {
     Coq_ty_bool s1 ->
      Specif.sumbool_rec (\_ -> Logic.eq_rec_r s1 Prelude.True s0) (\_ ->
        Prelude.False) (secty_eq_dec s0 s1);
     Coq_arrow t0 t1 s1 -> Prelude.False}) (\t0 h t1 h0 s0 t'0 ->
    case t'0 of {
     Coq_ty_bool s1 -> Prelude.False;
     Coq_arrow t2 t3 s1 ->
      Specif.sumbool_rec (\_ ->
        Logic.eq_rec_r t2
          (Specif.sumbool_rec (\_ ->
            Logic.eq_rec_r t3
              (Specif.sumbool_rec (\_ -> Logic.eq_rec_r s1 Prelude.True s0)
                (\_ -> Prelude.False) (secty_eq_dec s0 s1)) t1) (\_ ->
            Prelude.False) (h0 t3)) t0) (\_ -> Prelude.False) (h t2)}) t t'

ty_size :: Coq_ty -> Datatypes.Coq_nat
ty_size t =
  case t of {
   Coq_ty_bool s -> Datatypes.O;
   Coq_arrow l r s ->
    Peano.plus (Peano.plus (Datatypes.S Datatypes.O) (ty_size l)) (ty_size r)}

