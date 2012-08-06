module Syntax where

import qualified Prelude
import qualified Ty
import qualified Utils


data Coq_term =
   Coq_tm_false
 | Coq_tm_true
 | Coq_tm_var Utils.Coq_id
 | Coq_tm_app Coq_term Coq_term
 | Coq_tm_abs Utils.Coq_id Ty.Coq_ty Coq_term
 | Coq_tm_trust Coq_term
 | Coq_tm_distrust Coq_term
 | Coq_tm_check Coq_term

term_rect :: a1 -> a1 -> (Utils.Coq_id -> a1) -> (Coq_term -> a1 -> Coq_term
             -> a1 -> a1) -> (Utils.Coq_id -> Ty.Coq_ty -> Coq_term -> a1 ->
             a1) -> (Coq_term -> a1 -> a1) -> (Coq_term -> a1 -> a1) ->
             (Coq_term -> a1 -> a1) -> Coq_term -> a1
term_rect f f0 f1 f2 f3 f4 f5 f6 t =
  case t of {
   Coq_tm_false -> f;
   Coq_tm_true -> f0;
   Coq_tm_var i -> f1 i;
   Coq_tm_app t0 t1 ->
    f2 t0 (term_rect f f0 f1 f2 f3 f4 f5 f6 t0) t1
      (term_rect f f0 f1 f2 f3 f4 f5 f6 t1);
   Coq_tm_abs i t0 t1 -> f3 i t0 t1 (term_rect f f0 f1 f2 f3 f4 f5 f6 t1);
   Coq_tm_trust t0 -> f4 t0 (term_rect f f0 f1 f2 f3 f4 f5 f6 t0);
   Coq_tm_distrust t0 -> f5 t0 (term_rect f f0 f1 f2 f3 f4 f5 f6 t0);
   Coq_tm_check t0 -> f6 t0 (term_rect f f0 f1 f2 f3 f4 f5 f6 t0)}

term_rec :: a1 -> a1 -> (Utils.Coq_id -> a1) -> (Coq_term -> a1 -> Coq_term
            -> a1 -> a1) -> (Utils.Coq_id -> Ty.Coq_ty -> Coq_term -> a1 ->
            a1) -> (Coq_term -> a1 -> a1) -> (Coq_term -> a1 -> a1) ->
            (Coq_term -> a1 -> a1) -> Coq_term -> a1
term_rec =
  term_rect

