module Subtype where

import qualified Prelude
import qualified Ty


sectyof :: Ty.Coq_ty -> Ty.Coq_secty
sectyof t =
  case t of {
   Ty.Coq_ty_bool s -> s;
   Ty.Coq_arrow t0 t1 s -> s}

update :: Ty.Coq_ty -> Ty.Coq_secty -> Ty.Coq_ty
update t s =
  case t of {
   Ty.Coq_ty_bool s0 -> Ty.Coq_ty_bool s;
   Ty.Coq_arrow l r s0 -> Ty.Coq_arrow l r s}

lub_secty :: Ty.Coq_secty -> Ty.Coq_secty -> Ty.Coq_secty
lub_secty x y =
  case x of {
   Ty.Trust -> y;
   Ty.Untrust -> Ty.Untrust}

update_secty :: Ty.Coq_ty -> Ty.Coq_secty -> Ty.Coq_ty
update_secty t s =
  case t of {
   Ty.Coq_ty_bool s' -> Ty.Coq_ty_bool (lub_secty s s');
   Ty.Coq_arrow l r s' -> Ty.Coq_arrow l r (lub_secty s s')}

