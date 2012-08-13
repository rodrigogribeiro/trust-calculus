module TypeChecker where

import qualified Prelude
import qualified Context
import qualified Datatypes
import qualified Peano
import qualified Specif
import qualified Subtype
import qualified Syntax
import qualified Ty
import qualified Utils


sec_ordering_dec :: Ty.Coq_secty -> Ty.Coq_secty -> Prelude.Bool
sec_ordering_dec s s' =
  case s of {
   Ty.Trust -> Prelude.True;
   Ty.Untrust ->
    case s' of {
     Ty.Trust -> Prelude.False;
     Ty.Untrust -> Prelude.True}}

typair_size :: Ty.Coq_ty -> Ty.Coq_ty -> Datatypes.Coq_nat
typair_size t t' =
  Peano.plus (Ty.ty_size t) (Ty.ty_size t')

internal_eq_rew_dep :: a1 -> a2 -> a1 -> a2
internal_eq_rew_dep x f y =
  f

subtype_dec_func :: (Specif.Coq_sigT Ty.Coq_ty Ty.Coq_ty) -> Prelude.Bool
subtype_dec_func x =
  let {t = Specif.projT1 x} in
  let {t' = Specif.projT2 x} in
  let {
   subtype_dec0 = \t0 t'0 ->
    let {y = Specif.Coq_existT t0 t'0} in
    subtype_dec_func (Specif.proj1_sig y)}
  in
  case t of {
   Ty.Coq_ty_bool s ->
    case t' of {
     Ty.Coq_ty_bool s' -> sec_ordering_dec s s';
     Ty.Coq_arrow t0 t1 s0 -> Prelude.False};
   Ty.Coq_arrow l r s ->
    case t' of {
     Ty.Coq_ty_bool s0 -> Prelude.False;
     Ty.Coq_arrow l' r' s' ->
      let {filtered_var = subtype_dec0 l' l} in
      let {filtered_var0 = subtype_dec0 r r'} in
      let {filtered_var1 = sec_ordering_dec s s'} in
      case filtered_var of {
       Prelude.True ->
        case filtered_var0 of {
         Prelude.True -> filtered_var1;
         Prelude.False -> Prelude.False};
       Prelude.False -> Prelude.False}}}

subtype_dec :: Ty.Coq_ty -> Ty.Coq_ty -> Prelude.Bool
subtype_dec t t' =
  subtype_dec_func (Specif.Coq_existT t t')

trustworth :: Ty.Coq_ty -> Prelude.Bool
trustworth t =
  Ty.secty_rec (\s ->
    case s of {
     Ty.Trust -> Prelude.True;
     Ty.Untrust -> Prelude.False}) (\s ->
    case s of {
     Ty.Trust -> Prelude.False;
     Ty.Untrust -> Prelude.True}) (Subtype.sectyof t) Ty.Trust

var_dec :: Utils.Coq_id -> (Context.Coq_finite_map Ty.Coq_ty) ->
           Prelude.Maybe Ty.Coq_ty
var_dec i ctx =
  let {o = Context.lookup i ctx} in
  case o of {
   Datatypes.Some t -> Prelude.Just t;
   Datatypes.None -> Prelude.Nothing}

arrow_split :: Ty.Coq_ty -> Prelude.Maybe
               (Datatypes.Coq_prod Ty.Coq_ty Ty.Coq_ty)
arrow_split t =
  case t of {
   Ty.Coq_ty_bool s -> Prelude.Nothing;
   Ty.Coq_arrow t1 t2 s -> Prelude.Just (Datatypes.Coq_pair t1 t2)}

is_a_bool_ty :: Ty.Coq_ty -> Prelude.Bool
is_a_bool_ty t =
  case t of {
   Ty.Coq_ty_bool s -> Prelude.True;
   Ty.Coq_arrow t1 t2 s -> Prelude.False}

typecheck_dec :: Syntax.Coq_term -> (Context.Coq_finite_map Ty.Coq_ty) ->
                 Prelude.Maybe Ty.Coq_ty
typecheck_dec e ctx =
  case e of {
   Syntax.Coq_tm_var i -> var_dec i ctx;
   Syntax.Coq_tm_app l r ->
    case typecheck_dec l ctx of {
     Prelude.Just s ->
      case typecheck_dec r ctx of {
       Prelude.Just s0 ->
        case arrow_split s of {
         Prelude.Just s1 ->
          case subtype_dec s0 (Datatypes.fst s1) of {
           Prelude.True -> Prelude.Just
            (Subtype.update_secty (Datatypes.snd s1) (Subtype.sectyof s));
           Prelude.False -> Prelude.Nothing};
         Prelude.Nothing -> Prelude.Nothing};
       Prelude.Nothing -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing};
   Syntax.Coq_tm_abs i ty e0 ->
    case typecheck_dec e0 (Context.extend i ty ctx) of {
     Prelude.Just s -> Prelude.Just (Ty.Coq_arrow ty s Ty.Trust);
     Prelude.Nothing -> Prelude.Nothing};
   Syntax.Coq_tm_trust t ->
    case typecheck_dec t ctx of {
     Prelude.Just s -> Prelude.Just (Subtype.update_secty s Ty.Trust);
     Prelude.Nothing -> Prelude.Nothing};
   Syntax.Coq_tm_distrust t ->
    case typecheck_dec t ctx of {
     Prelude.Just s -> Prelude.Just (Subtype.update_secty s Ty.Untrust);
     Prelude.Nothing -> Prelude.Nothing};
   Syntax.Coq_tm_check t ->
    case typecheck_dec t ctx of {
     Prelude.Just s ->
      case trustworth s of {
       Prelude.True -> Prelude.Just s;
       Prelude.False -> Prelude.Nothing};
     Prelude.Nothing -> Prelude.Nothing};
   _ -> Prelude.Just (Ty.Coq_ty_bool Ty.Trust)}

