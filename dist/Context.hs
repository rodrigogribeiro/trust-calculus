module Context where

import qualified Prelude
import qualified Datatypes
import qualified Utils


type Coq_finite_map a =
  Datatypes.Coq_list (Datatypes.Coq_prod Utils.Coq_id a)

empty :: Coq_finite_map a1
empty =
  Datatypes.Coq_nil

extend :: Utils.Coq_id -> a1 -> (Coq_finite_map a1) -> Datatypes.Coq_list
          (Datatypes.Coq_prod Utils.Coq_id a1)
extend x t gamma =
  case gamma of {
   Datatypes.Coq_nil -> Datatypes.Coq_cons (Datatypes.Coq_pair x t)
    Datatypes.Coq_nil;
   Datatypes.Coq_cons p gam ->
    case p of {
     Datatypes.Coq_pair y t' ->
      case Utils.eq_id_dec x y of {
       Prelude.True -> Datatypes.Coq_cons (Datatypes.Coq_pair y t) gam;
       Prelude.False -> Datatypes.Coq_cons (Datatypes.Coq_pair y t')
        (extend x t gam)}}}

lookup :: Utils.Coq_id -> (Coq_finite_map a1) -> Datatypes.Coq_option a1
lookup x gamma =
  case gamma of {
   Datatypes.Coq_nil -> Datatypes.None;
   Datatypes.Coq_cons p gam ->
    case p of {
     Datatypes.Coq_pair y t' ->
      case Utils.eq_id_dec x y of {
       Prelude.True -> Datatypes.Some t';
       Prelude.False -> lookup x gam}}}

eq_rew_r_dep :: a1 -> a1 -> a2 -> a2
eq_rew_r_dep x y hC =
  hC

