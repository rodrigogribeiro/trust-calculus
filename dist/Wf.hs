module Wf where

import qualified Prelude
import qualified Specif


coq_Fix_F_sub :: (a1 -> (a1 -> a2) -> a2) -> a1 -> a2
coq_Fix_F_sub f_sub x =
  f_sub x (\y -> coq_Fix_F_sub f_sub (Specif.proj1_sig y))

coq_Fix_sub :: (a1 -> (a1 -> a2) -> a2) -> a1 -> a2
coq_Fix_sub f_sub x =
  f_sub x (\y -> coq_Fix_sub f_sub (Specif.proj1_sig y))

coq_Fix_F_sub_rect :: (a1 -> (a1 -> a2) -> a2) -> (a1 -> (a1 -> () -> () ->
                      a3) -> () -> a3) -> a1 -> a3
coq_Fix_F_sub_rect =
  Prelude.error "AXIOM TO BE REALIZED"

coq_Fix_sub_rect :: (a1 -> (a1 -> a2) -> a2) -> (a1 -> (a1 -> () -> a3) -> ()
                    -> a3) -> a1 -> a3
coq_Fix_sub_rect =
  Prelude.error "AXIOM TO BE REALIZED"

