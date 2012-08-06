module Wf0 where

import qualified Prelude
import qualified Logic
import qualified Specif
import qualified Wf


__ :: any
__ = Prelude.error "Logical or arity value used"

coq_Fix_F_sub :: (a1 -> (a1 -> a2) -> a2) -> a1 -> a2
coq_Fix_F_sub f_sub x =
  f_sub x (\y -> coq_Fix_F_sub f_sub (Specif.proj1_sig y))

coq_Fix_sub :: (a1 -> (a1 -> a2) -> a2) -> a1 -> a2
coq_Fix_sub f_sub x =
  f_sub x (\y -> coq_Fix_sub f_sub (Specif.proj1_sig y))

coq_Fix_F_sub_rect :: (a1 -> (a1 -> a2) -> a2) -> (a1 -> (a1 -> () -> () ->
                      a3) -> () -> a3) -> a1 -> a3
coq_Fix_F_sub_rect f inv x =
  Wf.well_founded_induction_type (\x0 x1 _ ->
    Logic.eq_rect_r
      (f x0 (\y ->
        let {
         fix_F_sub x2 =
           f x2 (\y0 -> fix_F_sub (Specif.proj1_sig y0))}
        in fix_F_sub (Specif.proj1_sig y))) (inv x0 x1 __)
      (let {
        fix_F_sub x2 =
          f x2 (\y -> fix_F_sub (Specif.proj1_sig y))}
       in fix_F_sub x0)) x __

coq_Fix_sub_rect :: (a1 -> (a1 -> a2) -> a2) -> (a1 -> (a1 -> () -> a3) -> ()
                    -> a3) -> a1 -> a3
coq_Fix_sub_rect f inv x =
  coq_Fix_F_sub_rect f (\x0 x1 _ ->
    let {x2 = \y -> x1 y __ __} in
    let {q = inv x0 (\y _ -> x2 y) __} in
    Logic.eq_rect
      (f x0 (\y ->
        let {
         fix_F_sub x3 =
           f x3 (\y0 -> fix_F_sub (Specif.proj1_sig y0))}
        in fix_F_sub (Specif.proj1_sig y))) q
      (f x0 (\y ->
        let {
         fix_F_sub x3 =
           f x3 (\y0 -> fix_F_sub (Specif.proj1_sig y0))}
        in fix_F_sub (Specif.proj1_sig y)))) x

