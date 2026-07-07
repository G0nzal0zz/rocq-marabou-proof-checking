From mathcomp Require Import all_ssreflect all_algebra.

Require Import certificate_specs.
Require Import tightening.
Require Import constraint.
Require Import split.
Require Import sat.

Import CertificateSpecs.

Module NodeSoundness.

(*lemma soundness_split_contra tableau upper_bounds lower_bounds constraints x split =
    let (lb_left, ub_left), (lb_right, ub_right) = update_bounds_from_split lower_bounds upper_bounds split in
    List.length x = List.length lower_bounds 
    && List.length x = List.length upper_bounds
    && check_split split constraints
    && not (sat tableau ub_left lb_left constraints x 
        || sat tableau ub_right lb_right constraints x)
    ==>
    not (sat tableau upper_bounds lower_bounds constraints x)
[@@by [%use soundness_split tableau upper_bounds lower_bounds constraints x split] 
    @> auto]
[@@fc]*)
Lemma soundness_split_contra
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (ub lb: Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (split : Split.t)
  (x : 'rV[R]_n) :
  Split.check_split split constraints &&
  (Sat.sat tableau (Split.update_bounds_from_split ub lb split).1.2 (Split.update_bounds_from_split ub lb split).1.1 constraints x ||
  Sat.sat tableau (Split.update_bounds_from_split ub lb split).2.2 (Split.update_bounds_from_split ub lb split).2.1 constraints x) = false
  ->
  Sat.sat tableau ub lb constraints x = false.
Proof.
Admitted.

End NodeSoundness.
