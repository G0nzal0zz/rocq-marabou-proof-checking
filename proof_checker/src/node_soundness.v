From mathcomp Require Import all_ssreflect all_algebra.

Require Import certificate_specs.
Require Import tightening.
Require Import constraint.
Require Import split.
Require Import split_soundness.
Require Import sat.

Import CertificateSpecs.

Module NodeSoundness.

(*lemma soundness_split tableau upper_bounds lower_bounds constraints x split =
    let (lb_left, ub_left), (lb_right, ub_right) = update_bounds_from_split lower_bounds upper_bounds split in
    List.length x = List.length lower_bounds
    && List.length x = List.length upper_bounds
    && check_split split constraints
    && sat tableau upper_bounds lower_bounds constraints x
    ==>
    sat tableau ub_left lb_left constraints x
    || sat tableau ub_right lb_right constraints x
[@@by [%use soundness_split_helper tableau upper_bounds lower_bounds constraints x split]
    @> auto]
[@@fc]*)
Lemma soundness_split
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (ub lb: Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (split : Split.t)
  (x : 'rV[R]_n) :
  Split.check_split split constraints &&
  Sat.sat tableau ub lb constraints x
  ->
  let bounds := Split.update_bounds_from_split ub lb split in
  Sat.sat tableau bounds.1.2 bounds.1.1 constraints x ||
  Sat.sat tableau bounds.2.2 bounds.2.1 constraints x.
Proof.
  case: split => [i k | b f aux] /andP [H_check H_sat].
  - move: (SplitSoundness.soundness_single_var_split tableau ub lb constraints i k x) => H_single.
    auto.
  - move: (SplitSoundness.soundness_relu_split tableau ub lb constraints b f aux x) => H_relu.
    move: H_relu; apply; apply/andP; split => //.
Qed.

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
  let bounds := Split.update_bounds_from_split ub lb split in
Split.check_split split constraints &&
~~ (Sat.sat tableau bounds.1.2 bounds.1.1 constraints x ||
     Sat.sat tableau bounds.2.2 bounds.2.1 constraints x)
->
~~ Sat.sat tableau ub lb constraints x.
Proof.
move=> bounds.
move=> /andP [Hcheck Hnot].
apply/negP.
move=> Hsat.

have Hor :
  Sat.sat tableau bounds.1.2 bounds.1.1 constraints x ||
  Sat.sat tableau bounds.2.2 bounds.2.1 constraints x.
  apply: (soundness_split tableau ub lb constraints split x).
  by rewrite Hcheck Hsat.

move/negP: Hnot.
move=> Hcontra.
exact: (Hcontra Hor).
Qed.

End NodeSoundness.
