From mathcomp Require Import all_ssreflect all_algebra.

Require Import certificate_specs.

Require Import constraint.
Require Import split.
Require Import sat.
Require Import arithmetic.
Require Import util.

Open Scope ring_scope.

Import CertificateSpecs GRing.Theory Num.Theory Order.POrderTheory.

Module SingleSplitSoundness.

Lemma bounded_set_lb (x ub lb: 'rV[R]_n) (i : 'I_n) (k : R)
  : Arithmetic.bounded x ub lb ->
    k <= x 0 i ->
    Arithmetic.bounded x ub (set_nth_vector lb i k).
Proof.
  move=> /forallP Hb Hk.
  apply/forallP => j.
  rewrite /set_nth_vector mxE.
  case: eqP => [-> | Hij].
  - move: (Hb i) => /andP [H_lb H_ub]. by rewrite Hk H_ub.
  - by move: (Hb j) => /andP [H_lb H_ub].
Qed.

Lemma bounded_set_ub (x ub lb: 'rV[R]_n) (i : 'I_n) (k : R)
  : Arithmetic.bounded x ub lb ->
     x 0 i < k  ->
    Arithmetic.bounded x (set_nth_vector ub i k) lb.
Proof.
  move=> /forallP Hb Hk.
  apply/forallP => j.
  rewrite /set_nth_vector mxE.
  case: eqP => [-> | Hij].
  - move: (Hb i) => /andP [H_lb H_ub].
    rewrite H_lb. exact: (ltW Hk).
  - by move: (Hb j) => /andP [H_lb H_ub].
Qed.

(*lemma bounded_set_nth xs us ls k i =
    bounded xs us ls
    ==>
    bounded xs us (set_nth ls i k) ||
    bounded xs (set_nth us i k) ls
    [@@by auto]*)
Lemma bounded_set_nth
  (ub lb: 'rV[R]_n)
  (i : 'I_n)
  (k : R)
  (x : 'rV[R]_n) :
  Arithmetic.bounded x ub lb
  ->
  Arithmetic.bounded x (set_nth_vector ub i k) lb ||
  Arithmetic.bounded x ub (set_nth_vector lb i k).
Proof.
  move=> Hb.
  have Hcmp := lerP k (x 0 i).
  case: Hcmp.
  - move=> Hk.
    apply/orP; right.
    exact: bounded_set_lb Hb Hk.
  - move=> Hk.
    apply/orP; left.
    exact: bounded_set_ub Hb Hk.
Qed.

(*lemma soundness_single_var_split_matching tableau ubs lbs constraints x split =
    let (lbs_l, ubs_l), (lbs_r, ubs_r) = update_bounds_from_split lbs ubs split in
    match split with
    | SingleSplit (i, k) ->
        sat tableau ubs lbs constraints x
        ==>
        sat tableau ubs_l lbs_l constraints x ||
        sat tableau ubs_r lbs_r constraints x
    | _ -> true
   [@@by auto]*)
Theorem soundness_single_var_split
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (ub lb: 'rV[R]_n)
  (constraints : seq Constraint.t)
  (i : 'I_n)
  (k : R)
  (x : 'rV[R]_n) :
  let bounds := Split.update_bounds_from_split ub lb (Split.single i k) in
  Sat.sat tableau ub lb constraints x
  ->
  Sat.sat tableau bounds.1.2 bounds.1.1 constraints x ||
  Sat.sat tableau bounds.2.2 bounds.2.1 constraints x.
Proof.
  move=> bounds H_sat.
  unfold Sat.sat in *.
  move/andP: H_sat => [/andP[H_kernel H_bounded] H_relu].
  rewrite H_kernel H_relu !andbT /=.
  clear H_kernel H_relu.
  move: (bounded_set_nth ub lb i k x) => H_set_nth.
  by apply H_set_nth in H_bounded.
Qed.

End SingleSplitSoundness.
