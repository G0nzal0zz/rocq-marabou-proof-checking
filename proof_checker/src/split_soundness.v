From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import ssrnum.

Require Import certificate_specs.

Require Import constraint.
Require Import split.
Require Import sat.
Require Import arithmetic.
Require Import util.
Require Import single_var_split_soundness.
Require Import relu_split_soundness.

Open Scope ring_scope.

Import CertificateSpecs GRing.Theory Num.Theory Order.POrderTheory.

Module SplitSoundness.

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
  move: (SingleSplitSoundness.bounded_set_nth ub lb i k x) => H_set_nth.
  by apply H_set_nth in H_bounded.
Qed.

(*theorem soundness_relu_split tableau us ls constraints xs b f aux split =
    let (lb_left, ub_left), (lb_right, ub_right) = update_bounds_from_split ls us split in
    List.length xs = List.length ls
    && List.length xs = List.length us
    && List.mem (Relu (b,f,aux)) constraints
    && split = ReluSplit (b, f, aux)
    && sat tableau us ls constraints xs
    ==>
    sat tableau ub_left lb_left constraints xs
    || sat tableau ub_right lb_right constraints xs
[@@by [%use sat_eval_relu tableau us ls constraints xs b f aux]
    @> [%use relu_split_soundness_sat xs tableau ls us constraints b f aux]
    @> intros
    @> auto
    ]
[@@disable sat, update_bounds_from_split, List.length, List.mem]
[@@fc] *)
Theorem soundness_relu_split
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (ub lb: 'rV[R]_n)
  (constraints : seq Constraint.t)
  (b f aux : 'I_n)
  (x : 'rV[R]_n) :
  let relu := Split.relu b f aux in
  let bounds := Split.update_bounds_from_split ub lb relu in
  Split.check_split relu constraints &&
  Sat.sat tableau ub lb constraints x
  ->
  (Sat.sat tableau bounds.1.2 bounds.1.1 constraints x
  || Sat.sat tableau bounds.2.2 bounds.2.1 constraints x).
Proof.
  move => relu bounds /andP[H_split H_sat].
  unfold Sat.sat.
  unfold Sat.sat in H_sat.
  move: H_sat => /andP[/andP[H_kernel H_bounded] H_relu].
  rewrite H_kernel H_relu !andbT /=.
  clear H_kernel.
  by move: (ReluSplitSoundness.soundness_relu_split_bounded ub lb constraints b f aux x H_split H_bounded H_relu). 
Qed.

End SplitSoundness.
