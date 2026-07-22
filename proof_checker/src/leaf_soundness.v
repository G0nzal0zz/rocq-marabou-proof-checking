From mathcomp Require Import all_algebra all_ssreflect.

Require Import certificate_specs.
Require Import proof_tree.

Require Import constraint.
Require Import certificate.
Require Import checker.
Require Import farkas.
Require Import farkas_soundness.
Require Import sat.
Require Import arithmetic.
Require Import system_soundness.

Import CertificateSpecs.

Module LeafSoundness.

(* lemma check_tree_implies_check_cert tableau upper_bounds lower_bounds relu_constraints (proof_tree: Proof_tree.t) =
    match proof_tree with
    | Node _ -> true
    | Leaf contradiction ->
        let sys = mk_system_contradiction tableau upper_bounds lower_bounds in
        let certificate = mk_contradiction_certificate contradiction tableau upper_bounds lower_bounds in
        check_tree tableau upper_bounds lower_bounds relu_constraints proof_tree
        ==>
        check_cert sys certificate
[@@by auto]
[@@disable Farkas.check_cert, Checker.check_tree, Checker.mk_contradiction_certificate, Certificate.mk_system_contradiction]
[@@fc] *)
Lemma check_tree_implies_check_cert
  (tableau : Farkas.system m n)
  (ub lb : 'rV[R]_n)
  (constraints : seq Constraint.t)
  (contradiction : (m.+2).-tuple R)
  (x : 'rV[R]_n) :
  let sys := Cert.mk_system_contradiction tableau ub lb in
  let certificate := Cert.mk_contradiction_certificate contradiction tableau ub lb in
  Checker.check_tree tableau ub lb constraints (ProofTree.leaf contradiction) ->
  Farkas.check_cert sys certificate.
Proof.
  auto.
Qed.

(* lemma check_cert_implies_not_eval_system tableau upper_bounds lower_bounds x proof_tree certificate sys =
    match proof_tree with
    | Node _ -> true
    | Leaf contradiction ->
        sys = mk_system_contradiction (mk_eq_constraints tableau) upper_bounds lower_bounds &&
        well_formed_tableau_bounds tableau upper_bounds lower_bounds &&
        List.length x = List.length (List.hd tableau) &&
        check_cert sys certificate
        ==>
        eval_system sys x = false
[@@by [%use contradiction_system_evaluation_false tableau upper_bounds lower_bounds sys x certificate]
   @> auto]
[@@disable Checker.well_formed_tableau_bounds]
[@@fc]*)
Lemma check_cert_implies_not_eval_system
  (tableau : Farkas.system m n)
  (ub lb : 'rV[R]_n)
  (constraints : seq Constraint.t)
  (contradiction : (m.+2).-tuple R)
  (x : 'rV[R]_n) :
  let sys := Cert.mk_system_contradiction tableau ub lb in
  let certificate := Cert.mk_contradiction_certificate contradiction tableau ub lb in
  Checker.check_tree tableau ub lb constraints (ProofTree.leaf contradiction) ->
  FarkasSoundness.eval_system sys (trmx x) = false.
Proof.
  move: (check_tree_implies_check_cert tableau ub lb constraints contradiction x) => H_cert.
  move: (@FarkasSoundness.farkas_unsat (Cert.mk_system_contradiction tableau ub lb) ((Cert.mk_contradiction_certificate contradiction tableau ub lb)) (trmx x)) => H_farkas.
  by [].
Qed.

(* lemma soundness_eval_sys_composition tableau upper_bounds lower_bounds x =
    let sys = mk_system_contradiction (mk_eq_constraints tableau) upper_bounds lower_bounds in
    well_formed_tableau_bounds tableau upper_bounds lower_bounds &&
    List.length x = List.length (List.hd tableau) &&
    not (eval_system sys x)
    ==>
    not (eval_system (mk_eq_constraints tableau) x) || not (eval_system (mk_geq_constraints upper_bounds lower_bounds) x)
[@@by [%use destruct_mk_system (mk_eq_constraints tableau) upper_bounds lower_bounds]
   @> auto]
[@@disable Farkas.eval_system, Certificate.mk_system_contradiction, Checker.well_formed_tableau_bounds]
[@@fc]
[@@timeout 90] *)
(* WARN: This lemma is not being used *)
Lemma soundness_eval_sys_composition
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (ub lb : 'rV[R]_n)
  (x : 'rV[R]_n) :
    let sys := Cert.mk_system_contradiction (Cert.mk_eq_constraints tableau) ub lb in
    FarkasSoundness.eval_system sys (trmx x)
    ==
    let sys' := cat_tuple (Cert.mk_eq_constraints tableau)  (Cert.mk_geq_constraints ub lb) in
    FarkasSoundness.eval_system sys' (trmx x).
Proof.
  auto.
Qed.

(*lemma soundness_check_cert_composition tableau upper_bounds lower_bounds x =
    let sys = mk_system_contradiction (mk_eq_constraints tableau) upper_bounds lower_bounds in
    well_formed_tableau_bounds tableau upper_bounds lower_bounds &&
    List.length x = List.length (List.hd tableau) &&
    not (eval_system sys x)
    ==>
    not (is_in_kernel tableau x) || not (bounded x upper_bounds lower_bounds)
[@@by [%use soundness_eval_sys_composition tableau upper_bounds lower_bounds x]
   @> [%use eval_system_unsat_contra tableau upper_bounds lower_bounds x]
   @> auto]
[@@disable Certificate.mk_system_contradiction, Arithmetic.bounded,
    List.length, Checker.well_formed_tableau_bounds, Arithmetic.is_in_kernel,
    Farkas.eval_system, Certificate.mk_geq_constraints,
    Certificate.mk_eq_constraints, Certificate.mk_lower_bounds_constraints,
    List.append]
   [@@fc]*)
Lemma soundness_check_cert_composition
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (ub lb : 'rV[R]_n)
  (x : 'rV[R]_n) :
  let sys := Cert.mk_system_contradiction (Cert.mk_eq_constraints tableau) ub lb in
  (FarkasSoundness.eval_system sys (trmx x)) = false
  ->
  ((Arithmetic.is_in_kernel tableau x) && (Arithmetic.bounded x ub lb)) = false.
Proof.
  intros.
  case H_prop: ((Arithmetic.is_in_kernel tableau x) && (Arithmetic.bounded x ub lb)).
  - move : (SystemSoundness.system_soundness tableau ub lb x H_prop) => H_unsat.
    rewrite  <- H.
    simpl in *.
    by rewrite H_unsat.
  - reflexivity.
Qed.

(* lemma not_eval_system_implies_unsat tableau upper_bounds lower_bounds relu_constraints x =
    let sys = mk_system_contradiction (mk_eq_constraints tableau) upper_bounds lower_bounds in
    well_formed_tableau_bounds tableau upper_bounds lower_bounds &&
    List.length x = List.length (List.hd tableau) &&
    not (eval_system sys x)
    ==>
   unsat tableau upper_bounds lower_bounds relu_constraints x
[@@by [%use soundness_check_cert_composition tableau upper_bounds lower_bounds x]
   @> auto]
[@@disable Checker.well_formed_tableau_bounds, Certificate.mk_system_contradiction, Arithmetic.bounded]
[@@fc]
[@@timeout 120] *)
Lemma not_eval_system_implies_unsat
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (ub lb : 'rV[R]_n)
  (constraints : seq Constraint.t)
  (contradiction : (m.+2).-tuple R)
  (x : 'rV[R]_n) :
  let sys := Cert.mk_system_contradiction (Cert.mk_eq_constraints tableau) ub lb in
  (FarkasSoundness.eval_system sys (trmx x)) = false
  ->
  Sat.unsat tableau ub lb constraints x.
Proof.
  intros.
  rewrite /Sat.unsat.
  move: (soundness_check_cert_composition tableau ub lb x) => H_comp.
  have H_final := H_comp H.
  by rewrite H_final.
Qed.

(* lemma soundness_leaf tableau upper_bounds lower_bounds relu_constraints x proof_tree =
    match proof_tree with
    | Node _ -> true
    | Leaf contradiction ->
        well_formed_tableau_bounds tableau upper_bounds lower_bounds &&
        List.length x = List.length (List.hd tableau) &&
        check_tree (mk_eq_constraints tableau) upper_bounds lower_bounds relu_constraints proof_tree
        ==>
        unsat tableau upper_bounds lower_bounds relu_constraints x
[@@by [%use check_tree_implies_check_cert (mk_eq_constraints tableau) upper_bounds lower_bounds relu_constraints proof_tree]
   @> [%use not_eval_system_implies_unsat tableau upper_bounds lower_bounds relu_constraints x]
   @> auto]
[@@disable Arithmetic.bounded, List.length, Checker.well_formed_tableau_bounds, Arithmetic.is_in_kernel,
           Farkas.eval_system, Certificate.mk_eq_constraints, Certificate.mk_geq_constraints, Farkas.check_cert,
           Certificate.mk_system_contradiction]
[@@fc]
   [@@timeout 120] *)
Lemma leaf_soundness
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (ub lb : 'rV[R]_n)
  (constraints : seq Constraint.t)
  (contradiction : (m.+2).-tuple R)
  (x : 'rV[R]_n) :
  let system' := Cert.mk_eq_constraints tableau in
  Checker.check_tree system' ub lb constraints (ProofTree.leaf contradiction) ->
  Sat.unsat tableau ub lb constraints x.
Proof.
  intros system' H.
  move: (not_eval_system_implies_unsat tableau ub lb constraints contradiction x) => H_eval.
  move: (check_cert_implies_not_eval_system system' ub lb constraints contradiction x) => H_test.
  auto.
Qed.

End LeafSoundness.
