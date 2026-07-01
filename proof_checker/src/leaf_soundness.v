From mathcomp Require Import all_algebra all_ssreflect.

Require Import certificate_specs.
Require Import proof_tree.
Require Import tightening.
Require Import constraint.
Require Import certificate.
Require Import checker.
Require Import farkas.
Require Import farkas_soundness.
Require Import sat.

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
(* WARN: Is it possible to use ProofTree.leaf as an argument type? *)
Lemma check_tree_implies_check_cert
  (tableau : Farkas.system m n)
  (upper_bounds : Tightening.t_bounds)
  (lower_bounds : Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (contradiction : (m.+2).-tuple R)
  (x : 'rV[R]_n) :
  let sys := Certificate.mk_system_contradiction tableau upper_bounds lower_bounds in
  let certificate := Certificate.mk_contradiction_certificate contradiction tableau upper_bounds lower_bounds in
  Checker.check_tree tableau upper_bounds lower_bounds constraints (ProofTree.leaf contradiction) ->
  Farkas.check_cert sys certificate.
Proof.
  auto.
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
  (upper_bounds lower_bounds : Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (contradiction : (m.+2).-tuple R)
  (x : 'rV[R]_n) :
  let sys := Certificate.mk_system_contradiction (Certificate.mk_eq_constraints tableau) upper_bounds lower_bounds in
  not (FarkasSoundness.eval_system sys x)
  ==>
  Sat.unsat tableau upper_bounds lower_bounds constraints x.
Proof.
Admitted.

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
Lemma soundness_leaf
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (upper_bounds lower_bounds : Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (contradiction : (m.+2).-tuple R)
  (x : 'rV[R]_n) :
  Checker.check_tree (Certificate.mk_eq_constraints tableau) upper_bounds lower_bounds constraints (ProofTree.leaf contradiction) ->
  Sat.unsat tableau upper_bounds lower_bounds constraints x.
Proof.
  intros H.
  (* Apply the implication lemma directly to your hypothesis H *)
  move: (check_tree_implies_check_cert _ upper_bounds lower_bounds constraints contradiction x H) => H_cert.
  simpl in *.
Admitted.


End LeafSound.
