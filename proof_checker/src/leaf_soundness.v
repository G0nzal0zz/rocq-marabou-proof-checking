From mathcomp Require Import all_algebra all_ssreflect.

Require Import certificate_specs.
Require Import proof_tree.
Require Import tightening.
Require Import constraint.
Require Import certificate.
Require Import checker.
Require Import farkas.

Import CertificateSpecs.

Module LeafSoundness.

(*lemma check_tree_implies_check_cert tableau upper_bounds lower_bounds relu_constraints (proof_tree: Proof_tree.t) =*)
(*    match proof_tree with*)
(*    | Node _ -> true*)
(*    | Leaf contradiction ->*)
(*        let sys = mk_system_contradiction tableau upper_bounds lower_bounds in*)
(*        let certificate = mk_contradiction_certificate contradiction tableau upper_bounds lower_bounds in*)
(*        check_tree tableau upper_bounds lower_bounds relu_constraints proof_tree*)
(*        ==> *)
(*        check_cert sys certificate*)
(*[@@by auto]*)
(*[@@disable Farkas.check_cert, Checker.check_tree, Checker.mk_contradiction_certificate, Certificate.mk_system_contradiction]*)
(*[@@fc]*)
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
  Checker.check_tree tableau upper_bounds lower_bounds constraints (ProofTree.leaf contradiction)
  ->
  Farkas.check_cert sys certificate.
  Proof.
  Admitted.

End LeafSoundness.
