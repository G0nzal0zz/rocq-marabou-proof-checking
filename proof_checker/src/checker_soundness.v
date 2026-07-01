From mathcomp Require Import all_ssreflect all_fingroup all_algebra zmodp ssrnum ssrnat matrix eqtype.

Require Import certificate_specs.
Require Import farkas.
Require Import tightening.
Require Import constraint.
Require Import proof_tree.
Require Import checker.
Require Import sat.
Require Import certificate.
Require Import split.


Import Farkas.
Import CertificateSpecs.


(* It's convenient to have both cases we want in induction wrapped up into a single lemma. *)
(*lemma check_tree_soundness_full (tableau: real list list) (upper_bounds: real list) (lower_bounds: real list) *)
(*   (constraints: Constraint.t list) (tree: Proof_tree.t) (x: real list) =*)
(*(* this is a check performed in check_proof_tree, outside of check_tree *)*)
(* well_formed_tableau_bounds tableau upper_bounds lower_bounds*)
(* && List.length x = List.length (List.hd tableau)*)
(* && check_all_splits tree constraints*)
(* && check_tree (mk_eq_constraints tableau) upper_bounds lower_bounds constraints tree*)
(* ==>*)
(* match tree with *)
(* | Leaf _ -> unsat tableau upper_bounds lower_bounds constraints x*)
(* | Node (split, left, right)  -> *)
(*   let (lb_left, ub_left), (lb_right, ub_right) = update_bounds_from_split lower_bounds upper_bounds split in*)
(*   unsat tableau ub_left lb_left constraints x *)
(*   && unsat tableau ub_right lb_right constraints x*)
(*   ==> *)
(*   unsat tableau upper_bounds lower_bounds constraints x*)
(*[@@by [%use check_tree_soundness_leaf tableau upper_bounds lower_bounds constraints tree x]*)
(*   @> [%use check_tree_soundness_node tableau upper_bounds lower_bounds constraints tree x]*)
(*   @> unroll 50]*)

Lemma check_tree_soundness_full (tableau : (m.+2).-tuple ('rV[R]_n))
  (upper_bounds : Tightening.t_bounds)
  (lower_bounds : Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (proof_tree : ProofTree.t)
  (x : 'rV[R]_n) :
  Checker.check_tree (Certificate.mk_eq_constraints tableau) upper_bounds lower_bounds constraints proof_tree ->
  match proof_tree with
  | ProofTree.leaf _ => Sat.unsat tableau upper_bounds lower_bounds constraints x
  | ProofTree.node split tleft tright => 
    let '((lb_left, ub_left), (lb_right, ub_right)) := Split.update_bounds_from_split lower_bounds upper_bounds split in
    Sat.unsat tableau ub_left lb_left constraints x
    && Sat.unsat tableau ub_right lb_right constraints x ->
    Sat.unsat tableau upper_bounds lower_bounds constraints x
  end.
Proof.
Admitted.

(*theorem check_tree_soundness (tableau: real list list) (upper_bounds: real list) (lower_bounds: real list) *)
(*        (constraints: Constraint.t list) (tree: Proof_tree.t) (x: real list) =*)
(*    valid_proof tableau upper_bounds lower_bounds constraints tree*)
(*    && well_formed_vector tableau x*)
(*    ==>*)
(*    unsat tableau upper_bounds lower_bounds constraints x*)
(*[@@by [%expand "valid_proof"] *)
(*   @> [%expand "well_formed_vector"] *)
(*   @> induction ~id:[%id check_tree] ()*)
(*      @>>| [%use check_tree_soundness_full tableau upper_bounds lower_bounds constraints tree x]*)
(*             @> [%use check_tree_parent_imply_check_tree_children (mk_eq_constraints tableau) *)
(*                      upper_bounds lower_bounds constraints tree]*)
(*             @> [%use well_formed_preservation tableau upper_bounds lower_bounds (split_of_node tree)]*)
(*             @> auto*)
(*    ]*)
(*[@@disable List.length, well_formed_tableau_bounds, check_tree, mk_eq_constraints, unsat, set_nth, *)
(*           update_bounds_from_split]*)
(*[@@timeout 300]*)


Theorem check_tree_soundness
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (upper_bounds : Tightening.t_bounds)
  (lower_bounds : Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (proof_tree : ProofTree.t)
  (x : 'rV[R]_n) :
  Checker.check_proof_tree tableau upper_bounds lower_bounds constraints proof_tree
  -> Sat.unsat tableau upper_bounds lower_bounds constraints x.
Proof.
Admitted.


