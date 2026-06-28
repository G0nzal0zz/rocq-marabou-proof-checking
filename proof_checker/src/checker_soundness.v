From mathcomp Require Import all_ssreflect all_fingroup all_algebra zmodp ssrnum ssrnat matrix eqtype.

Require Import certificate_specs.
Require Import farkas.
Require Import tightening.
Require Import constraint.
Require Import proof_tree.
Require Import checker.
Require Import sat.

Import Farkas.
Import CertificateSpecs.

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
  (tableau : system m n)
  (upper_bounds : Tightening.t_bounds)
  (lower_bounds : Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (proof_tree : ProofTree.t)  
  (x : 'rV[R]_n.+1) :
  Checker.check_tree tableau upper_bounds lower_bounds constraints proof_tree
  -> Sat.unsat tableau constraints x.
Proof.
Admitted.


