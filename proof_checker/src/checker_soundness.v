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
Require Import leaf_soundness.
Require Import node_soundness.


Import Farkas.
Import CertificateSpecs.

(*lemma check_tree_soundness_leaf (tableau: real list list) (upper_bounds: real list) (lower_bounds: real list)
        (constraints: Constraint.t list) (tree: Proof_tree.t) (x: real list) =
    (* this is a check performed in check_proof_tree, outside of check_tree *)
    well_formed_tableau_bounds tableau upper_bounds lower_bounds
    && List.length x = List.length (List.hd tableau)
    && check_all_splits tree constraints
    && check_tree (mk_eq_constraints tableau) upper_bounds lower_bounds constraints tree
    ==>
    match tree with
    | Leaf _ -> unsat tableau upper_bounds lower_bounds constraints x
    | Node _ -> true
[@@by [%use soundness_leaf tableau upper_bounds lower_bounds constraints x tree]
       @> auto]
[@@disable update_bounds, unsat, Checker.well_formed_tableau_bounds, List.length, Checker.check_tree, check_split]*)
Lemma check_tree_soundness_leaf
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (ub lb: Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (contradiction : (m.+2).-tuple R)
  (x : 'rV[R]_n) :
  Checker.check_tree (Cert.mk_eq_constraints tableau) ub lb constraints (ProofTree.leaf contradiction) ->
  Sat.unsat tableau ub lb constraints x.
Proof.
  intros.
  by apply (LeafSoundness.leaf_soundness tableau ub lb constraints contradiction x).
Qed.

(* lemma check_tree_parent_imply_check_tree_children tableau upper_bounds lower_bounds constraints tree =
    match tree with
    | Leaf _ -> true
    | Node (split, left, right) ->
        let (lb_left, ub_left), (lb_right, ub_right) = update_bounds_from_split lower_bounds upper_bounds split in
        (check_tree tableau upper_bounds lower_bounds constraints tree) [@trigger]
        ==>
        (check_tree tableau ub_left lb_left constraints left)
          && (check_tree tableau ub_right lb_right constraints right)
[@@by auto]
[@@disable check_tree, update_bounds_from_split]
[@@fc] *)
Lemma check_tree_parent_imply_check_tree_children
  (tableau : Farkas.system m n)
  (ub lb: Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (split : Split.t)
  (tleft tright : ProofTree.t)
  (x : 'rV[R]_n) :
  let bounds := Split.update_bounds_from_split ub lb split in
  (Checker.check_tree tableau ub lb constraints (ProofTree.node split tleft tright))
  ->
  (Checker.check_tree tableau bounds.1.2 bounds.1.1 constraints tleft) &&
  (Checker.check_tree tableau bounds.2.2 bounds.2.1 constraints tright).
Proof.
  rewrite /Checker.check_tree.
  move/andP=> [H H_right].
  move/andP: H => [H_split H_left].
  by apply/andP; split.
Qed.

(*lemma unsat_children_imply_unsat_parent tableau upper_bounds lower_bounds constraints proof_tree x =
    match proof_tree with
    | Leaf _ -> true
    | Node (split, left, right) ->
        let (lb_left, ub_left), (lb_right, ub_right) = update_bounds_from_split lower_bounds upper_bounds split in
        List.length x = List.length lower_bounds
        && List.length x = List.length upper_bounds
        && check_split split constraints
        && unsat tableau ub_left lb_left constraints x
        && unsat tableau ub_right lb_right constraints x
        ==>
        unsat tableau upper_bounds lower_bounds constraints x
[@@by [%use Node_soundness.soundness_split_contra tableau upper_bounds lower_bounds constraints x (split_of_node proof_tree)]
   @> auto]
   [@@timeout 120]*)
Lemma unsat_children_imply_unsat_parent
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (ub lb: Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (split : Split.t)
  (tleft tright : ProofTree.t)
  (x : 'rV[R]_n) :
  Split.check_split split constraints
  && Sat.unsat tableau (Split.update_bounds_from_split ub lb split).1.2 (Split.update_bounds_from_split ub lb split).1.1 constraints x
  && Sat.unsat tableau (Split.update_bounds_from_split ub lb split).2.2 (Split.update_bounds_from_split ub lb split).2.1 constraints x
  ->
  Sat.unsat tableau ub lb constraints x.
Proof.
  move/andP=> [/andP[H_split H_unsat_l] H_unsat_r].
  have H_sat_l : Sat.sat tableau (Split.update_bounds_from_split ub lb split).1.2 (Split.update_bounds_from_split ub lb split).1.1 constraints x = false.
  { move/eqP: H_unsat_l => H; exact H. }
  have H_sat_r : Sat.sat tableau (Split.update_bounds_from_split ub lb split).2.2 (Split.update_bounds_from_split ub lb split).2.1 constraints x = false.
  { move/eqP: H_unsat_r => H; exact H. }
  rewrite /Sat.unsat.
  apply/eqP.
  apply: (NodeSoundness.soundness_split_contra tableau ub lb constraints split x).
  by rewrite H_split H_sat_l H_sat_r.
Qed.


(*lemma check_tree_soundness_node (tableau: real list list) (upper_bounds: real list) (lower_bounds: real list)
    (constraints: Constraint.t list) (tree: Proof_tree.t) (x: real list) =
(* this is a check performed in check_proof_tree, outside of check_tree *)
  well_formed_tableau_bounds tableau upper_bounds lower_bounds
  && List.length x = List.length (List.hd tableau)
  && List.length x = List.length upper_bounds
  && List.length x = List.length lower_bounds
  && check_tree (mk_eq_constraints tableau) upper_bounds lower_bounds constraints tree
  ==>
  match tree with
  | Leaf _ -> true
  | Node (split, left, right)  ->
    let (lb_left, ub_left), (lb_right, ub_right) = update_bounds_from_split lower_bounds upper_bounds split in
    check_split split constraints
    && unsat tableau ub_left lb_left constraints x
    && unsat tableau ub_right lb_right constraints x
    ==>
    unsat tableau upper_bounds lower_bounds constraints x
[@@by [%use check_tree_parent_imply_check_tree_children (mk_eq_constraints tableau) upper_bounds lower_bounds constraints tree]
   @> [%use unsat_children_imply_unsat_parent tableau upper_bounds lower_bounds constraints tree x]
   @> auto]
   [@@timeout 120]*)
Lemma  check_tree_soundness_node
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (ub lb: Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (split : Split.t)
  (tleft tright : ProofTree.t)
  (x : 'rV[R]_n)
  (IHleft : forall ub lb, Checker.check_tree (Cert.mk_eq_constraints tableau) ub lb constraints tleft -> Sat.unsat tableau ub lb constraints x)
  (IHright : forall ub lb, Checker.check_tree (Cert.mk_eq_constraints tableau) ub lb constraints tright -> Sat.unsat tableau ub lb constraints x) :
  Checker.check_tree (Cert.mk_eq_constraints tableau) ub lb constraints (ProofTree.node split tleft tright) ->
  Sat.unsat tableau ub lb constraints x.
Proof.
  move=> H_check.
  move: (check_tree_parent_imply_check_tree_children (Cert.mk_eq_constraints tableau) ub lb constraints split tleft tright x H_check) => /andP [H_left H_right].
  set bounds := Split.update_bounds_from_split ub lb split.
  have H_unsat_l := IHleft bounds.1.2 bounds.1.1 H_left.
  have H_unsat_r := IHright bounds.2.2 bounds.2.1 H_right.
  apply: (unsat_children_imply_unsat_parent tableau ub lb constraints split tleft tright x).
  have H_split : Split.check_split split constraints.
  { move: H_check. by rewrite /Checker.check_tree => /andP[/andP[H_split _] _]. }
  rewrite /bounds.
  by rewrite H_split H_unsat_l H_unsat_r.
Qed.



(*theorem check_tree_soundness (tableau: real list list) (upper_bounds: real list) (lower_bounds: real list)
        (constraints: Constraint.t list) (tree: Proof_tree.t) (x: real list) =
    valid_proof tableau upper_bounds lower_bounds constraints tree
    && well_formed_vector tableau x
    ==>
    unsat tableau upper_bounds lower_bounds constraints x
[@@by [%expand "valid_proof"]
   @> [%expand "well_formed_vector"]
   @> induction ~id:[%id check_tree] ()
      @>>| [%use check_tree_soundness_full tableau upper_bounds lower_bounds constraints tree x]
             @> [%use check_tree_parent_imply_check_tree_children (mk_eq_constraints tableau)
                      upper_bounds lower_bounds constraints tree]
             @> [%use well_formed_preservation tableau upper_bounds lower_bounds (split_of_node tree)]
             @> auto
    ]
[@@disable List.length, well_formed_tableau_bounds, check_tree, mk_eq_constraints, unsat, set_nth,
           update_bounds_from_split]
[@@timeout 300]*)
Theorem check_tree_soundness
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (ub lb : Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (proof_tree : ProofTree.t)
  (x : 'rV[R]_n) :
  Checker.check_proof_tree tableau ub lb constraints proof_tree
  -> Sat.unsat tableau ub lb constraints x.
Proof.
elim: proof_tree ub lb => [split tleft IHleft tright IHright | contradiction] ub lb.
- rewrite /Checker.check_proof_tree in IHleft IHright.
  by apply: (check_tree_soundness_node tableau ub lb constraints split tleft tright x IHleft IHright).
- by apply: (check_tree_soundness_leaf tableau ub lb constraints contradiction x).
Qed.
