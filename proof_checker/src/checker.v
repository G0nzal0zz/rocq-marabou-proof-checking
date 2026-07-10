From mathcomp Require Import all_ssreflect all_algebra.

Require Import certificate_specs.
Require Import certificate.
Require Import proof_tree.
Require Import constraint.
Require Import farkas.
Require Import split.
Require Import arithmetic.

Import CertificateSpecs.
Import Farkas.

Module Checker.

(* check contradiction with polynomials representation *)
(*let check_contradiction (contradiction: Real.t list) (tableau: expr list) (upper_bounds: Real.t list) (lower_bounds: Real.t list): bool =*)
(*    let sys = mk_system_contradiction tableau upper_bounds lower_bounds in*)
(*    let certificate = mk_contradiction_certificate contradiction tableau upper_bounds lower_bounds in*)
(*    let res = (check_cert sys certificate) in*)
(*    res*)
Definition check_contradiction
  (contradiction : (m.+2).-tuple R)
  (tableau : system m n)
  (upper_bounds : 'rV[R]_n)
  (lower_bounds : 'rV[R]_n)
  : bool :=
  let sys := Cert.mk_system_contradiction tableau upper_bounds lower_bounds in
  let certificate := Cert.mk_contradiction_certificate contradiction tableau upper_bounds lower_bounds in
  (* WARN:
     `check_cert` expects `sys` and `certificate` to have the same size.
     But `sys` and `certificate` both have different sizes.
     It should be investigated if this fact is an error in my implementation or
     if the function `check_cert` should expect both arguments to have different sizes.
  *)
  check_cert sys certificate.

Fixpoint check_tree
  (tableau : system m n)
  (ub lb : 'rV[R]_n)
  (constraints : seq Constraint.t)
  (proof_node : ProofTree.t)
  : bool :=
  match proof_node with
  | ProofTree.leaf contradiction =>
    check_contradiction contradiction tableau ub lb
  | ProofTree.node split tleft tright =>
    let bounds := Split.update_bounds_from_split ub lb split in

    let valid_split := Split.check_split split constraints in
    let valid_left  := check_tree tableau bounds.1.2 bounds.1.1 constraints tleft in
    let valid_right := check_tree tableau bounds.2.2 bounds.2.1 constraints tright in
    valid_split && valid_left && valid_right
  end.

(* Main entry point to verify the proof tree.
   - perform sanity checks on the tableau and upper and lower bound vector dimensions.
   - check the tree recursively starting from the root. We use pattern matching to check
   that the root node contains no dynamic bound tightenings.
   The function `check_tree` will traverse the tree recursively; so if it returns true,
   it means that the proof is valid, i.e.all the bound tightenings are correct and
   all the contradiction vectors correpond to a contradiction.
*)
(*let check_proof_tree (tableau: Real.t list list) (upper_bounds: Real.t list) (lower_bounds: Real.t list) (constraints: Constraint.t list) (tree: Proof_tree.t) =*)
(*    well_formed_tableau_bounds tableau upper_bounds lower_bounds*)
(*    (* && check_all_splits tree constraints *)*)
(*    && check_tree (mk_eq_constraints tableau) upper_bounds lower_bounds constraints tree*)

Definition check_proof_tree
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (upper_bounds : 'rV[R]_n)
  (lower_bounds : 'rV[R]_n)
  (constraints : seq Constraint.t)
  (proof_tree : ProofTree.t)
  : bool :=
  check_tree (Cert.mk_eq_constraints tableau) upper_bounds lower_bounds constraints proof_tree.

End Checker.

