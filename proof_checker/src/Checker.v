From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect all_algebra.

Require Import Certificate.
Require Import Farkas.
Require Import Split.

Inductive Constraint.

Section Checker.

Variable (R' : numDomainType).
Variable (n : nat).
Variable (m : nat).

Print Farkas.expr.

Definition poly : Type := Farkas.poly R' n.

Definition expr : Type := Farkas.expr R' n.

Definition example_poly : 'rV[R']_n.+1 := \row_(i < n.+1) (0: R').  (* all zeros *)
Definition example_eq : Farkas.expr R' n := Farkas.Eq example_poly.

Definition system : Type := Farkas.system R' n m.

Definition s : system :=
  [tuple of nseq m.+2 example_eq].

(*let mk_system_contradiction (tableau: expr list) (upper_bounds: Real.t list) (lower_bounds: Real.t list): expr list =*)
(*  tableau @ (mk_geq_constraints upper_bounds lower_bounds)*)

(* TODO: Implement function *)
Definition mk_system_contradcition
  (tableau : list expr)
  (upper_bounds : list R)
  (lower_bounds : list R)
  : system :=
  s.


(*let mk_contradiction_certificate (contradiction: Real.t list) (tableau: expr list) (upper_bounds: Real.t list) (lower_bounds: Real.t list) =*)
(*    let lc = compute_combination contradiction tableau in*)
(*    contradiction @ ((mk_upper_bound_certificate lc) @ (mk_lower_bound_certificate lc))*)

(* TODO: Implement function *)
Definition mk_contradiction_certificate
  (contradiction : list R)
  (tableau : list expr)
  (upper_bounds : list R)
  (lower_bounds : list R)
  : m.+2.-tuple R' :=
  [tuple of nseq m.+2 0].

(* check contradiction with polynomials representation *)
(*let check_contradiction (contradiction: Real.t list) (tableau: expr list) (upper_bounds: Real.t list) (lower_bounds: Real.t list): bool =*)
(*    let sys = mk_system_contradiction tableau upper_bounds lower_bounds in*)
(*    let certificate = mk_contradiction_certificate contradiction tableau upper_bounds lower_bounds in*)
(*    let res = (check_cert sys certificate) in*)
(*    res*)

Definition check_contradiction
  (contradiction : list R)
  (tableau : list expr)
  (upper_bounds : list R)
  (lower_bounds : list R)
  : bool :=
  let sys : system := mk_system_contradcition tableau upper_bounds lower_bounds in
  let certificate := mk_contradiction_certificate contradiction tableau upper_bounds lower_bounds in 
  Farkas.check_cert sys certificate.

Print Certificate.

(* WARN: Should I be using mathcomp's reals or Rocq's Stdlib reals? *)
Fixpoint check_tree
  (tableau : list expr)
  (upper_bounds : list R)
  (lower_bounds : list R)
  (constraints : list constraint)
  (proof_node : proof_tree)
  : bool :=
  match proof_node with
  | leaf contradiction => 
      check_contradiction contradiction
                          tableau
                          upper_bounds
                          lower_bounds
  | node split tleft tright =>
      let valid_split := check_split split constraints in
      let bounds := update_bounds_from_split
                      lower_bounds
                      upper_bounds
                      split in
      let '((lb_left, ub_left), (lb_right, ub_right)) := bounds in

      let valid_children :=
        andb
          (check_tree tableau ub_left lb_left constraints tleft)
          (check_tree tableau ub_right lb_right constraints tright)
      in

      andb valid_children valid_split
  end.

End Checker.
