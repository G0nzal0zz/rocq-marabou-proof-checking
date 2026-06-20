From mathcomp Require Import all_ssreflect all_algebra.

Require Import certificate_specs.
Require Import certificate.
Require Import proof_tree.
Require Import constraint.
Require Import farkas.
Require Import split.
Require Import tightening.
Require Import arithmetic.

Import CertificateSpecs.
Import Farkas.


(*let mk_contradiction_certificate (contradiction: Real.t list) (tableau: expr list) (upper_bounds: Real.t list) (lower_bounds: Real.t list) =*)
(*    let lc = compute_combination contradiction tableau in*)
(*    contradiction @ ((mk_upper_bound_certificate lc) @ (mk_lower_bound_certificate lc))*)
Definition mk_contradiction_certificate
  (contradiction : seq R)
  (tableau : system m n)
  (upper_bounds : Tightening.t_bounds)
  (lower_bounds : Tightening.t_bounds)
  : seq R :=
  let lc := Arithmetic.compute_combination contradiction tableau in
  let upper_bound_cert := Certificate.mk_upper_bound_certificate lc in
  let lower_bound_cert := Certificate.mk_lower_bound_certificate lc in
  contradiction ++ (upper_bound_cert ++ lower_bound_cert).

(* check contradiction with polynomials representation *)
(*let check_contradiction (contradiction: Real.t list) (tableau: expr list) (upper_bounds: Real.t list) (lower_bounds: Real.t list): bool =*)
(*    let sys = mk_system_contradiction tableau upper_bounds lower_bounds in*)
(*    let certificate = mk_contradiction_certificate contradiction tableau upper_bounds lower_bounds in*)
(*    let res = (check_cert sys certificate) in*)
(*    res*)
Definition check_contradiction
  (contradiction : seq R)
  (tableau : system m n)
  (upper_bounds : Tightening.t_bounds)
  (lower_bounds : Tightening.t_bounds)
  : bool :=
  let sys := Certificate.mk_system_contradiction tableau upper_bounds lower_bounds in
  let certificate := mk_contradiction_certificate contradiction tableau upper_bounds lower_bounds in 
  check_cert sys certificate.

Fixpoint check_tree
  (tableau : system m n)
  (upper_bounds : Tightening.t_bounds)
  (lower_bounds : Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (proof_node : ProofTree.t)
  : bool :=
  match proof_node with
  | ProofTree.leaf contradiction => 
      check_contradiction contradiction
                          tableau
                          upper_bounds
                          lower_bounds
  | ProofTree.node split tleft tright =>
      let valid_split := Split.check_split split constraints in
      let bounds := Split.update_bounds_from_split
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

