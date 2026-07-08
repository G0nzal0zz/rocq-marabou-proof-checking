From mathcomp Require Import all_ssreflect all_algebra.

Require Import certificate_specs.
Require Import farkas.
Require Import arithmetic.
Require Import constraint.
Require Import tightening.

Import CertificateSpecs.
Import Farkas.

Module Sat.

(*let unsat tableau upper_bounds lower_bounds relu_constraints x =*)
(*    (is_in_kernel tableau x &&*)
(*    bounded x upper_bounds lower_bounds &&*)
(*    check_relu_constraints relu_constraints x) = false*)
Definition unsat
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (upper_bounds lower_bounds : Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (x : 'rV[R]_n) : bool :=
  (Arithmetic.is_in_kernel tableau x && Arithmetic.bounded x upper_bounds lower_bounds && Constraint.check_relu_constraints constraints x) == false.

(* let sat tableau upper_bounds lower_bounds relu_constraints x =
    (is_in_kernel tableau x &&
    bounded x upper_bounds lower_bounds &&
    check_relu_constraints relu_constraints x) *)
Definition sat
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (upper_bounds lower_bounds : Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (x : 'rV[R]_n) : bool :=
  Arithmetic.is_in_kernel tableau x && Arithmetic.bounded x upper_bounds lower_bounds && Constraint.check_relu_constraints constraints x.


(*lemma unsat_not_sat tableau upper_bounds lower_bounds relu_constraints x =
    unsat tableau upper_bounds lower_bounds relu_constraints x
    = not (sat tableau upper_bounds lower_bounds relu_constraints x)*)
Lemma unsat_not_sat
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (upper_bounds lower_bounds : Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (x : 'rV[R]_n) :
  unsat tableau upper_bounds lower_bounds constraints x =
  (sat tableau upper_bounds lower_bounds constraints x == false).
Proof.
  auto.
Qed.

End Sat.

