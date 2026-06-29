From mathcomp Require Import all_ssreflect all_algebra.

Require Import certificate_specs.
Require Import relu.

Import CertificateSpecs.

Module Constraint.

(* NOTE: Since ReLU is the only possible constraint Constraint.t is just an alias to Relu.t *)
Definition t : Type := Relu.t.

Definition constraint_eqb (c1 c2 : Relu.t) : bool :=
  let '(b1, f1, aux1) := c1 in
  let '(b2, f2, aux2) := c2 in
  Nat.eqb b1 b2 && Nat.eqb f1 f2 && Nat.eqb aux1 aux2.

(*let rec check_relu_constraints (cs: t list) (x: real list) =*)
(*    match cs with*)
(*    | [] -> true*)
(*    | Relu (b, f, a) :: cs -> eval_relu b f a x && check_relu_constraints cs x*)

Fixpoint check_relu_constraints (cs : seq t) (x : 'rV[R]_n) : bool :=
  match cs with
  | [::] => true
  |(b, f, a) :: cs' => Relu.eval_relu b f a x && check_relu_constraints cs' x
  end.

End Constraint.
