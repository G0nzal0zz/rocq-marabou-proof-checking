From mathcomp Require Import all_ssreflect all_algebra.

Require Import certificate_specs.
Require Import relu.

Import CertificateSpecs.

Module Constraint.

(* NOTE: Since ReLU is the only possible constraint Constraint.t is just an alias to Relu.t *)
Definition t : Type := Relu.t.

Definition constraint_eqb (c1 c2 : Relu.t) : bool := c1 == c2.

(*let rec check_relu_constraints (cs: t list) (x: real list) =*)
(*    match cs with*)
(*    | [] -> true*)
(*    | Relu (b, f, a) :: cs -> eval_relu b f a x && check_relu_constraints cs x*)

Fixpoint check_relu_constraints (cs : seq t) (x : 'rV[R]_n) : bool :=
  match cs with
  | [::] => true
  | c' :: cs' => Relu.eval_relu c'.1.1 c'.1.2 c'.2 x && check_relu_constraints cs' x
  end.

End Constraint.
