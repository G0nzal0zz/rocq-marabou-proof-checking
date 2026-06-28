From mathcomp Require Import all_ssreflect all_algebra.

Require Import certificate_specs.
Require Import relu.

Import CertificateSpecs.

Module Constraint.

Inductive t : Type :=
  | relu : nat -> nat -> nat -> t.

Definition constraint_eqb (c1 c2 : t) : bool :=
  match c1, c2 with 
  | relu b1 f1 aux1, relu b2 f2 aux2 =>
      Nat.eqb b1 b2 && Nat.eqb f1 f2 && Nat.eqb aux1 aux2
  end.

(*let rec check_relu_constraints (cs: t list) (x: real list) =*)
(*    match cs with*)
(*    | [] -> true*)
(*    | Relu (b, f, a) :: cs -> eval_relu b f a x && check_relu_constraints cs x*)

Fixpoint check_relu_constraints (cs : seq t) (x : 'rV[R]_n.+1) : bool :=
  match cs with
  | [::] => true
  | relu b f a :: cs' =>
      (* We must cast the nat indices from the constructor into 'I_n.+1 ordinals *)
      (* using 'nat_of_ord' or an option-check, or we assume a safe lookup helper. *)
      (* Assuming eval_relu handles or expects ordinals, we can use an explicit check: *)
      match (insub b, insub f, insub a) with
      | (Some b_ord, Some f_ord, Some a_ord) =>
          Relu.eval_relu b_ord f_ord a_ord x && check_relu_constraints cs' x
      | _ => false (* Returns false if any index is out of bounds of the vector *)
      end
  end.


End Constraint.
