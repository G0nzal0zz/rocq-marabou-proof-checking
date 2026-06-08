Require Import Reals.
Require Import List.
Import ListNotations.

Inductive split :=
| single : nat -> R -> split
| relu : nat -> nat -> nat -> split.


Inductive proof_tree : Type :=
  | node : split -> proof_tree -> proof_tree -> proof_tree
  | leaf : list R -> proof_tree.

(* TODO: Formalise tableau *)
(* TODO: Formalise constraints *)

(*Inductive constraint_type : Type :=*)
(*| RELU*)
(*| MAX*)
(*| SIGN*)
(*| DISJUNCTION*)
(*| ABSOLUTE_VALUE*)
(*| LEAKY_RELU*)
(*| UNDEFINED.*)
(**)
(*Record constraint : Type := {*)
(*  constraint_type' : constraint_type;*)
(*  vars : list nat*)
(*}.*)
