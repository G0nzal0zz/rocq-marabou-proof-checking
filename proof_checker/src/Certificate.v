From Stdlib Require Import Reals.
From Stdlib Require Import List.
Import ListNotations.
Require Import Farkas.

Inductive split :=
| single : nat -> R -> split
| relu : nat -> nat -> nat -> split.

Inductive proof_tree : Type :=
  | node : split -> proof_tree -> proof_tree -> proof_tree
  | leaf : list R -> proof_tree.

(* TODO: Formalise constraints correctly*)
Inductive constraint : Type :=
  | node' : split -> constraint -> constraint -> constraint
  | leaf' : list R -> constraint.

(* TODO: Formalise tableau ???*)

