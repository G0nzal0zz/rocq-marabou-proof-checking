From Stdlib Require Import Reals.
From Stdlib Require Import List.

Require Import Farkas.
Require Import Split.

Import ListNotations.


Inductive proof_tree : Type :=
  | node : split -> proof_tree -> proof_tree -> proof_tree
  | leaf : list R -> proof_tree.

(* TODO: Formalise tableau ??? *)

