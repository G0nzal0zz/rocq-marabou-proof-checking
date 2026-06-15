From Stdlib Require Import Reals.
From Stdlib Require Import List.

Require Import farkas.
Require Import split.

Import ListNotations.

Inductive proof_tree : Type :=
  | node : Split.t -> proof_tree -> proof_tree -> proof_tree
  | leaf : list R -> proof_tree.

(* TODO: Formalise tableau ??? *)

