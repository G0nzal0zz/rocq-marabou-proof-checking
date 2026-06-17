From Stdlib Require Import Reals.
From Stdlib Require Import List.

From mathcomp Require Import all_ssreflect all_algebra.

Require Import split.

Import ListNotations.

Module CertificateSpecs.
  Definition R : numFieldType := rat.
  (* NOTE: Number of items in each row *)
  Parameter (n : nat).
  (* NOTE:  Number of  rows *)
  Parameter (m : nat).
End CertificateSpecs.

Import CertificateSpecs.

Inductive proof_tree : Type :=
  | node : Split.t -> proof_tree -> proof_tree -> proof_tree
  | leaf : seq R -> proof_tree.

