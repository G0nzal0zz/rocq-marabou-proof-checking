From Stdlib Require Import List.

From mathcomp Require Import all_ssreflect all_algebra.


Require Import certificate_specs.

Import CertificateSpecs.

Import ListNotations.


Fixpoint set_nth {A : Type} (l : list A) (idx : nat) (elem : A) :=
  match idx, l with
  | _, [] => []
  | O, x :: xs => [elem] ++ xs
  | S n, x :: xs => [x] ++ set_nth xs n elem
  end.

Definition set_nth_vector {A : Type} {n : nat} (v : 'rV[A]_n) (idx : nat) (elem : A) : 'rV[A]_n :=
  if insub idx is Some col then
    \matrix_(i, j) if j == col then elem else v i j
  else v.

(* NOTE: Like OCaml List.map2, but it does not fail if the lists have unequal lengths *)
Fixpoint map2 {A B C: Type } (f : A -> B -> C) (a : list A) (b : list B) : list C :=
  match a, b with
  | [], _ => []
  | _, []  => []
  | hd :: tl, hd' :: tl' => f hd hd' :: map2 f tl tl'
  end.

Definition map_vector  (f : R -> R) (v : 'rV[R]_n.+1) : 'rV[R]_n.+1 :=
  (* Reconstruct the row vector by applying 'f' to every element at index (i, j) *)
  \row_(j < n.+1) f (v 0%R j).
From mathcomp Require Import all_ssreflect all_algebra.

Definition map2_vector {R : numFieldType} {n : nat} (f : R -> R -> R) (u v : 'rV[R]_n.+1) : 'rV[R]_n.+1 :=
  (* Element-wise transformation across all columns *)
  \row_(j < n.+1) f (u 0%R j) (v 0%R j).

Definition vector_to_seq {n : nat} (v : 'rV[R]_n) : seq R :=
  [seq v 0%R i | i <- enum 'I_n].

Definition drop_last_vector (v : 'rV[R]_n.+1) : 'rV[R]_n :=
  \matrix_(i < 1, j < n) v 0%R (cast_ord (addn1 n) (lshift 1 j)).
