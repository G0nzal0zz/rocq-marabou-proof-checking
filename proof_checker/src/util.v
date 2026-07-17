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

Definition set_nth_vector {A : Type} {n : nat} (v : 'rV[A]_n) (idx : 'I_n) (elem : A) : 'rV[A]_n :=
    \matrix_(i, j) if j == idx then elem else v i j.

(* NOTE: Unused *)
Definition vector_to_seq {n : nat} (v : 'rV[R]_n) : seq R :=
  [seq v 0%R i | i <- enum 'I_n].

Definition drop_last_vector {n : nat} (v : 'rV[R]_n.+1) : 'rV[R]_n :=
  \matrix_(i < 1, j < n) v 0%R (cast_ord (addn1 n) (lshift 1 j)).

