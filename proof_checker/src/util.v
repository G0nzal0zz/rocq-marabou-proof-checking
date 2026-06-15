From Stdlib Require Import List.

Import ListNotations.

Fixpoint set_nth {A : Type} (l : list A) (idx : nat) (elem : A) :=
  match idx, l with
  | _, [] => []
  | O, x :: xs => [elem] ++ xs
  | S n, x :: xs => [x] ++ set_nth xs n elem
  end.

(* NOTE: Like OCaml List.map2, but it does not fail if the lists have unequal lengths *)
Fixpoint map2 {A B C: Type } (f : A -> B -> C) (a : list A) (b : list B) : list C :=
  match a, b with
  | [], _ => []
  | _, []  => []
  | hd :: tl, hd' :: tl' => f hd hd' :: map2 f tl tl'
  end.

