From mathcomp Require Import all_ssreflect all_algebra matrix.

Require Import certificate_specs.
Require Import farkas.
Require Import tightening.

Import CertificateSpecs.

Module Certificate.

Open Scope ring_scope.

(* create certificate for Geq constraints corresponding to upper bounds *)
(*let rec mk_upper_bound_certificate (lc: Real.t list) = *)
(*  match lc with *)
(*  | [] -> []*)
(*  | hd :: tl -> (if hd >=. 0. then hd else 0. ) :: mk_upper_bound_certificate tl*)
Definition mk_upper_bound_certificate (lc : n.-tuple R) : n.-tuple R :=
  [tuple
    let val := tnth lc j in
    if val >= 0%R then val else 0%R
  | j < n].

(* create certificate for Geq constraints corresponding to lower bounds *)
(*let rec mk_lower_bound_certificate (lc: Real.t list) = *)
(*  match lc with *)
(*  | [] -> []*)
(*  | hd :: tl -> (if hd <. 0. then (-. hd) else 0. ) :: mk_lower_bound_certificate tl*)
Definition mk_lower_bound_certificate (lc : n.-tuple R) : n.-tuple R :=
  [tuple
    let val := tnth lc j in
    if val < 0%R then - val else 0%R
  | j < n].

(*
  Create a polynomial of size (size + 1) that represents the bound of variable i:
  all coefficients are 0, except at index i where it is  `coeff` (should be 1 for a lower bound
  and -1 for an upper bound). The constant is the value of the bound.
*)
(*let rec mk_bound_poly (size: int) (i: int) (coeff: Real.t) (bound: Real.t): Real.t list =*)
(*  if size < 0 then []*)
(*  else if size = 0 then [bound]*)
(*  else if (i = 0) then coeff :: mk_bound_poly (size - 1) (i - 1) coeff bound*)
(*  else 0. :: mk_bound_poly (size - 1) (i - 1) coeff bound*)
(*
  WARN: For some reason I couldn't use the row notation for the following function.
  I should try to make it work as it improves readibilit.
*)
Definition mk_bound_poly (n : nat) (i : nat) (coeff : R) (bound : R) : Farkas.poly n :=
  matrix_of_fun matrix_key (fun _ (j : 'I_n.+1) =>
    if (j : nat) == n then bound
    else if (j : nat) == i then coeff
    else 0%R).

(* remove iterator to make it easier to prove *)
(*let rec mk_upper_bounds_constraints size upper_bounds = *)
(*  match upper_bounds with*)
(*  | [] -> []*)
(*  | u::bounds -> let i = size - (List.length upper_bounds) in*)
(*      Geq (mk_bound_poly size i (-1.) u) :: mk_upper_bounds_constraints size bounds*)

Definition mk_upper_bounds_constraints (upper_bounds : Tightening.t_bounds) : n.-tuple (Farkas.expr n) :=
  [tuple (Farkas.Geq n (mk_bound_poly n (j : nat) (-1)%R (upper_bounds 0%R j))) | j < n].

(* remove iterator to make it easier to prove *)
(*let rec mk_lower_bounds_constraints size lower_bounds = *)
(*  match lower_bounds with*)
(*  | [] -> []*)
(*  | l::bounds -> let i = size - (List.length lower_bounds) in*)
(*    Geq (mk_bound_poly size i 1. (-. l)) :: mk_lower_bounds_constraints size bounds*)
Definition mk_lower_bounds_constraints (lower_bounds : Tightening.t_bounds) : n.-tuple (Farkas.expr n) :=
  [tuple (Farkas.Geq n (mk_bound_poly n (j : nat) 1%R (lower_bounds 0%R j))) | j < n].

(*
  transform the tableau into a list of Eq expressions, with
  an added 0. for the constant at the end
*)
(*let rec mk_eq_constraints (tableau: Real.t list list): expr list =*)
(*  match tableau with *)
(*  | hd :: tl -> Eq (hd @ [0.]) :: mk_eq_constraints tl*)
(*  | [] -> []*)
Definition mk_eq_constraints (tableau : (m.+2).-tuple ('rV[R]_n)) : (m.+2).-tuple (Farkas.expr n) :=
  map_tuple (fun hd =>
  let extended_vector := row_mx hd 0 in (* Adding the constant at the end of each vector.*)
    let typed_vector := castmx (erefl 1, addn1 n) extended_vector in
    Farkas.Eq n typed_vector
  ) tableau.


(** Create Geq constraints corresponding to the variable bounds.
*)
(*let mk_geq_constraints (upper_bounds: Real.t list) (lower_bounds: Real.t list): expr list =*)
(*  let size = List.length upper_bounds in*)
(*  (mk_upper_bounds_constraints size upper_bounds) @ (mk_lower_bounds_constraints size lower_bounds)*)

Definition mk_geq_constraints (upper_bounds lower_bounds : Tightening.t_bounds) : (n + n).-tuple (Farkas.expr n) :=
  cat_tuple (mk_upper_bounds_constraints upper_bounds) (mk_lower_bounds_constraints lower_bounds).

(* Create the polynomial representation of the linear constraints from the matrix representation *)
(*let mk_system_contradiction (tableau: expr list) (upper_bounds: Real.t list) (lower_bounds: Real.t list): expr list =*)
(*  tableau @ (mk_geq_constraints upper_bounds lower_bounds)*)
Definition mk_system_contradiction
  (tableau : Farkas.system m n)
  (upper_bounds lower_bounds : Tightening.t_bounds)
  : (m.+2 + (n + n)).-tuple (Farkas.expr n) :=
  cat_tuple tableau (mk_geq_constraints upper_bounds lower_bounds).

End Certificate.
