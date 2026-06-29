From mathcomp Require Import all_ssreflect all_algebra.

Require Import certificate_specs.
Require Import farkas.
Require Import util.

Import CertificateSpecs.
Import Farkas.

Module Arithmetic.

(** Helper function for {!compute_combination} *)
(*let rec update_combination (lc: Real.t list) (expl: Real.t list) (tableau: expr list): Real.t list = *)
(*    match expl, tableau with*)
(*    | _, [] | [], _ -> lc*)
(*    | coeff :: expl', row :: tableau' -> update_combination (list_add lc (list_scale (extract_poly row) coeff)) expl' tableau'*)

(** Compute a linear combination of tableau rows with coefficients from the explanation vector `expl`
    (i.e. a bound-tightening lemma vector or a contradiction in a Leaf node)
    The initial zero vector accumulator has length (len p - 1) because the polynomials have a constant factor,
    and we want it to be the size of the variable vector
*)
(*let compute_combination (expl: Real.t list) (tableau: expr list): Real.t list =*)
(*    match tableau with*)
(*    | [] -> []*)
(*    | (hd::tl as tableau) -> update_combination (repeat 0. (List.length (extract_poly hd) - 1)) expl tableau*)

Definition compute_combination (expl : (m.+2).-tuple R) (tableau : system m n) : n.-tuple R :=
  let raw_vector_sum : 'rV[R]_n :=
    \sum_(i < m.+2) (tnth expl i *: drop_last_vector (extract_poly (tnth tableau i))) in
  [tuple raw_vector_sum 0 j | j < n].

(*let rec dot_product x y =*)
(*match x, y with*)
(*    | [], [] -> 0.*)
(*    | x_hd :: x_tl, y_hd :: y_tl -> x_hd *. y_hd +. (dot_product x_tl y_tl)*)
(*    | _ -> 0.*)
(**)
(*let rec is_in_kernel tableau x =*)
(*    match tableau with*)
(*    | [] -> true*)
(*    | row :: rows -> dot_product row x = 0. && is_in_kernel rows x*)

Definition is_in_kernel (tableau : (m.+2).-tuple ('rV[R]_n)) (x : 'rV[R]_n) : bool :=
  (* 1. Build the matrix out of the tuple of rows *)
  let tab_mx := \matrix_(i, j) (tnth tableau i) 0 j in

  (* 2. Transpose x to make it a column vector, multiply, and check for zero *)
  (tab_mx *m (trmx x)) == 0.


End Arithmetic.

