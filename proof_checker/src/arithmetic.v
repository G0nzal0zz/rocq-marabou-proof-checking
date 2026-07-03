From mathcomp Require Import all_ssreflect all_algebra.

Require Import certificate_specs.
Require Import farkas.
Require Import util.

Import CertificateSpecs.
Import Farkas.

Module Arithmetic.


(*let rec bounded xs us ls = *)
(*    match xs, us, ls with*)
(*    | [], [], [] -> true*)
(*    | x::xs, u::us, l::ls -> l <=. x && x <=. u && bounded xs us ls*)
(*    | _, _, _ -> true*)
Definition bounded (v ub lb: 'rV[R]_n) :=
  [forall i : 'I_n, (lb 0 i <= v 0 i) && (v 0 i <= ub 0 i)].

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

Definition cv_addn1_succ: 'cV[R]_(n+1) -> 'cV[R]_n.+1 :=
  (castmx (addn1 n, erefl)).

Definition rv_addn1_succ: 'rV[R]_(n+1) -> 'rV[R]_n.+1 :=
  (castmx (erefl, addn1 n)).

(*let rec dot_product x y =
match x, y with
    | [], [] -> 0.
    | x_hd :: x_tl, y_hd :: y_tl -> x_hd *. y_hd +. (dot_product x_tl y_tl)
    | _ -> 0.*)
Definition dot_product (p : 'rV[R]_n.+1) (x : 'cV[R]_n) : R :=
  (p *m (cv_addn1_succ (col_mx x 1%:M))) ord0 ord0.

Definition check_dot_product_zero (p : 'rV[R]_n.+1) (x : 'cV[R]_n) : bool :=
  dot_product p x == 0.

(*let rec is_in_kernel tableau x =*)
(*    match tableau with*)
(*    | [] -> true*)
(*    | row :: rows -> dot_product row x = 0. && is_in_kernel rows x*)
Definition is_in_kernel (tableau : (m.+2).-tuple ('rV[R]_n)) (x : 'rV[R]_n) : bool :=
  let padded_tableau := map_tuple (fun hd => Arithmetic.rv_addn1_succ(row_mx hd 0)) tableau in
  all (check_dot_product_zero ^~ (trmx x)) (val padded_tableau).


End Arithmetic.

