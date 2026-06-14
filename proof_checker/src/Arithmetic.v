From Stdlib Require Import Reals.
From Stdlib Require Import List.
From mathcomp Require Import all_ssreflect all_algebra.

Require Import Farkas.
Require Import Util.

Import ListNotations.

Section Arithmetic.

Variable (R' : numDomainType).
Variable (n : nat).

Definition expr : Type := Farkas.expr R' n.

(** Helper function for {!compute_combination} *)
(*let rec update_combination (lc: Real.t list) (expl: Real.t list) (tableau: expr list): Real.t list = *)
(*    match expl, tableau with*)
(*    | _, [] | [], _ -> lc*)
(*    | coeff :: expl', row :: tableau' -> update_combination (list_add lc (list_scale (extract_poly row) coeff)) expl' tableau'*)


(* WARN: `extrac_poly` uses MathComp reals, while the rest of the variables use Stdlib reals,
  only of definition of reals should be used to maintain consistency.
*)
Fixpoint update_combination (lc expl : list R) (tableau : list expr) : list R :=
  match expl, tableau with
  | _, [] => lc
  | [], _ => lc
  | coeff :: expl', row :: tableau' => update_combination (map2 Rplus lc (map (fun x => x * coeff) (extract_poly row))) expl' tableau
  end.

(** Compute a linear combination of tableau rows with coefficients from the explanation vector `expl` 
    (i.e. a bound-tightening lemma vector or a contradiction in a Leaf node) 
    The initial zero vector accumulator has length (len p - 1) because the polynomials have a constant factor, 
    and we want it to be the size of the variable vector
*)
(*let compute_combination (expl: Real.t list) (tableau: expr list): Real.t list =*)
(*    match tableau with*)
(*    | [] -> []*)
(*    | (hd::tl as tableau) -> update_combination (repeat 0. (List.length (extract_poly hd) - 1)) expl tableau*)

Definition compute_combination (expl : list R) (tableau : list expr) : list R :=
  match tableau with
  | [] => []
  | (hd :: tl) => update_combination (repeat 0 (length (Farkas.extract_poly hd) - 1)) expl tableau
  end.

End Arithmetic.

