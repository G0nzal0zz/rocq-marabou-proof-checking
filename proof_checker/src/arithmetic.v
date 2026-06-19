From mathcomp Require Import all_ssreflect all_algebra.

Require Import certificate_specs.
Require Import farkas.
Require Import util.

Import CertificateSpecs.
Import Farkas.


Module Arithmetic.


(* NOTE: Temporary function to avoid compiling error when multiplying a Stdlib Real and a Mathcomp real. *)

(*Definition mul' (x : R) (y : R') : R :=*)
(*  0.*)
(*Definition poly : Type := farkas.poly R' n.*)
(**)
(*Definition expr : Type := farkas.expr R' n.*)
(**)
(*Definition example_poly : 'rV[R']_n.+1 := \row_(i < n.+1) (0: R').  (* all zeros *)*)
(*Definition example_eq : farkas.expr R' n := farkas.Eq example_poly.*)
(**)
(**)
(*Definition extract_poly' := extract_poly example_eq.*)

(** Helper function for {!compute_combination} *)
(*let rec update_combination (lc: Real.t list) (expl: Real.t list) (tableau: expr list): Real.t list = *)
(*    match expl, tableau with*)
(*    | _, [] | [], _ -> lc*)
(*    | coeff :: expl', row :: tableau' -> update_combination (list_add lc (list_scale (extract_poly row) coeff)) expl' tableau'*)

Fixpoint update_combination_list  (lc expl : seq R) (tableau_list : seq (expr n)) : seq R :=
  match expl, tableau_list with
  | [::], _ => lc
  | _, [::] => lc
  | coeff :: expl', row :: tableau' => 
      let scaled_row := map_vector (fun x => mulq coeff x) (extract_poly row) in
      let next_lc := map2 addq lc (vector_to_seq scaled_row) in
      
      update_combination_list next_lc expl' tableau'
  end.

Definition update_combination (lc expl : seq R) (tableau : system m n) : seq R :=
  update_combination_list lc expl (val tableau).

(** Compute a linear combination of tableau rows with coefficients from the explanation vector `expl` 
    (i.e. a bound-tightening lemma vector or a contradiction in a Leaf node)
    The initial zero vector accumulator has length (len p - 1) because the polynomials have a constant factor, 
    and we want it to be the size of the variable vector
*)
(*let compute_combination (expl: Real.t list) (tableau: expr list): Real.t list =*)
(*    match tableau with*)
(*    | [] -> []*)
(*    | (hd::tl as tableau) -> update_combination (repeat 0. (List.length (extract_poly hd) - 1)) expl tableau*)

Definition compute_combination (expl : seq R) (tableau : system m n) : seq R :=
  match val tableau with
  | [::] => [::]
  | hd :: tl => 
      let initial_size := n.-1 in
      update_combination (nseq initial_size 0%R) expl tableau
  end.

End Arithmetic.

