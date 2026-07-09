From mathcomp Require Import all_ssreflect all_algebra.
From Stdlib Require Import Reals.

Require Import certificate_specs.
Require Import util.

Import CertificateSpecs.

Module Tightening.

Inductive bound_type :=
| UPPER
| LOWER.

(* index of value to tighten, new value, bound type (UPPER or LOWER) *)
Definition t : Type := nat * R * bound_type.

Definition t_bounds : Type := 'rV[R]_n.

Definition is_upper (type : bound_type) : bool :=
  match type with
  | UPPER => true
  | _ => false
  end.

Definition is_lower (type : bound_type) : bool :=
  match type with
  | LOWER => true
  | _ => false
  end.

(*let rec update_bounds_by_tightenings (tightenings: t list) (bounds: Real.t list): Real.t list =
   match tightenings with
   | []                    -> bounds
   | (var, value, _) :: tl -> let updated_bounds = set_nth bounds var value in
     update_bounds_by_tightenings tl updated_bounds*)
(*Fixpoint update_bounds_by_tightenings (tightenings : seq t) (bounds : t_bounds) : Tightening.t_bounds :=
  match tightenings with
  | [::] => bounds
  | (var, value, _) :: tl => let updated_bounds := set_nth_vector bounds var value in
      update_bounds_by_tightenings tl updated_bounds
   end.*)


(*update the bounds according to a list of tightenings *)
(*let update_bounds (tightenings: t list) (upper_bounds: Real.t list) (lower_bounds: Real.t list): (Real.t list * Real.t list) =
   let upper_tightenings = List.filter is_upper tightenings in
   let lower_tightenings = List.filter (fun a -> not (is_upper a)) tightenings in
   let updated_upper = update_bounds_by_tightenings upper_tightenings upper_bounds in
   let updated_lower = update_bounds_by_tightenings lower_tightenings lower_bounds in
   (updated_upper, updated_lower)*)
(*Definition update_bounds
  (tightenings : seq t)
  (upper_bounds : t_bounds)
  (lower_bounds : t_bounds)
  : t_bounds * t_bounds :=
  let upper_tightenings := filter (fun '(_, _, btype) => is_upper btype) tightenings in
  let lower_tightenings := filter (fun '(_, _, btype) => is_lower btype) tightenings in
  let updated_upper := update_bounds_by_tightenings upper_tightenings upper_bounds in
  let updated_lower := update_bounds_by_tightenings lower_tightenings lower_bounds in
   (updated_upper, updated_lower).*)

End Tightening.

