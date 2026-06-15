From Stdlib Require Import Reals.

Inductive bound_type :=
| UPPER
| LOWER.

(* index of value to tighten, new value, bound type (UPPER or LOWER) *)
Definition t : Type := nat * R * bound_type.

(* update the bounds according to a list of tightenings *)
(*let update_bounds (tightenings: t list) (upper_bounds: Real.t list) (lower_bounds: Real.t list): (Real.t list * Real.t list) =*)
(*   let upper_tightenings = List.filter is_upper tightenings in*)
(*   let lower_tightenings = List.filter (fun a -> not (is_upper a)) tightenings in*)
(*   let updated_upper = update_bounds_by_tightenings upper_tightenings upper_bounds in*)
(*   let updated_lower = update_bounds_by_tightenings lower_tightenings lower_bounds in*)
(*   (updated_upper, updated_lower)*)

Definition update_bounds
  (tightenings : list t)
  (upper_bounds : list R)
  (lower_bounds : list R)
  : list R * list R :=
  (nil, nil).
