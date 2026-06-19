From mathcomp Require Import all_algebra seq.

Require Import certificate_specs.
Require Import constraint.
Require Import util.
Require Import tightening.

Import CertificateSpecs.

Module Split.

Inductive t :=
| single : nat -> R -> t
| relu : nat -> nat -> nat -> t.

(*let update_bounds_from_split (lbs: real list) (ubs: real list) (split: t): *)
(*        ((real list * real list) * (real list * real list)) =*)
(*    match split with*)
(*    | SingleSplit (i, k) -> ((lbs, set_nth ubs i k), (set_nth lbs i k, ubs))*)
(*    | ReluSplit (b, f, aux) ->*)
(*        (* ((set_nth lbs f 0.,  set_nth (set_nth ubs b 0.) f 0.), (set_nth (set_nth lbs b 0.) aux 0., set_nth ubs aux 0.)) *)*)
(*        (* left: inactive phase *)*)
(*        let lbs_l = set_nth lbs f 0. in*)
(*        let ubs_l = set_nth (set_nth ubs b 0.) f 0. in*)
(*        (* right: active phase *)*)
(*        let lbs_r = set_nth (set_nth lbs b 0.) aux 0. in*)
(*        let ubs_r = set_nth ubs aux 0. in*)
(*        (lbs_l, ubs_l), (lbs_r, ubs_r)*)

Definition update_bounds_from_split
  (lbs: Tightening.t_bounds)
  (ubs : Tightening.t_bounds)
  (split : t)
  : ((Tightening.t_bounds * Tightening.t_bounds)  * (Tightening.t_bounds  * Tightening.t_bounds)) :=
  match split with
  | single i k => ((lbs, set_nth_vector ubs i k), (set_nth_vector lbs i k, ubs))
  | relu b f aux => 
    (* left: inactive phase *)
    let lbs_l := set_nth_vector lbs f 0%R in
    let ubs_l := set_nth_vector (set_nth_vector ubs b 0%R) f 0%R in
    (* right: active phase *)
    let lbs_r := set_nth_vector (set_nth_vector lbs b 0%R) aux 0%R in
    let ubs_r := set_nth_vector ubs aux 0%R in
    ((lbs_l, ubs_l), (lbs_r, ubs_r))
  end.

(*let check_split split constraints = *)
(*    match split with *)
(*    | ReluSplit (b,f,aux) -> List.mem (Relu (b,f,aux)) constraints*)
(*    | _ -> true*)

Definition check_split (split : t) (constraints : seq Constraint.t) : bool :=
  match split with
  | relu b f aux => has (Constraint.constraint_eqb (Constraint.relu b f aux)) constraints
  | _ => false
  end.

End Split.
