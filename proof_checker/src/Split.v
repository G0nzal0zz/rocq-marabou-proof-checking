From Stdlib Require Import Reals.

Require Import Certificate.

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

(* TODO: Implement function*)
Definition update_bounds_from_split (lbs: list R) (ubs : list R) (split : split)
  : ((list R * list R)  * (list R * list R)) :=
  ((nil, nil), (nil, nil)).

(*let check_split split constraints = *)
(*    match split with *)
(*    | ReluSplit (b,f,aux) -> List.mem (Relu (b,f,aux)) constraints*)
(*    | _ -> true*)

Definition check_split (split : split) (constraints : list constraint) : bool :=
  true.
