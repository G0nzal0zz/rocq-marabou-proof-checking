(**
  Disclaimer: The contents of this file were extracted from the
  proof-certs-translation repository:
  https://github.com/lstrsrmn/proof-certs-translation/tree/main
*)
From mathcomp Require Import all_ssreflect all_fingroup all_algebra zmodp ssrnum ssrnat matrix eqtype.
Import GRing.Theory.
Require Import farkas_soundness.


Set Implicit Arguments.

Section Farkas.

Definition poly := seq rat.

Open Scope ring_scope.

Inductive expr :=
| Eq of poly
| Geq of poly.

Print FarkasSoundness.poly.

Definition convert_poly (n : nat) (p : poly) : FarkasSoundness.poly rat n :=
  \row_(i < n.+1) nth 0 p i.

Print FarkasSoundness.expr.

Fixpoint convert_expr (n : nat) (e : expr) : FarkasSoundness.expr rat n :=
  match e with
  | Eq p  => FarkasSoundness.Eq (convert_poly n p)
  | Geq p => FarkasSoundness.Geq (convert_poly n p)
  end.

Definition system (n : nat) := seq expr.

Print FarkasSoundness.system.

Definition convert_system' (n m : nat) (s : system n) (H : size s = m.+2) 
  : FarkasSoundness.system rat n m.
Proof.
  (* 1. We still must convert the elements to the target type *)
  pose s_converted := [seq convert_expr n i | i <- s].
  
  (* 2. We prove the NEW sequence has the correct size *)
  have Hsize : size s_converted == m.+2.
  { (* size_map proves that size s_converted is exactly size s *)
    rewrite size_map. 
    (* Now the goal is size s == m.+2, which we can solve with our hypothesis *)
    apply/eqP. 
    exact: H.
  }
    
  (* 3. We build the tuple exactly as before *)
  exact: (Tuple Hsize).
Defined.


(* n = 1 (meaning row vectors will have size n.+1 = 2) *)
Definition n := 1%nat.

(* m = 0 (meaning system will have size m.+2 = 2) *)
Definition m := 0%nat. 

Definition dummy_poly1 : poly := [:: 0; 0].
Definition dummy_poly2 : poly := [:: 0; 0].


Definition dummy_sys : system n := [:: Eq dummy_poly1; Geq dummy_poly2].

Lemma dummy_sys_has_correct_size : size dummy_sys = m.+2.
Proof. simpl. reflexivity. Qed.


Definition converted_dummy_system := 
  convert_system' dummy_sys dummy_sys_has_correct_size.

Print converted_dummy_system.

End Farkas.

