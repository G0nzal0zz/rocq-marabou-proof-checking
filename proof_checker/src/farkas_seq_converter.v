From mathcomp Require Import all_ssreflect all_fingroup all_algebra zmodp ssrnum ssrnat matrix eqtype.

Require Import farkas.
Require Import certificate.

Import CertificateSpecs.

Set Implicit Arguments.


Definition poly := seq rat.

Open Scope ring_scope.

Inductive expr :=
| Eq of poly
| Geq of poly.

Print Farkas.poly.

Definition convert_poly (n : nat) (p : poly) : Farkas.poly n :=
  \row_(i < n.+1) nth 0 p i.

Print Farkas.expr.

Fixpoint convert_expr (n : nat) (e : expr) : Farkas.expr n :=
  match e with
  | Eq p  => Farkas.Eq n (convert_poly n p)
  | Geq p => Farkas.Geq n (convert_poly n p)
  end.

Definition system  := seq expr.

Print Farkas.system.

Definition convert_system' (m : nat) (s : system ) (H : size s = m.+2) 
  : Farkas.system m.
Proof.
  (* 1. We still must convert the elements to the target type *)
  pose s_converted := [seq convert_expr n i | i <- s].

  (* 2. We prove the NEW sequence has the correct size *)
  have Hsize : size s_converted == m.+2.
  { (* size_map proves that size s_converted is exactly size s *)
    rewrite size_map. 
    (* Now the goal is size s == m.+2, which we can solve with our hypothesis *)
    apply/eqP. 
    exact: H. }

  (* 3. We build the tuple exactly as before *)
  exact: (Tuple Hsize).
Defined.

(* Let's test with n = 1 (meaning row vectors will have size n.+1 = 2) *)
Definition dummy_poly1 : poly := [:: 0; 0].
Definition dummy_poly2 : poly := [:: 0; 0].

(* Let's build a sample system of 2 expressions (m = 0, so m.+2 = 2) *)
Definition test_sys : system  := [:: Eq dummy_poly1; Geq dummy_poly2].

(* Coq evaluates 'size test_sys' to 2 automatically, so 'by []' closes this instantly *)
Lemma test_sys_has_correct_size : size test_sys = 0.+2.
Proof. by []. Qed.

Definition converted_test_system := 
  convert_system' test_sys test_sys_has_correct_size.

Print converted_test_system.

(* This will print the actual evaluated MathComp Tuple matrix expressions in your compilation buffer *)
(*Eval compute in converted_test_system.*)
