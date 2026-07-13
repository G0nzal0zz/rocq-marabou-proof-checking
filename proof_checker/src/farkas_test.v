From mathcomp Require Import all_ssreflect all_algebra.
Import GRing.Theory.
Import Num.Theory.

Require Import certificate_specs.
Require Import farkas.
Require Import certificate.
Require Import parsed_certificate.

Import CertificateSpecs ParsedCertificates.

Open Scope ring_scope.

Module FarkasTest.

Definition poly := seq rat.

Inductive expr :=
| Eq  : poly -> expr
| Geq : poly -> expr.

Definition extract_poly (e : expr) : poly :=
  match e with
  | Eq p => p
  | Geq p => p
  end.

Definition system := seq expr.

Fixpoint eval_poly (p : poly) (x : seq rat) : rat :=
  match p, x with
  | a :: p', b :: x' =>
      a * b + eval_poly p' x'
  | [:: a], [::] =>
      a
  | _, _ =>
      0
  end.

Definition eval_expr (e : expr) (x : seq rat) : bool :=
  match e with
  | Eq p =>
      eval_poly p x == 0
  | Geq p =>
      0 <= eval_poly p x
  end.

Fixpoint eval_system (es : system) (x : seq rat) : bool :=
  match es with
  | [::] => true
  | e :: es' =>
      eval_expr e x && eval_system es' x
  end.

Fixpoint p_add (p q : poly) : poly :=
  (*match p, q with*)
  (*| [::], [::] =>*)
  (*    [::]*)
  (*| a :: p', b :: q' =>*)
  (*    (a + b) :: p_add p' q'*)
  (*| _, _ =>*)
  (*    [::]*)
  (*end.*)
  [::].

Fixpoint p_scale (p : poly) (r : rat) : poly :=
  match p with
  | [::] =>
      [::]
  | c :: cs =>
      (r * c) :: p_scale cs r
  end.

Fixpoint is_neg_const (p : poly) : bool :=
  (*match p with*)
  (*| [::] =>*)
  (*    false*)
  (*| [:: c] =>*)
  (*    c < 0*)
  (*| c :: p' =>*)
  (*    (c == 0) && is_neg_const p'*)
  (*end.*)
  false.

Definition sum_polys (ps : seq poly) : poly :=
  (*match ps with*)
  (*| [::] => [::]*)
  (*| p :: ps' => foldl p_add p ps'*)
  (*end.*)
  match ps with
  | p :: ps' => [::]
  | _ => [::]
  end.


Fixpoint scale_exprs (cs : seq rat) (es : system) : seq poly :=
  (*match cs, es with*)
  (*| c :: cs', Eq p :: es' =>*)
  (*    p_scale p c :: scale_exprs cs' es'*)
  (*| c :: cs', Geq p :: es' =>*)
  (*    if 0 <= c then*)
  (*      p_scale p c :: scale_exprs cs' es'*)
  (*    else*)
  (*      p :: scale_exprs cs' es'*)
  (*| [::], Eq p :: es' =>*)
  (*    p :: scale_exprs [::] es'*)
  (*| [::], Geq p :: es' =>*)
  (*    p :: scale_exprs [::] es'*)
  (*| _, _ =>*)
  (*    [::]*)
  (*end.*)
  [::].


Definition mk_cert_poly (cs : seq rat) (es : system) : poly :=
  let test := scale_exprs cs es in
  sum_polys test.

Eval cbv in (scale_exprs [::] [::]).
Eval cbv in (mk_cert_poly [::] [::]).
Definition check_cert (es : system) (cs : seq rat) : bool :=
  is_neg_const (mk_cert_poly cs es).

Definition poly_to_seq (p : Farkas.poly n) : seq rat :=
  [seq p 0 i | i <- enum 'I_(n.+1)].

Definition farkas_expr_to_test_expr (e : Farkas.expr n) : expr :=
  match e with
  | Farkas.Eq p => Eq (poly_to_seq p)
  | Farkas.Geq p => Geq (poly_to_seq p)
  end.

Definition farkas_system_to_test_system (es : Farkas.system m' n) : system :=
  map farkas_expr_to_test_expr (val es).

Definition tuple_to_seq (t : m'.+2.-tuple R) : seq rat :=
  val t.

Let tableau' := Cert.mk_eq_constraints tableau.

Let sys := Cert.mk_system_contradiction tableau' ub lb.
Let contradiction :  (m.+2).-tuple R := [tuple nth 0%R [:: 0%:R; (1873178551 %:R / 10000000000 %:R)%R; 0%:R; -(5319786917 %:R / 5000000000 %:R)%R; 0%:R; 0%:R; -(1873178551 %:R / 10000000000 %:R)%R; 0%:R; (5319786917 %:R / 5000000000 %:R)%R; 0%:R; -(7668856663 %:R / 5000000000 %:R)%R; 0%:R; -(1873178551 %:R / 10000000000 %:R)%R; 0%:R; (5319786917 %:R / 5000000000 %:R)%R; 0%:R; 0%:R; (1873178551 %:R / 10000000000 %:R)%R; 0%:R; -(5319786917 %:R / 5000000000 %:R)%R; 0%:R] i | i < m.+2].
Let cs := Cert.mk_contradiction_certificate contradiction tableau' ub lb.

Time Eval vm_compute in tableau.

Time Eval vm_compute in scale_exprs [::] (farkas_system_to_test_system sys).
End FarkasTest.
