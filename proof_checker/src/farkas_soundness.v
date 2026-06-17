(**
  Disclaimer: The contents of this file were extracted from the
  proof-certs-translation repository:
  https://github.com/lstrsrmn/proof-certs-translation/tree/main
*)
From mathcomp Require Import all_ssreflect all_fingroup all_algebra zmodp ssrnum ssrnat matrix eqtype.
(* Require Import utils algebra_ext matrix_ext. *)
Import GroupScope Order.TTheory GRing.Theory Num.Theory.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.

Module FarkasSoundness.

Section Farkas.
(* Variable (R : realFieldType). *)
Variable (R : numDomainType).
Variable (n : nat).
Implicit Type x : 'cV[R]_n.
Implicit Type p : 'rV[R]_n.+1.
Variable (m : nat).

(* NOTE:'rV[R]_n.+1 is the MathComp type of row vectors over R of length n + 1. *)
Definition poly (n : nat) : Type := 'rV[R]_n.+1.


Open Scope ring_scope.

Inductive expr :=
  | Eq of poly n
  | Geq of poly n.


Definition expr_eq e1 e2 :=
  match e1, e2 with
  | Eq p1, Eq p2 => p1 == p2
  | Geq p1, Geq p2 => p1 == p2
  | _, _ => false
  end.

(* NOTE: Proof that denotes that expr is decidable (IMPORTANT FOR MATHCOMP) *)
Lemma expr_eqP : Equality.axiom expr_eq.
Proof.
  move=> e1 e2.
  apply: (iffP idP).
  case: e1=> p1; case: e2=> p2;
  rewrite /expr_eq //= => /eqP -> //=.
  move=> ->.
  case: e2 => p2;
  rewrite /expr_eq;
  by apply/eqP.
Qed.

HB.instance Definition _ := hasDecEq.Build expr expr_eq.

Definition extract_poly e : poly n :=
  match e with
  | Eq p => p
  | Geq p => p
  end.

(* NOTE: The following coercion tells Rocq that a expr can be converted into a polynomial *)
Coercion extract_poly : expr >-> poly.

(*
  NOTE:
   - `m.+2`: Is equal to S (S n), equivalently `m.+1` is equal to S n. In simple terms `m.+2` is m + 2.
   - `-tuple expr`: A tuple of type `expr` and length `m.+2`, meaning that there are at least 2 items in the tuple.
*)
Definition system := m.+2.-tuple expr.

Let cv_addn1_succ: 'cV[R]_(n+1) -> 'cV[R]_n.+1 :=
  (castmx (addn1 n, erefl)).

Definition rv_addn1_succ: 'rV[R]_(n+1) -> 'rV[R]_n.+1 :=
  (castmx (erefl, addn1 n)).

Definition eval_poly_def p x := (p *m (cv_addn1_succ (col_mx x 1%:M))) ord0 ord0.

Fact eval_poly_key : unit. Proof. by []. Qed.

Definition eval_poly := locked_with eval_poly_key eval_poly_def.

Canonical eval_poly_unlockable := [unlockable fun eval_poly].

Definition eval_expr e x : bool :=
  match e with
  | Eq p => eval_poly p x == 0%R
  | Geq p => 0%R <= eval_poly p x
  end.

Definition eval_system (es : system) x : bool := all (eval_expr ^~ x) es.

Definition is_neg_const p : bool :=
  [forall i : 'I_n.+1, if i == ord_max then p 0 i < 0 else p 0 i == 0].

(** This is not a nice solution, should look into it **)
Definition scale_expr (c : R) (e : expr) : expr :=
  match e with
  | Eq p => Eq (c *: p)
  | Geq p => if c >= 0 then Geq (c *: p) else Geq p
  end.

Definition scale_exprs (cs : m.+2.-tuple R) (es : system) : system :=
  map (fun '(c, e) => scale_expr c e) (zip_tuple cs es).

Definition sum_polys (es : system) : poly n :=
  \sum_(e <- es) extract_poly e.

Definition mk_cert_poly (cs : m.+2.-tuple R) (es : system) : poly n :=
  sum_polys (scale_exprs cs es).

Definition check_cert (es : system) (cs : m.+2.-tuple R) : bool :=
  is_neg_const (mk_cert_poly cs es).

Lemma col_mx_max1 x : cv_addn1_succ (col_mx x 1%:M) ord_max ord0 = 1.
Proof.
  rewrite /cv_addn1_succ castmxE (_ : ord_max = cast_ord (addn1 n) (rshift n ord0)) //=.
  by rewrite cast_ordK col_mxEd cast_ord_id mxE.
  apply/val_inj.
  by rewrite //= addn0.
Qed.

Lemma eval_scale_pull p (r : R) x : eval_poly (r *: p) x = r * eval_poly p x.
Proof.
  rewrite unlock /eval_poly !mxE big_distrr /= (eq_bigr (fun j => r * (p ord0 j * cv_addn1_succ (col_mx x 1%:M) j ord0))) // => i _.
  by rewrite mulrA !mxE.
Qed.

Lemma eval_zero_scale p (c : R) x : eval_poly p x = 0 -> eval_poly (c *: p) x = 0.
Proof.
  move=> H.
  by rewrite eval_scale_pull H mulr0.
Qed.

Lemma eval_non_neg_scale p (c : R) x :eval_poly p x >= 0 -> c >= 0 -> eval_poly (c *: p) x >= 0.
Proof.
  move=> Hp Hc.
  rewrite eval_scale_pull mulr_ge0 //=.
Qed.

Lemma cert_is_neg cs es x :
  check_cert es cs -> eval_poly (mk_cert_poly cs es) x < 0.
Proof.
  rewrite /check_cert /is_neg_const unlock /eval_poly !mxE big_ord_recr /= col_mx_max1 mulr1 => /forallP H.
  rewrite big1.
  rewrite add0r.
  move: (H ord_max).
  by rewrite eq_refl.
  move=> i _.
  move: (H (widen_ord (leqnSn n) i)).
  rewrite ifF => [/eqP -> | ].
  by rewrite mul0r.
  apply/eqP => H'.
  have := ltn_ord i.
  move: H' => /(f_equal val) /= ->.
  by rewrite ltnn.
Qed.

Lemma eval_poly0 x : eval_poly 0 x = 0.
Proof.
  by rewrite unlock /eval_poly mul0mx !mxE.
Qed.

Lemma eval_poly_morph x :
  {morph eval_poly^~ x : p q / p + q >-> p + q}.
Proof.
  move=> p q.
  rewrite unlock /eval_poly !mxE -big_split /=.
  apply eq_bigr => i _.
  by rewrite -mulrDl !mxE.
Qed.

Lemma zip_mem_in (a : nat) (A B : eqType) (cs : a.-tuple A) (es : a.-tuple B) (c : A) (e : B) :
  (c, e) \in zip cs es -> (c \in cs) && (e \in es).
Proof.
  elim E: a es cs => [ | a' IH] es cs.
  by rewrite (size0nil (size_tuple es)) (size0nil (size_tuple cs)) /= in_nil.
  case: cs es => /= cs Hcs es.
  case: cs Hcs => //= c' cs Hcs.
  case: es => //= es Hes.
  case: es Hes => //= e' es Hes.
  rewrite in_cons.
  case/orP => [/eqP [-> ->] | Hin].
  by rewrite !in_cons !eqxx /=.
  move: (IH (Tuple Hes) (Tuple Hcs) Hin) => /=.
  rewrite !in_cons => /andP [-> ->].
  by rewrite !orbT.
Qed.

Lemma solution_is_not_neg cs es x : eval_system es x -> eval_poly (mk_cert_poly cs es) x >= 0.
Proof.
  (* rewrite /eval_system => /allP H. *)
  rewrite /eval_system /mk_cert_poly /sum_polys (big_morph (eval_poly^~ x) (eval_poly_morph x) (eval_poly0 x)) /scale_exprs big_seq /= => /allP H.
  apply sumr_ge0 => k /mapP [ce Hce] ->.
  case: ce Hce => c e.
  move=> /zip_mem_in /andP [Hc He].
  move: (H e He).
  rewrite /eval_expr /scale_expr.
  case e => p Hep.
  by move/eqP:Hep => /(eval_zero_scale c) ->.
  case E: (0 <= c).
  apply eval_non_neg_scale => //.
  by have := H e He.
Qed.

Theorem farkas_unsat (es:system) (cs : m.+2.-tuple R) x :
  check_cert es cs -> eval_system es x = false.
Proof.
  move=> /(cert_is_neg x).
  case E: (eval_system es x) => //=.
  move: E => /(solution_is_not_neg cs) E /lt_le_trans => /(_ (eval_poly (mk_cert_poly cs es ) x)) => /(_ E).
  by rewrite lt_irreflexive.
Qed.

End Farkas.

(* NOTE: This section aim is to demonstrate that the inductive definition `system` is the same as a matrix *)
Section Mat.

Open Scope ring_scope.

Variable (R : numDomainType).
Variable (m n : nat).
Variable (A : 'M[R]_(m,n)).
Variable (l x u : 'cV[R]_n).

Definition mat_to_system A l u x : system R n m :=
  tcast (addn2 m) (
  cat_tuple
  [tuple (Eq (rv_addn1_succ (row_mx (row i A) 0%:M))) | i < m]
  [tuple (Geq (rv_addn1_succ (row_mx (u-x)^T 0%:M))); (Geq (rv_addn1_succ (row_mx (x-l)^T 0%:M)))]).

Definition poly_to_rv (p : poly R n) : 'rV[R]_n :=
  lsubmx (castmx (erefl, esym (addn1 n)) p).


Lemma leqW2 (a : nat) : (a <= a.+2)%N.
Proof.
  apply leqW.
  by apply leqnSn.
Qed.

Definition system_to_mat (es : system R n m) : ('M[R]_(m,n) * 'cV[R]_n * 'cV[R]_n) :=
  (\matrix_(i < m) poly_to_rv (extract_poly (tnth es (widen_ord (leqW2 m) i))),
    (poly_to_rv (extract_poly (tnth es (ord_max - 1))))^T,
    (poly_to_rv (extract_poly (tnth es ord_max)))^T
  ).

(* NOTE: Specifying the order of mathcomp matrices. *)
Definition lermx (mx1 mx2 : 'M[R]_(m,n)) :=
    [forall i : 'I_m * 'I_n, mx1 i.1 i.2 <= mx2 i.1 i.2].

End Mat.
Open Scope ring_scope.

Notation "A <=m B" := (lermx A B) (at level 70, no associativity) : ring_scope.

Definition eval_mat {R : numDomainType} {m n} (A : 'M[R]_(m,n)) (l x u : 'cV[R]_n) : bool :=
  (A *m x == 0) && (l <=m x) && (x <=m u).

(* WARN: The following lemma is unfinished, is there any reason for it? *)
Lemma mat_system_inv {R : numDomainType} {m n} (A : 'M[R]_(m,n)) (l u x : 'cV[R]_n)
(es : system R n m) : system_to_mat (mat_to_system A l x u) = (A, l, u).
Proof.
  rewrite /system_to_mat.
  apply congr2.
  apply congr2.
  rewrite /mat_to_system.
  apply/matrixP => i j.
  rewrite !mxE !castmxE /= esymK.
  Check tnth_lshift.
Admitted.

(* WARN: The following lemma is unfinished, is there any reason for it? *)
Lemma poly_equiv {R : numDomainType} {m n} (A : 'M[R]_(m,n)) (l x u : 'cV[R]_n) (es : system R n m) :
  eval_mat A l x u <-> eval_system es x.
Proof.
  split.
  rewrite /eval_mat /eval_system.
Admitted.

End FarkasSoundness.
