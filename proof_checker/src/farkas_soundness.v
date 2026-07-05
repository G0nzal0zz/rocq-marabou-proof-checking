(**
  Disclaimer: The contents of this file were extracted from the
  proof-certs-translation repository:
  https://github.com/lstrsrmn/proof-certs-translation/tree/main
*)
From mathcomp Require Import all_ssreflect all_fingroup all_algebra zmodp ssrnum ssrnat matrix eqtype.
(* Require Import utils algebra_ext matrix_ext. *)
From HB Require Import structures.

Require Import certificate_specs.
Require Import farkas.
Require Import arithmetic.

Import GroupScope Order.TTheory GRing.Theory Num.Theory.
Import CertificateSpecs.
(* NOTE: Open the Farkas namespace to access its definitions directly without using qualified paths (e.g., Farkas.foo). *)
Import Farkas.

Set Implicit Arguments.
Unset Strict Implicit.

Module FarkasSoundness.

Section Farkas.

Implicit Type x : 'cV[R]_n.
Implicit Type p : 'rV[R]_n.+1.

Definition expr_eq (e1 e2 : expr n) :=
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

HB.instance Definition _ := hasDecEq.Build (expr n) expr_eqP.

(* NOTE:
   In order to compute the value of the polynomial, we need to compute the matrix multiplication (`*m`) between `p` and `x`.
   For matrix multiplication, the number of columns of the first matrix must match the number of rows of the second.
   Since `p` has `n.+1` columns and `x` only has `n` rows, we stack a scalar `1` to the bottom of `x` (using `col_mx`) to make its row count match.
   Because the result of a matrix multiplication is always a matrix, even if it only contains a single element (a 1x1 matrix in our case), we extract the final scalar value using `ord0 ord0`.
*)

(*Fact eval_poly_key : unit. Proof. by []. Qed.*)
(**)
(*Definition eval_poly := locked_with eval_poly_key eval_poly_def.*)
(**)
(*Canonical eval_poly_unlockable := [unlockable fun eval_poly].*)

Definition eval_expr {n : nat} (e : expr n) (x : 'cV[R]_n) : bool :=
  match e with
  | Eq p => Arithmetic.dot_product p (Arithmetic.cv_addn1_succ (col_mx x 1%:M)) == 0%R
  | Geq p => 0%R <= Arithmetic.dot_product p (Arithmetic.cv_addn1_succ (col_mx x 1%:M))
  end.

(* NOTE: Using `m` as an explicit argument to facilitate generating proofs around eval_system (e.g., tableau_reduction_soundness). *)
Definition eval_system {m n : nat} (es : (m).-tuple (expr n)) (x : 'cV[R]_n) : bool := all (eval_expr ^~ x) es.

Lemma col_mx_max1 x : Arithmetic.cv_addn1_succ (col_mx x 1%:M) ord_max ord0 = 1.
Proof.
  rewrite /Arithmetic.cv_addn1_succ castmxE (_ : ord_max = cast_ord (addn1 n) (rshift n ord0)) //=.
  by rewrite cast_ordK col_mxEd cast_ord_id mxE.
  apply/val_inj.
  by rewrite //= addn0.
Qed.

Lemma eval_scale_pull p (r : R) x : Arithmetic.dot_product (r *: p) (Arithmetic.cv_addn1_succ (col_mx x 1%:M))  = r * Arithmetic.dot_product p (Arithmetic.cv_addn1_succ (col_mx x 1%:M)).
Proof.
  rewrite /Arithmetic.dot_product !mxE big_distrr /= (eq_bigr (fun j => r * (p ord0 j * Arithmetic.cv_addn1_succ (col_mx x 1%:M) j ord0))) // => i _.
  by rewrite mulrA !mxE.
Qed.

Lemma eval_zero_scale p (c : R) x : Arithmetic.dot_product p (Arithmetic.cv_addn1_succ (col_mx x 1%:M))  = 0 -> Arithmetic.dot_product (c *: p) (Arithmetic.cv_addn1_succ (col_mx x 1%:M)) = 0.
Proof.
  move=> H.
  by rewrite eval_scale_pull H mulr0.
Qed.

Lemma eval_non_neg_scale p (c : R) x :Arithmetic.dot_product p (Arithmetic.cv_addn1_succ (col_mx x 1%:M)) >= 0 -> c >= 0 -> Arithmetic.dot_product (c *: p) (Arithmetic.cv_addn1_succ (col_mx x 1%:M)) >= 0.
Proof.
  move=> Hp Hc.
  rewrite eval_scale_pull mulr_ge0 //=.
Qed.

Lemma cert_is_neg cs es x :
  check_cert es cs -> Arithmetic.dot_product (mk_cert_poly cs es) (Arithmetic.cv_addn1_succ (col_mx x 1%:M)) < 0.
Proof.
  rewrite /check_cert /is_neg_const /Arithmetic.dot_product !mxE big_ord_recr /= col_mx_max1 mulr1 => /forallP H.
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

Lemma eval_poly0 x : Arithmetic.dot_product 0 (Arithmetic.cv_addn1_succ (col_mx x 1%:M)) = 0.
Proof.
  by rewrite /Arithmetic.dot_product mul0mx !mxE.
Qed.

Lemma eval_poly_morph x :
  {morph Arithmetic.dot_product^~ (Arithmetic.cv_addn1_succ (col_mx x 1%:M)) : p q / p + q >-> p + q}.
Proof.
  move=> p q.
  rewrite /Arithmetic.dot_product !mxE -big_split /=.
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

Lemma solution_is_not_neg cs es x : eval_system es x -> Arithmetic.dot_product (mk_cert_poly cs es) (Arithmetic.cv_addn1_succ (col_mx x 1%:M)) >= 0.
Proof.
  (* rewrite /eval_system => /allP H. *)
  rewrite /eval_system /mk_cert_poly /sum_polys (big_morph (Arithmetic.dot_product^~ (Arithmetic.cv_addn1_succ (col_mx x 1%:M))) (eval_poly_morph x) (eval_poly0 x)) /scale_exprs big_seq /= => /allP H.
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

Theorem farkas_unsat (es : system m' n) (cs : m'.+2.-tuple R) x :
  check_cert es cs -> eval_system es x = false.
Proof.
  move=> /(cert_is_neg x).
  case E: (eval_system es x) => //=.
  move: E => /(solution_is_not_neg cs) E /lt_le_trans => /(_ (Arithmetic.dot_product (mk_cert_poly cs es ) (Arithmetic.cv_addn1_succ (col_mx x 1%:M)))) => /(_ E).
  by rewrite lt_irreflexive.
Qed.

End Farkas.

(* NOTE: This section aim is to demonstrate that the inductive definition `system` is the same as a matrix *)
Section Mat.

Open Scope ring_scope.

Definition mat_to_system A l u x : system m' n :=
  tcast (addn2 m') (
  cat_tuple
  [tuple (Eq n (Arithmetic.rv_addn1_succ (row_mx (row i A) 0%:M))) | i < m']
  [tuple (Geq n (Arithmetic.rv_addn1_succ (row_mx (u-x)^T 0%:M))); (Geq n (Arithmetic.rv_addn1_succ (row_mx (x-l)^T 0%:M)))]).

Definition poly_to_rv (p : poly n) : 'rV[R]_n :=
  lsubmx (castmx (erefl, esym (addn1 n)) p).

Lemma leqW2 (a : nat) : (a <= a.+2)%N.
Proof.
  apply leqW.
  by apply leqnSn.
Qed.

Definition system_to_mat (es : system m' n) : ('M[R]_(m',n) * 'cV[R]_n * 'cV[R]_n) :=
  (\matrix_(i < m') poly_to_rv (extract_poly (tnth es (widen_ord (leqW2 m') i))),
    (poly_to_rv (extract_poly (tnth es (ord_max - 1))))^T,
    (poly_to_rv (extract_poly (tnth es ord_max)))^T
  ).

(* NOTE: Specifying the order of mathcomp matrices. *)
Definition lermx {m' n} (mx1 mx2 : 'M[R]_(m',n)) :=
    [forall i : 'I_m' * 'I_n, mx1 i.1 i.2 <= mx2 i.1 i.2].

Check lermx.

End Mat.
Open Scope ring_scope.

Notation "A <=m B" := (lermx A B) (at level 70, no associativity) : ring_scope.

Definition eval_mat (A: 'M[R]_(m',n)) (l x u : 'cV[R]_n) : bool :=
  (A *m x == 0) && (l <=m x) && (x <=m u).

(* WARN: The following lemma is unfinished, is there any reason for it? *)
Lemma mat_system_inv  (A : 'M[R]_(m',n)) (l u x : 'cV[R]_n)
(es : system m' n) : system_to_mat (mat_to_system A l x u) = (A, l, u).
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
Lemma poly_equiv  (A : 'M[R]_(m',n)) (l x u : 'cV[R]_n) (es : system m' n) :
  eval_mat A l x u <-> eval_system es x.
Proof.
  split.
  rewrite /eval_mat /eval_system.
Admitted.

End FarkasSoundness.
