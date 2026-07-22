From mathcomp Require Import all_algebra all_ssreflect.

Require Import certificate_specs.
Require Import certificate.
Require Import arithmetic.
Require Import farkas.
Require Import farkas_soundness.

Require Import constraint.

Import CertificateSpecs GRing.Theory Num.Theory.

Open Scope ring_scope.

Module SystemSoundness.

Lemma dot_product_eq_kernel (hd : 'rV[R]_n) (x : 'rV[R]_n) :
  Arithmetic.dot_product (Arithmetic.rv_addn1_succ (row_mx hd 0))
    (Arithmetic.cv_addn1_succ (col_mx (trmx x) 1%:M))
  = Arithmetic.dot_product hd (trmx x).
Proof.
  rewrite /Arithmetic.dot_product.
  rewrite /Arithmetic.rv_addn1_succ /Arithmetic.cv_addn1_succ.
  rewrite !castmx_id.
  rewrite (mul_row_col hd 0 x^T 1%:M).
  by rewrite mul0mx addr0.
Qed.

Lemma system_soundness_eq
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (x : 'rV[R]_n) :
  Arithmetic.is_in_kernel tableau x ->
  let sys := Cert.mk_eq_constraints tableau in
  FarkasSoundness.eval_system sys (trmx x).
Proof.
  move=> Hin.
  rewrite /FarkasSoundness.eval_system
          /Arithmetic.is_in_kernel
          /Cert.mk_eq_constraints.

  apply/all_tnthP => i.
  rewrite tnth_map.
  rewrite /FarkasSoundness.eval_expr.

  have Hi := (all_tnthP Hin) i.
  by rewrite dot_product_eq_kernel.
Qed.

Lemma mk_bound_poly_last (i : 'I_n) (coeff bound : R) :
  (Cert.mk_bound_poly n i coeff bound) 0 ord_max = bound.
Proof. by rewrite /Cert.mk_bound_poly mxE /=. Qed.


Lemma mk_bound_poly_i (i : 'I_n) (coeff bound : R) :
  (Cert.mk_bound_poly n i coeff bound) 0 (widen_ord (leqnSn n) i) = coeff.
Proof.
  rewrite /Cert.mk_bound_poly mxE /=.
  have H : (widen_ord (leqnSn n) i : nat) != n
    by rewrite neq_ltn (ltn_ord i).
  by rewrite (negbTE H) /widen_ord /= eqxx.
Qed.

Search (_ == _ _).
Lemma mk_bound_poly_j (i j : 'I_n) (coeff bound : R) : i != j ->
  (Cert.mk_bound_poly n i coeff bound) 0 (widen_ord (leqnSn n) j) = 0.
Proof.
  move=> Hij.
  rewrite /Cert.mk_bound_poly mxE /=.
  have Hn : (widen_ord (leqnSn n) j : nat) != n
    by rewrite neq_ltn (ltn_ord j).
  rewrite (negbTE Hn).
  have Hji : (widen_ord (leqnSn n) j : nat) != (i : nat)
    by rewrite /widen_ord /= eq_sym.
  by rewrite (negbTE Hji).
Qed.

Lemma ext_col_mx_last (x : 'rV[R]_n) :
  (Arithmetic.cv_addn1_succ (col_mx (trmx x) 1%:M)) ord_max 0 = 1.
Proof. exact: FarkasSoundness.col_mx_max1. Qed.

Lemma ext_col_mx_i (x : 'rV[R]_n) (i : 'I_n) :
  (Arithmetic.cv_addn1_succ (col_mx (trmx x) 1%:M)) (widen_ord (leqnSn n) i) 0 = x 0 i.
Proof.
  rewrite /Arithmetic.cv_addn1_succ castmxE.
  have Hcast : cast_ord (esym (addn1 n)) (widen_ord (leqnSn n) i) = lshift 1 i
    by exact/val_inj.
  by rewrite Hcast col_mxEu mxE cast_ord_id.
Qed.

Lemma dot_product_mk_bound_poly (i : 'I_n) (coeff bound : R) (x : 'rV[R]_n) :
  Arithmetic.dot_product (Cert.mk_bound_poly n i coeff bound)
    (Arithmetic.cv_addn1_succ (col_mx (trmx x) 1%:M))
  = coeff * x 0 i + bound.
Proof.
  rewrite /Arithmetic.dot_product mxE big_ord_recr /=.
  rewrite mk_bound_poly_last ext_col_mx_last mulr1.
  rewrite (bigD1 i) //= mk_bound_poly_i ext_col_mx_i.
  rewrite big1 => [|j Hji].
    - by rewrite addr0.
    - have Hij : i != j by rewrite eq_sym in Hji.
        by rewrite mk_bound_poly_j // mul0r.
Qed.

Lemma system_soundness_geq
  (ub lb : 'rV[R]_n)
  (x : 'rV[R]_n) :
  Arithmetic.bounded x ub lb ->
  FarkasSoundness.eval_system (Cert.mk_geq_constraints ub lb) (trmx x).
Proof.
  move=> /forallP Hbounded.
  rewrite /FarkasSoundness.eval_system /Cert.mk_geq_constraints.
  rewrite all_cat; apply/andP; split.
  - have Hall_ub : all (FarkasSoundness.eval_expr ^~ (trmx x)) (Cert.mk_upper_bounds_constraints ub).
    {
      rewrite /Cert.mk_upper_bounds_constraints.
      refine (introT (all_tnthP (a := _) (t := _)) _) => i.
      rewrite tnth_mktuple /FarkasSoundness.eval_expr dot_product_mk_bound_poly.
      have /andP[_ Hupper] := Hbounded i.
      by rewrite mulN1r addrC subr_ge0.
    }
    exact Hall_ub.
  - have Hall_lb : all (FarkasSoundness.eval_expr ^~ (trmx x)) (Cert.mk_lower_bounds_constraints lb).
    {
      rewrite /Cert.mk_lower_bounds_constraints.
      refine (introT (all_tnthP (a := _) (t := _)) _) => i.
      rewrite tnth_mktuple /FarkasSoundness.eval_expr dot_product_mk_bound_poly.
      have /andP[Hlower _] := Hbounded i.
      by rewrite mul1r subr_ge0.
    }
    exact Hall_lb.
  Qed.

  (*theorem tableau_reduction_soundness tableau x =
    List.length x = List.length (List.hd tableau) &&
    well_formed_tableau tableau &&
    is_in_kernel tableau x
    ==>
    eval_system (mk_eq_constraints tableau) x
    [@@by induct ~on_vars:["tableau"] ()]
    [@@fc]*)
Theorem system_soundness
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (ub lb : 'rV[R]_n)
  (x : 'rV[R]_n) :
  Arithmetic.is_in_kernel tableau x && Arithmetic.bounded x ub lb ->
  let sys := Cert.mk_system_contradiction (Cert.mk_eq_constraints tableau) ub lb in
  FarkasSoundness.eval_system sys (trmx x).
Proof.
  move/andP=> [/system_soundness_eq H_ker /system_soundness_geq H_bound].
  rewrite /Cert.mk_system_contradiction in H_ker *.
  by rewrite FarkasSoundness.eval_system_composition H_ker H_bound.
Qed.

End SystemSoundness.
