From mathcomp Require Import all_algebra all_ssreflect.

Require Import certificate_specs.
Require Import certificate.
Require Import arithmetic.
Require Import farkas.
Require Import farkas_soundness.
Require Import tightening.
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
  apply (f_equal (fun M : 'M[R]_(1,1) => M ord0 ord0)).
  apply/matrixP => i j.
  rewrite !mxE.
  rewrite /Arithmetic.rv_addn1_succ /Arithmetic.cv_addn1_succ.
  rewrite [\sum_(k < n.+1) _]big_ord_recr.
  have Hcast (A : 'M[R]_(1, n+1)) (u : 'I_n.+1) :
    (castmx (erefl, addn1 n) A) i u = A i (cast_ord (esym (addn1 n)) u).
    by rewrite (@castmxE R 1 (n+1) 1 n.+1 (erefl, addn1 n) A i u) cast_ord_id.
  have Hcast' (B : 'M[R]_(n+1, 1)) (v : 'I_n.+1) :
    (castmx (addn1 n, erefl) B) v j = B (cast_ord (esym (addn1 n)) v) j.
    by rewrite (@castmxE R (n+1) 1 n.+1 1 (addn1 n, erefl) B v j) cast_ord_id.
  have Hord_max : cast_ord (esym (addn1 n)) (ord_max : 'I_n.+1) = rshift n ord0 :> 'I_(n+1).
    apply/val_inj => /=; by rewrite addn0.
  have Hwiden (k : 'I_n) : cast_ord (esym (addn1 n)) (widen_ord (leqnSn n) k) = lshift 1 k :> 'I_(n+1).
    exact/val_inj.
  have Hlast : (castmx (erefl, addn1 n) (row_mx hd 0)) i ord_max *
    (castmx (addn1 n, erefl) (col_mx (trmx x) 1%:M)) ord_max j = 0.
    rewrite Hcast Hcast' Hord_max.
    by rewrite row_mxEr col_mxEd !mxE mul0r.
  rewrite Hlast; simpl; rewrite addr0.
  apply: eq_bigr => k _.
  rewrite Hcast Hcast' Hwiden row_mxEl col_mxEu.
  by [].
Qed.

Lemma system_soundness_eq
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (x : 'rV[R]_n) :
  Arithmetic.is_in_kernel tableau x ->
  let sys := Cert.mk_eq_constraints tableau in
  FarkasSoundness.eval_system sys (trmx x).
Proof.
  move=> Hin.
  rewrite /FarkasSoundness.eval_system /Cert.mk_eq_constraints.
  have -> : val (map_tuple (fun hd : 'rV[R]_n => Farkas.Eq n (Arithmetic.rv_addn1_succ (row_mx hd 0))) tableau) =
            map (fun hd : 'rV[R]_n => Farkas.Eq n (Arithmetic.rv_addn1_succ (row_mx hd 0))) (val tableau) by [].
  rewrite all_map.
  apply/allP => hd Hhd.
  move/allP: Hin => Hin.
  have Hcheck : Arithmetic.check_dot_product_zero hd (trmx x) := Hin hd Hhd.
  move: Hcheck => /eqP Hcheck.
  rewrite /FarkasSoundness.eval_expr.
  apply/eqP.
  rewrite dot_product_eq_kernel.
  exact Hcheck.
Qed.

Lemma dot_product_mk_bound_poly (i : 'I_n) (coeff bound : R) (x : 'rV[R]_n) :
  Arithmetic.dot_product (Cert.mk_bound_poly n i coeff bound)
    (Arithmetic.cv_addn1_succ (col_mx (trmx x) 1%:M))
  = coeff * x 0 i + bound.
Proof.
  rewrite /Arithmetic.dot_product mxE big_ord_recr.
  have Hlast : (Cert.mk_bound_poly n i coeff bound) 0 ord_max *
    (Arithmetic.cv_addn1_succ (col_mx (trmx x) 1%:M)) ord_max 0 = bound.
  { have -> : (Cert.mk_bound_poly n i coeff bound) 0 ord_max = bound.
    { rewrite /Cert.mk_bound_poly mxE /=.
      by rewrite /ord_max /= eqxx. }
    by rewrite FarkasSoundness.col_mx_max1 mulr1. }
  rewrite Hlast.
  rewrite [X in X + _ = _](bigD1 i) //=.
  rewrite /Cert.mk_bound_poly mxE /=.
  have H_not_n : (widen_ord (leqnSn n) i : nat) != n.
    by rewrite /widen_ord /= neq_ltn (ltn_ord i).
  rewrite (negbTE H_not_n) /widen_ord /= eqxx.
  rewrite /Arithmetic.cv_addn1_succ castmxE.
  have Hcast : cast_ord (esym (addn1 n)) (widen_ord (leqnSn n) i) = lshift 1 i.
    exact/val_inj.
  rewrite Hcast col_mxEu mxE cast_ord_id.
  rewrite big1 => [|k Hk]; last first.
  { rewrite /Cert.mk_bound_poly mxE /=.
    have H_not_n' : (widen_ord (leqnSn n) k : nat) != n.
      by rewrite /widen_ord /= neq_ltn (ltn_ord k).
    rewrite (negbTE H_not_n').
    have H_not_i : (widen_ord (leqnSn n) k : nat) != (i : nat).
      by rewrite /widen_ord /=.
    by rewrite (negbTE H_not_i) mul0r. }
  rewrite addr0.
  reflexivity.
Qed.

Lemma system_soundness_geq
  (ub lb : Tightening.t_bounds)
  (x : 'rV[R]_n) :
  Arithmetic.bounded x ub lb ->
  FarkasSoundness.eval_system (Cert.mk_geq_constraints ub lb) (trmx x).
Proof.
  move=> /forallP Hbounded.
  rewrite /FarkasSoundness.eval_system /Cert.mk_geq_constraints.
  have Heq_val : val (Cert.mk_geq_constraints ub lb) = val (Cert.mk_upper_bounds_constraints ub) ++ val (Cert.mk_lower_bounds_constraints lb) := erefl.
  rewrite Heq_val all_cat; apply/andP; split.
  - have Hall_ub : all (FarkasSoundness.eval_expr ^~ (trmx x)) (Cert.mk_upper_bounds_constraints ub).
    { rewrite /Cert.mk_upper_bounds_constraints.
      refine (introT (all_tnthP (a := _) (t := _)) _) => i.
      rewrite tnth_mktuple /FarkasSoundness.eval_expr dot_product_mk_bound_poly.
      have /andP[_ Hupper] := Hbounded i.
      by rewrite mulN1r addrC subr_ge0. }
    exact Hall_ub.
  - have Hall_lb : all (FarkasSoundness.eval_expr ^~ (trmx x)) (Cert.mk_lower_bounds_constraints lb).
    { rewrite /Cert.mk_lower_bounds_constraints.
      refine (introT (all_tnthP (a := _) (t := _)) _) => i.
      rewrite tnth_mktuple /FarkasSoundness.eval_expr dot_product_mk_bound_poly.
      have /andP[Hlower _] := Hbounded i.
      by rewrite mul1r subr_ge0. }
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
  (ub lb : Tightening.t_bounds)
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
