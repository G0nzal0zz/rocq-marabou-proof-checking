From mathcomp Require Import all_ssreflect all_algebra.

Require Import certificate_specs.

Require Import constraint.
Require Import split.
Require Import sat.
Require Import arithmetic.
Require Import util.
Require Import single_var_split_soundness.
Require Import relu.

Open Scope ring_scope.

Import CertificateSpecs GRing.Theory Num.Theory Order.POrderTheory.

Module ReluSplitSoundness.

Lemma maxr_idPr (x y : R) : reflect (Num.max x y = y) (x <= y).
Proof. by rewrite -eq_maxr; exact: eqP. Qed.

Lemma eval_relu_phase (b f aux : 'I_n) (x : 'rV[R]_n) :
  Relu.eval_relu b f aux x -> (x 0 b <= 0) || (0 <= x 0 b).
Proof.
  by move=> _; exact: Order.TotalTheory.le_total.
Qed.

Lemma bounded_inactive_phase
  (ub lb : 'rV[R]_n) (b f aux : 'I_n) (x : 'rV[R]_n) :
  let lbs_l := set_nth_vector lb f 0%R in
  let ubs_l := set_nth_vector (set_nth_vector ub b 0%R) f 0%R in
  x 0 b <= 0 ->
  Arithmetic.bounded x ub lb ->
  Relu.eval_relu b f aux x ->
  Arithmetic.bounded x ubs_l lbs_l.
Proof.
  move=> lbs_l ubs_l Hxb /forallP Hbound /andP [_ /andP [_ /andP [_ /andP [Hmax _]]]].
  apply/forallP => i; rewrite /ubs_l /lbs_l /set_nth_vector !mxE /=.
  have [Hif | Hif] := boolP (i == f).
  - move/eqP: Hif => Hif; subst i.
    have Hxf : x 0 f = 0%R.
      move/eqP: Hmax; rewrite /Relu.compute_relu => Hxf_eq.
      have Hmax0 : Num.max (x 0 b) 0 = 0 by apply/maxr_idPr; exact Hxb.
      by rewrite Hmax0 in Hxf_eq.
    by rewrite Hxf; apply/andP; split => //; exact/lexx.
  - have [Hib | Hib] := boolP (i == b).
      move/eqP: Hib => Hib; subst i.
      move: (Hbound b) => /andP [Hlb Hub].
      by rewrite Hlb Hxb.
    move: (Hbound i) => /andP [Hlb Hub].
    by apply/andP; split.
Qed.

Lemma bounded_active_phase
  (ub lb : 'rV[R]_n) (b f aux : 'I_n) (x : 'rV[R]_n) :
  let lbs_r := set_nth_vector (set_nth_vector lb b 0%R) aux 0%R in
  let ubs_r := set_nth_vector ub aux 0%R in
  0 <= x 0 b ->
  Arithmetic.bounded x ub lb ->
  Relu.eval_relu b f aux x ->
  Arithmetic.bounded x ubs_r lbs_r.
Proof.
  move=> lbs_r ubs_r Hxb /forallP Hbound /andP [_ /andP [_ /andP [_ /andP [Hmax Haux]]]].
  have Hxf_b : x 0 f = x 0 b.
  - move/eqP: Hmax; rewrite /Relu.compute_relu => Hxf_eq.
    have Hmax_b : Num.max (x 0 b) 0 = x 0 b.
      rewrite Order.TotalTheory.maxC; apply/maxr_idPr; exact Hxb.
    by rewrite Hmax_b in Hxf_eq.
  - have Hxaux0 : x 0 aux = 0%R.
      move/eqP: Haux => Haux_eq; rewrite Hxf_b addrK in Haux_eq; exact Haux_eq.
    apply/forallP => i; rewrite /ubs_r /lbs_r /set_nth_vector !mxE /=.
    have [Hiaux | Hiaux] := boolP (i == aux).
      move/eqP: Hiaux => Hiaux; subst i.
      rewrite Hxaux0; apply/andP; split => //; exact/lexx.
    have [Hib | Hib] := boolP (i == b).
      move/eqP: Hib => Hib; subst i.
      move: (Hbound b) => /andP [Hlb Hub].
      by rewrite Hxb Hub.
    move: (Hbound i) => /andP [Hlb Hub].
    by apply/andP; split.
Qed.

Lemma eval_relu_inequalities (b f aux : 'I_n) (x : 'rV[R]_n) :
  Relu.eval_relu b f aux x ->
  [/\ 0 <= x 0 f, x 0 aux = 0 & x 0 b = x 0 f] \/ [/\ x 0 b <= 0, x 0 f = 0 & 0 <= x 0 aux].
Proof.
  rewrite /Relu.eval_relu => /andP [Hneq_bf /andP [Hneq_baux /andP [Hneq_faux /andP [Hf Haux]]]].
  have Hphase: (x 0 b <= 0) || (0 <= x 0 b) := Order.TotalTheory.le_total (x 0 b) 0.
  case/orP: Hphase => Hx.
  - have Hmax0 : Relu.compute_relu (x 0 b) = 0.
      rewrite /Relu.compute_relu; apply/maxr_idPr; exact Hx.
    have Hf0 : x 0 f = 0.
      by move/eqP: Hf; rewrite Hmax0.
    have Haux_nonneg : 0 <= x 0 aux.
      move/eqP: Haux => Haux_eq.
      rewrite Hf0 subr0 in Haux_eq.
      have Haux_val : x 0 aux = - (x 0 b).
        move/eqP: Haux_eq; rewrite addr_eq0; move/eqP; by [].
      rewrite Haux_val; rewrite (oppr_ge0 (x 0 b)); exact Hx.
    right; split; [exact Hx | exact Hf0 | exact Haux_nonneg].
  - have Hmax_b : Relu.compute_relu (x 0 b) = x 0 b.
      rewrite /Relu.compute_relu; rewrite Order.TotalTheory.maxC; apply/maxr_idPr; exact Hx.
    have Hf_b : x 0 f = x 0 b.
      by move/eqP: Hf; rewrite Hmax_b.
    have Haux0 : x 0 aux = 0.
      move/eqP: Haux => Haux_eq.
      rewrite Hf_b addrK in Haux_eq.
      exact Haux_eq.
    left; split; [rewrite Hf_b; exact Hx | exact Haux0 | by rewrite Hf_b].
Qed.

Lemma soundness_relu_split_bounded
  (ub lb: 'rV[R]_n)
  (constraints : seq Constraint.t)
  (b f aux : 'I_n)
  (x : 'rV[R]_n) :
  let relu := Split.relu b f aux in
  let bounds := Split.update_bounds_from_split ub lb (Split.relu b f aux) in
  Split.check_split relu constraints ->
  Arithmetic.bounded x ub lb ->
  Constraint.check_relu_constraints constraints x ->
  Arithmetic.bounded x bounds.1.2 bounds.1.1 ||
  Arithmetic.bounded x bounds.2.2 bounds.2.1.
Proof.
  move=> relu bounds H_split H_bound H_constraints.
  have /hasP [c Hc_in Hc_eq] := H_split.
  have /eqP Heq_c' := Hc_eq.
  clear H_split.
  have Heval : Relu.eval_relu b f aux x.
  - have Hc_eval : Relu.eval_relu c.1.1 c.1.2 c.2 x.
     move: Hc_in H_constraints.
     elim: constraints => [|c' cs IH] Hc_in H_all.
      * by case: Hc_in.
      * move: Hc_in => /predU1P [->|Hc_in_cs].
        -- have /andP [Heval_c' _] : Constraint.check_relu_constraints (c' :: cs) x := H_all.
           exact Heval_c'.
        -- have /andP [_ H_cs] : Constraint.check_relu_constraints (c' :: cs) x := H_all.
           exact: IH Hc_in_cs H_cs.
    by rewrite -Heq_c' in Hc_eval.
  - have Hphase := eval_relu_phase b f aux x Heval.
    case/orP: Hphase => Hx.
    + apply/orP; left; exact: bounded_inactive_phase Hx H_bound Heval.
    + apply/orP; right; exact: bounded_active_phase Hx H_bound Heval.
Qed.

End ReluSplitSoundness.
