From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import ssrnum.

Require Import certificate_specs.
Require Import tightening.
Require Import constraint.
Require Import split.
Require Import sat.
Require Import arithmetic.
Require Import util.
Require Import single_var_split_soundness.
Require Import relu.

From Coq Require Import PeanoNat.

Open Scope ring_scope.

Import CertificateSpecs GRing.Theory Num.Theory Order.POrderTheory.

Module SplitSoundness.

(*lemma soundness_single_var_split_matching tableau ubs lbs constraints x split =
    let (lbs_l, ubs_l), (lbs_r, ubs_r) = update_bounds_from_split lbs ubs split in
    match split with
    | SingleSplit (i, k) ->
        sat tableau ubs lbs constraints x
        ==>
        sat tableau ubs_l lbs_l constraints x ||
        sat tableau ubs_r lbs_r constraints x
    | _ -> true
   [@@by auto]*)
Theorem soundness_single_var_split
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (ub lb: Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (i : 'I_n)
  (k : R)
  (x : 'rV[R]_n) :
  let bounds := Split.update_bounds_from_split ub lb (Split.single i k) in
  Sat.sat tableau ub lb constraints x
  ->
  Sat.sat tableau bounds.1.2 bounds.1.1 constraints x ||
  Sat.sat tableau bounds.2.2 bounds.2.1 constraints x.
Proof.
  move=> bounds H_sat.
  unfold Sat.sat in *.
  move/andP: H_sat => [/andP[H_kernel H_bounded] H_relu].
  rewrite H_kernel H_relu !andbT /=.
  clear H_kernel H_relu.
  move: (SingleSplitSoundness.bounded_set_nth ub lb i k x) => H_set_nth.
  by apply H_set_nth in H_bounded.
Qed.

Lemma maxr_idPr (x y : R) : reflect (Num.max x y = y) (x <= y).
Proof. by rewrite -eq_maxr; exact: eqP. Qed.

Lemma eval_relu_phase (b f aux : 'I_n) (x : 'rV[R]_n) :
  Relu.eval_relu b f aux x -> (x 0 b <= 0) || (0 <= x 0 b).
Proof.
  by move=> _; exact: Order.TotalTheory.le_total.
Qed.

Lemma bounded_inactive_phase
  (ub lb : Tightening.t_bounds) (b f aux : 'I_n) (x : 'rV[R]_n) :
  let lbs_l := set_nth_vector lb f 0%R in
  let ubs_l := set_nth_vector (set_nth_vector ub b 0%R) f 0%R in
  x 0 b <= 0 ->
  Arithmetic.bounded x ub lb ->
  Relu.eval_relu b f aux x ->
  Arithmetic.bounded x ubs_l lbs_l.
Proof.
  move=> lbs_l ubs_l Hxb /forallP Hbound /andP [_ /andP [_ /andP [_ /andP [Hmax _]]]].
  apply/forallP => i.
  rewrite /ubs_l /lbs_l /set_nth_vector !mxE.
  rewrite /ubs_l /lbs_l /set_nth_vector /=.
  have [Hif | Hif] := boolP (i == f).
    move/eqP: Hif => Hif; subst i.
    have Hxf : x 0 f = 0%R.
      move: Hmax; rewrite /Relu.compute_relu => /eqP ->.
      by move: (maxr_idPr (x 0 b) 0 Hxb) => H_maxr. 
      (*rewrite maxC; exact: max_l _ _ Hxb.*)
    by rewrite Hxf; apply/andP; split => //; exact/lexx.
  have [Hib | Hib] := boolP (i == b).
    move/eqP: Hib => Hib; subst i.
    move: (Hbound b) => /andP [Hlb Hub].
    by rewrite Hlb Hxb.
    (*apply/andP; split => //; exact: le_trans Hub Hxb.*)
  by move: (Hbound i) => /andP [Hlb Hub].
Qed.

Lemma bounded_active_phase
  (ub lb : Tightening.t_bounds) (b f aux : 'I_n) (x : 'rV[R]_n) :
  let lbs_r := set_nth_vector (set_nth_vector lb b 0%R) aux 0%R in
  let ubs_r := set_nth_vector ub aux 0%R in
  0 <= x 0 b ->
  Arithmetic.bounded x ub lb ->
  Relu.eval_relu b f aux x ->
  Arithmetic.bounded x ubs_r lbs_r.
Proof.
  move=> lbs_r ubs_r Hxb /forallP Hbound /andP [_ /andP [_ /andP [_ /andP [Hmax Haux]]]].
  have Hxf_b : x 0 f = x 0 b.
    have Hmax_eq : x 0 f = Num.max (x 0 b) 0%R := eqP Hmax.
    have Hmax_b : Num.max (x 0 b) 0%R = x 0 b.
   move: (max_idPr Hxb) => H_maxid.
   by rewrite  Order.TotalTheory.maxC.
    by rewrite Hmax_eq Hmax_b.
  have Hxaux0 : x 0 aux = 0%R.
    rewrite Hxf_b /= in Haux. 
    rewrite addrK in Haux.
    by move/eqP: Haux => Haux_eq.
  apply/forallP => i.
  rewrite /ubs_r /lbs_r /set_nth_vector !mxE.
  have [Hiaux | Hiaux] := boolP (i == aux).
      move/eqP: Hiaux => Hiaux.
      rewrite Hiaux Hxaux0. auto.
  have [Hib | Hib] := boolP (i == b).
    move/eqP: Hib => Hib.
    rewrite Hib Hxb /=. 
    move: (Hbound b) => H_test.
    by move/andP: H_test => [H_lb H_ub].
  move: (Hbound i) => /andP [Hlb Hub].
  by move: (Hbound i) => H_test.
Qed.

Print le_anti.

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
  -     have Hmax_b : Relu.compute_relu (x 0 b) = x 0 b.
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
  (ub lb: Tightening.t_bounds)
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
  - {have Hc_eval : Relu.eval_relu c.1.1 c.1.2 c.2 x.
    + {move: Hc_in H_constraints.
      elim: constraints => [|c' cs IH] Hc_in H_all.
      * by case: Hc_in.
      * move: Hc_in => /predU1P [->|Hc_in_cs].
        -- have /andP [Heval_c' _] : Constraint.check_relu_constraints (c' :: cs) x := H_all.
           exact Heval_c'.
        -- have /andP [_ H_cs] : Constraint.check_relu_constraints (c' :: cs) x := H_all.
           exact: IH Hc_in_cs H_cs. }
    + by rewrite -Heq_c' in Hc_eval. }
  - have Hphase := eval_relu_phase b f aux x Heval.
    case/orP: Hphase => Hx.
    + apply/orP; left; exact: bounded_inactive_phase Hx H_bound Heval.
    + apply/orP; right; exact: bounded_active_phase Hx H_bound Heval.
Qed.

(*theorem soundness_relu_split tableau us ls constraints xs b f aux split =
    let (lb_left, ub_left), (lb_right, ub_right) = update_bounds_from_split ls us split in
    List.length xs = List.length ls
    && List.length xs = List.length us
    && List.mem (Relu (b,f,aux)) constraints
    && split = ReluSplit (b, f, aux)
    && sat tableau us ls constraints xs
    ==>
    sat tableau ub_left lb_left constraints xs
    || sat tableau ub_right lb_right constraints xs
[@@by [%use sat_eval_relu tableau us ls constraints xs b f aux]
    @> [%use relu_split_soundness_sat xs tableau ls us constraints b f aux]
    @> intros
    @> auto
    ]
[@@disable sat, update_bounds_from_split, List.length, List.mem]
[@@fc] *)
Theorem soundness_relu_split
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (ub lb: Tightening.t_bounds)
  (constraints : seq Constraint.t)
  (b f aux : 'I_n)
  (x : 'rV[R]_n) :
  let relu := Split.relu b f aux in
  let bounds := Split.update_bounds_from_split ub lb relu in
  Split.check_split relu constraints &&
  Sat.sat tableau ub lb constraints x
  ->
  (Sat.sat tableau bounds.1.2 bounds.1.1 constraints x
  || Sat.sat tableau bounds.2.2 bounds.2.1 constraints x).
Proof.
  move => relu bounds /andP[H_split H_sat].
  unfold Sat.sat.
  unfold Sat.sat in H_sat.
  move: H_sat => /andP[/andP[H_kernel H_bounded] H_relu].
  rewrite H_kernel H_relu !andbT /=.
  clear H_kernel.
  by move: (soundness_relu_split_bounded ub lb constraints b f aux x H_split H_bounded H_relu). 
Qed.

End SplitSoundness.
