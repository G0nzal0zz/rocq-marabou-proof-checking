From mathcomp Require Import all_algebra all_ssreflect.

Require Import certificate_specs.
Require Import certificate.
Require Import arithmetic.
Require Import farkas.
Require Import farkas_soundness.
Require Import tightening.
Require Import constraint.

Import CertificateSpecs.

Module TableauSoundness.

  (*theorem tableau_reduction_soundness tableau x =
    List.length x = List.length (List.hd tableau) &&
    well_formed_tableau tableau &&
    is_in_kernel tableau x
    ==>
    eval_system (mk_eq_constraints tableau) x
    [@@by induct ~on_vars:["tableau"] ()]
    [@@fc]*)
Theorem tableau_reduction_soundness
  (tableau : (m.+2).-tuple ('rV[R]_n))
  (ub lb : Tightening.t_bounds)
  (x : 'rV[R]_n) :
  Arithmetic.is_in_kernel tableau x && Arithmetic.bounded x ub lb -> 
  let sys := Cert.mk_system_contradiction (Cert.mk_eq_constraints tableau) ub lb in
  FarkasSoundness.eval_system sys (trmx x).
Proof.
  (* TODO *)
  (*intros.*)
  (*simpl in *.*)
  (*unfold FarkasSoundness.eval_system.*)

Admitted.

End TableauSoundness.
