From mathcomp Require Import all_ssreflect all_algebra.

Require Import certificate_specs.

Import CertificateSpecs.

Open Scope ring_scope.

Module Relu.

Definition t : Type := ('I_n * 'I_n * 'I_n).

Definition compute_relu (x : R) : R := Num.max x 0.

(*let eval_relu b_var f_var aux_var x =*)
(*    match List.nth b_var x, List.nth f_var x, List.nth aux_var x with*)
(*    | Some b, Some f, Some aux -> (b_var <> f_var) && (b_var <> aux_var) && (f_var <> aux_var) &&*)
(*        f = relu b && aux +. b -. f = 0.*)
(*    | _ -> false*)

Definition eval_relu (b_var f_var aux_var : 'I_n) (x : 'rV[R]_n) : bool :=
  [&& b_var != f_var, 
      b_var != aux_var, 
      f_var != aux_var &
      (x 0 b_var == compute_relu (x 0 f_var)) && (x 0 aux_var + x 0 b_var - x 0 f_var == 0)
  ].

(*lemma eval_relu_different_var xs f_var b_var a_var =*)
(*    eval_relu f_var b_var a_var xs*)
(*    ==> *)
(*    (b_var <> f_var) && (b_var <> a_var) && (f_var <> a_var) *)
(*[@@fc]*)

Lemma eval_relu_different_var (xs : 'rV[R]_n) (f_var b_var a_var : 'I_n) :
  eval_relu f_var b_var a_var xs ->
  [&& b_var != f_var, b_var != a_var & f_var != a_var].
Proof.
  rewrite /eval_relu.
  move=> /andP [] H1 /andP [] H2 /andP [] H3 _.
  rewrite /andb.
  case E: (b_var != f_var). (* Same as destruct, but it keeps the equality as a hypothesis. *)
  - destruct (b_var != a_var).
    + apply H2.
    + apply H3.
  - rewrite -E. rewrite eq_sym. apply H1.
Qed.

End Relu.
