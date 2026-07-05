(**
  Disclaimer: The contents of this file were extracted from the
  proof-certs-translation repository:
  https://github.com/lstrsrmn/proof-certs-translation/tree/main
*)
From mathcomp Require Import all_ssreflect all_fingroup all_algebra zmodp ssrnum ssrnat matrix eqtype.

Require Import certificate_specs.

Import GRing.Theory.
Import CertificateSpecs.

Module Farkas.

Open Scope ring_scope.

Implicit Type x : 'cV[R]_n.
Implicit Type p : 'rV[R]_n.+1.

(* NOTE:'rV[R]_n.+1 is the MathComp type of row vectors over R of length n + 1. *)
Definition poly (n : nat) : Type := 'rV[R]_n.+1.

(*Coercion vector_poly 'rV[R]>-> *)

Inductive expr (n : nat) :=
  | Eq of poly n
  | Geq of poly n.

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
Definition system (m n : nat): Type := (m.+2).-tuple (expr n).

Definition is_neg_const p : bool :=
  [forall i : 'I_n.+1, if i == ord_max then p 0 i < 0 else p 0 i == 0].

Check Eq.

(** This is not a nice solution, should look into it **)
Definition scale_expr (c : R) (e : expr n) : (expr  n) :=
  match e with
  | Eq p => Eq n (c *: p)
  | Geq p => if c >= 0 then Geq n (c *: p) else Geq n p
  end.

Definition scale_exprs (cs : m'.+2.-tuple R) (es :  system m' n) : system m' n :=
  map (fun '(c, e) => scale_expr c e) (zip_tuple cs es).

Definition sum_polys (es : system m' n) : poly n :=
  \sum_(e <- es) extract_poly e.

Definition mk_cert_poly (cs : m'.+2.-tuple R) (es : system m' n) : poly n :=
  sum_polys (scale_exprs cs es).

Definition check_cert (es : system m' n) (cs : m'.+2.-tuple R) : bool :=
  is_neg_const (mk_cert_poly cs es).

End Farkas.
