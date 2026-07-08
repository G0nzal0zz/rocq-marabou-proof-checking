From mathcomp Require Import all_ssreflect all_algebra.

Module CertificateSpecs.
  Definition R : realDomainType := rat.
  (* NOTE: Number of items in each row of the tableau*)
  Parameter (n : nat).
  (* NOTE:  Number of rows in tableau *)
  Parameter (m : nat).

  Definition m' := (m + (n + n)).

End CertificateSpecs.
