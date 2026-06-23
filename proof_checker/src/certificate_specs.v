From mathcomp Require Import all_ssreflect all_algebra.

Module CertificateSpecs.
  Definition R : numFieldType := rat.
  (* NOTE: Number of items in each row of the tableau*)
  Parameter (n : nat).
  (* NOTE:  Number of rows in tableau *)
  Parameter (m : nat).

End CertificateSpecs.
