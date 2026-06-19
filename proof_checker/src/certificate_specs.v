
From mathcomp Require Import all_ssreflect all_algebra.

Module CertificateSpecs.
  Definition R : numFieldType := rat.
  (* NOTE: Number of items in each row *)
  Parameter (n : nat).
  (* NOTE:  Number of  rows *)
  Parameter (m : nat).
End CertificateSpecs.
