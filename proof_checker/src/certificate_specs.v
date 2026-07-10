From mathcomp Require Import all_ssreflect all_algebra.
Require Import parsed_certificate_specs.

Module CertificateSpecs.
  Definition R : realDomainType := rat.
  (* NOTE: Number of items in each row of the tableau*)
  Definition n : nat := ParsedCertificateSpecs.n.
  (* NOTE:  Number of rows in tableau *)
  Definition m : nat := ParsedCertificateSpecs.m.

  Definition m' := (m + (n + n)).

End CertificateSpecs.
