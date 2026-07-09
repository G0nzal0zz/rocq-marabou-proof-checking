From mathcomp Require Import all_ssreflect all_algebra.

Require Import gen_certificates.
Require Import checker.

Import ParsedCertificates.

Section Main.


Definition is_unsat := Checker.check_proof_tree tableau ub lb constraints proof_tree.

Compute (is_unsat).

End Main.

