From mathcomp Require Import all_ssreflect all_algebra.

Require Import parsed_certificate.
Require Import checker.

Import ParsedCertificates.

Section Main.


Definition is_unsat := Checker.check_proof_tree tableau ub lb constraints proof_tree.

Redirect "result.txt" Eval vm_compute in is_unsat.

End Main.

