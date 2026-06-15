From mathcomp Require Import all_ssreflect all_algebra.

Require Import gen_certificates.
Require Import checker.

Print check_tree.
Section Main.

Variable (R' : numDomainType).
Variable (n : nat).
Variable (m : nat).

Definition check_tree' := check_tree R' n.


(*Definition result : bool := check_tree' ... .*)

End Main.

