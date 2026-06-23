From mathcomp Require Import all_algebra all_ssreflect.

Require Import certificate_specs.
Require Import split.

Import CertificateSpecs.

Module ProofTree.

Inductive t : Type :=
  | node : Split.t -> t -> t -> t
  (* WARN:
     It might not be necessary to use m.+2. instead of m.
     If that is the case, it should be changed.
  *)
  | leaf : (m.+2).-tuple R -> t.

End ProofTree.

