From mathcomp Require Import all_algebra all_ssreflect.

Require Import certificate_specs.
Require Import split.

Import CertificateSpecs.

Module ProofTree.

Inductive t : Type :=
  (*  split information, left child, right child *)
  | node : Split.t -> t -> t -> t
  (* contradiction vector *)
  | leaf : (m.+2).-tuple R -> t.

End ProofTree.

