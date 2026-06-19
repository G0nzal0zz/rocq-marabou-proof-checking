From mathcomp Require Import all_algebra seq.

Require Import certificate_specs.
Require Import split.

Import CertificateSpecs.

Module ProofTree.

Inductive t : Type :=
  | node : Split.t -> t -> t -> t
  | leaf : seq R -> t.

End ProofTree.

