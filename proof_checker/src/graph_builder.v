Require Import dpdgraph.dpdgraph.
Require checker_soundness. 
Require Import leaf_soundness.
Require Import node_soundness.
Require Import farkas_soundness.
Require Import single_var_split_soundness.
Require Import relu_split_soundness.
Require Import split_soundness.
Require Import system_soundness.

Print FileDependGraph checker_soundness LeafSoundness NodeSoundness FarkasSoundness SingleSplitSoundness ReluSplitSoundness SplitSoundness SystemSoundness.
