Module Constraint.

Inductive t : Type :=
  | relu : nat -> nat -> nat -> t.

Definition constraint_eqb (c1 c2 : t) : bool :=
  match c1, c2 with 
  | relu b1 f1 aux1, relu b2 f2 aux2 =>
      Nat.eqb b1 b2 && Nat.eqb f1 f2 && Nat.eqb aux1 aux2
  end.

End Constraint.
