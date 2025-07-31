Inductive letter : Type :=
  | A | B | C | D | F.

Inductive modifier : Type :=
  | Plus | Natural | Minus.

Inductive grade : Type :=
  Grade (l:letter) (m:modifier).
  
Inductive comparison : Type :=
  | Eq (* "equal" *)
  | Lt (* "less than" *)
  | Gt. (* "greater than" *)
  
Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.


Theorem letter_comparison_Eq :
  forall l, letter_comparison l l = Eq.
Proof.
intro.
destruct l.
- simpl.
reflexivity.
- simpl.
reflexivity.
- simpl.
reflexivity.
- simpl.
reflexivity.
- simpl.
reflexivity.
Qed.
