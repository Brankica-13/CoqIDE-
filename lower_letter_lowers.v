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


Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.
  
  
  
Definition grade_comparison (g1 g2 : grade) : comparison :=
  match g1, g2 with
  | Grade l1 m1, Grade l2 m2 =>
      match letter_comparison l1 l2 with
      | Lt => Lt
      | Gt => Gt
      | Eq => modifier_comparison m1 m2
      end
  end.
  
  
Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F (* Can't go lower than F! *)
  end.
  
  Theorem lower_letter_F_is_F:
  lower_letter F = F.
Proof.
  simpl. reflexivity.
Qed.


Theorem lower_letter_lowers:
  forall (l : letter),
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l = Lt.
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
intro H.               (* We introduce H because we have expression Eq = Lt → Eq = Lt in which Eq = Lt makes a problem, so we want to get around it. *)
rewrite <- H.
reflexivity.
Qed.



  
  
  
  
  
  
