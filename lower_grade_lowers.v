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


Definition lower_grade (g : grade) : grade := 
match g with
|Grade l m =>
match m with
| Plus => Grade l Natural
| Natural => Grade l Minus
| Minus =>
match l with 
| F => Grade F Minus
| _ => Grade (lower_letter l) Plus
end
end
end.
  

Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof.
simpl.
reflexivity.
Qed.


Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof.
simpl.
reflexivity.
Qed.

Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof.
simpl.
reflexivity.
Qed.

Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof.
simpl.
reflexivity.
Qed.

Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof.
simpl.
reflexivity.
Qed.

Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof.
simpl.
reflexivity.
Qed.

Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof.
simpl.
reflexivity.
Qed.

Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof. Admitted.

Theorem lower_grade_lowers :
  forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
Proof.
intro.
intro H.
destruct g.
destruct m.
- simpl.
  rewrite letter_comparison_Eq.
  reflexivity.
- simpl.
  rewrite letter_comparison_Eq.
  reflexivity.
- destruct l.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity. 
  + rewrite lower_grade_F_Minus. apply H.
Qed. 




