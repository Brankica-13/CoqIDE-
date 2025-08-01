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
  
(* Definition grade_comparison (g1 g2 : grade) : comparison
match g1, g2 with                                                          This is a problem because: The variable APlus is bound several times in pattern.
  | APlus, APlus => Eq
  | APlus, A_ => Gt
  | ANatural, ANatural => Eq
  | A Minus, A Minus => Eq
  | A Natural, A Minus => Gt
  | A _ , A Plus => Lt
  | A _ , _ => Gt
  | B _ , A _ => Lt
  | B Plus, B Plus => Eq
  | B Plus, B _ => Gt
  | B Natural, B Natural => Eq
  | B Minus, B Minus => Eq
  | B Natural, B Minus => Gt
  | B _ , B Plus => Lt
  | C _ , (A _ | B _) => Lt
  | C Plus, C Plus => Eq
  | C Plus, C _ => Gt
  | C Natural, C Natural => Eq
  | C Minus, C Minus => Eq
  | C Natural, C Minus => Gt
  | C _ , C Plus => Lt  
  | C, _ => Gt
  | D _ , (A _ | B _ | C _) => Lt
  | D Plus, D Plus => Eq
  | D Plus, D _ => Gt
  | D Natural, D Natural => Eq
  | D Minus, D Minus => Eq
  | D Natural, D Minus => Gt
  | D _ , D Plus => Lt
  | D _ , _ => Gt
  | F _ , (A _ | B _ | C _ | D _) => Lt
  | F Plus, F Plus => Eq
  | F Plus, F _ => Gt
  | F Natural, F Natural => Eq
  | F Minus, F Minus => Eq
  | F Natural, F Minus => Gt
  | F _ , F Plus => Lt
  end.   *)
  

Definition grade_comparison (g1 g2 : grade) : comparison :=
  match g1, g2 with
  | Grade l1 m1, Grade l2 m2 =>                      First we decompose grades
      match letter_comparison l1 l2 with             then we compare letters
      | Lt => Lt
      | Gt => Gt
      | Eq => modifier_comparison m1 m2            if letters are same we compare modifiers
      end
  end.
  
  
  Example test_grade_comparison1 :
  (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof.
intros.
simpl.
reflexivity.
Qed.

Example test_grade_comparison2 :
  (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
  Proof.
intros.
simpl.
reflexivity.
Qed.

Example test_grade_comparison3 :
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
  Proof.
intros.
simpl.
reflexivity.
Qed.

Example test_grade_comparison4 :
  (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
  Proof.
intros.
simpl.
reflexivity.
Qed.
  
  
  
  
  
  
