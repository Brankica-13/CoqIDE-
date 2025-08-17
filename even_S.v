Fixpoint even (n:nat) : bool :=
  match n with
  | O =>true
  | S O => false
  | S (S n') => even n'
  end.
  

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
  
Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.
  
  

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
intro n.
simpl. induction n as [| n' IHn'].
- simpl. reflexivity.
- simpl. rewrite IHn'. rewrite negb_involutive. reflexivity.
Qed.
