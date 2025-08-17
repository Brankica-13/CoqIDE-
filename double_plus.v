Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
  
  Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
Admitted.
  
  Lemma double_plus : forall n, double n = n + n .
Proof.
intro n.
induction n as [| n' IHn'].
- simpl. reflexivity.
- simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.
