Theorem mult_n_0_m_0 : forall p q : nat,
  (p × 0) + (q × 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.
