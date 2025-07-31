Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros n.
destruct n. (* first case is 0 = 0 + 1, second is 0 = S n + 1*)
  - reflexivity.
  - reflexivity.
Qed.
