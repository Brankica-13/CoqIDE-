Theorem mult_n_2 : forall n : nat,
n * 2 = n + n.
Proof.
intros.
rewrite <- mult_n_Sm.
rewrite <- mult_n_Sm.
rewrite <- mult_n_O. (* Wouldn't work without it becaouse: In environment n : nat Unable to unify "n + n" with "n * 0 + n + n". *)
reflexivity.
Qed.
