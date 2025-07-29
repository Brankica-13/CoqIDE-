Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros.
  rewrite <- mult_n_Sm.   (** This writes p*1 as p*0 + p *)
  rewrite <- mult_n_O.    (** This writes p*0 as 0 *)
  reflexivity. Qed.
