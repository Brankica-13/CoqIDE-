Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
intros b c.
destruct b eqn:Eb.
-simpl.                  (* in this case b is true; simpl does this: c = true → c = true *)
  intro H.               (* H : c = true *)
rewrite <- H.
reflexivity.
  -simpl.                (* b is false; simol does this: false = true → c = true)
  intros H.                (* H : false = true *)
destruct c.
+ reflexivity.
  + rewrite -> H.          (* + is case false = true; because of H we can replasse falce with true*)
reflexivity.
Qed.
  
