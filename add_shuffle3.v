Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
intros n m p.
induction n as [ | n' IHn'].
- simpl. induction m as [ | m' IHm'].
+ simpl. reflexivity.
+ simpl. reflexivity.
- simpl. rewrite IHn'. reflexivity.
Qed.


Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
intros n m.
induction n as [ | n' IHn'].
- simpl. induction m as [ | m' IHm'].
+ simpl. reflexivity.
+ simpl. rewrite <- IHm'. reflexivity.
- simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.



Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
intros n m p.
rewrite -> add_assoc.
rewrite add_assoc.

assert (H: n + m = m + n).
{ rewrite add_comm. reflexivity.
}
rewrite H. reflexivity.
Qed.
