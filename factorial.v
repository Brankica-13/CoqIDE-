Module Brojevi.
Inductive nat : Type :=
  | O
  | S (n : nat).

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.
  
Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.
  
Fixpoint factorial1 (n : nat) : nat :=
match n with
| O => S O
| S n' => mult n (factorial1 n')
end.

End Brojevi.



Fixpoint factorial (n : nat) : nat :=
match n with
| 0 => 1
| S n' => n * factorial n'
end. 

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.
