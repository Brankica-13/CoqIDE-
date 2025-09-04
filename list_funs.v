Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.


Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.
Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.
  
     
Fixpoint nonzeros (l:natlist) : natlist :=
match l with
  | nil => nil
  | 0 :: h => nonzeros h
  | h :: t => h :: nonzeros t
  end.
 

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.


Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=
  negb (even n).


Fixpoint oddmembers (l:natlist) : natlist :=
match l with
 | nil => nil
 | h :: t => match odd h with 
             | true => h :: (oddmembers t)
             | falce => oddmembers t
    end
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.


Definition countoddmembers (l:natlist) : nat :=
length (oddmembers l).


Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.
