(* comments can even (* nest *) *)

Inductive bool : Set :=
| true : bool
| false : bool.

Check true.
Check (true : bool).
Check bool.
Check Set.
Check Type.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Compute (andb true false).
Compute (andb true true).

Lemma andb_comm :
    forall b1 b2 : bool,
        andb b1 b2 = andb b2 b1.
Proof.
    intro b1.
    intro b2.
    destruct b1.
    - simpl.
      destruct b2.
      (* foo *)
      + simpl. reflexivity.
      + simpl. reflexivity.
    - destruct b2.
    (* foo *)
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Lemma andb_comm_short :
    forall b1 b2 : bool,
        andb b1 b2 = andb b2 b1.
Proof.
    destruct b1; destruct b2; reflexivity.
Qed.

Print andb.
Print andb_comm.

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Compute (S O).

Definition isZero (n : nat) : bool :=
  match n with
  | O => true
  | _ => false
  end.

Fixpoint add (n1 n2 : nat) : nat :=
  match n1 with
  | O => n2
  | S p => S (add p n2)
  end.

Print add.

Lemma add_0_n :
    forall n : nat,
        add O n = n.
Proof.
    intro n.
    simpl.
    reflexivity.
Qed.

Lemma add_n_0 :
    forall n : nat,
        add n O = n.
Proof.
    intro n.
    induction n as [| p IHp].
    - auto.
    - simpl.
    (*
     f_equal. assumption.
    *)
     rewrite IHp.
     reflexivity.
Qed.

Inductive optional_nat : Set := 
| None_nat : optional_nat
| Some_nat : nat -> optional_nat.

(* return the previous natural number, except for zero where we return zero *)
Definition pred (n : nat) : optional_nat :=
  match n with
  | O => None_nat
  | S p => Some_nat p
  end.

Compute pred (S (S (S O))).   (* should be S (S O) *)

(* Definition f (b : bool) : optional_bool *)

Inductive optional (A : Set) : Set := 
| None : optional A 
| Some : A -> optional A.

Check None.
Check Some.

Definition pred2 (n : nat) : optional nat :=
  match n with
  | O => None nat
  | S p => Some nat p
  end.

Arguments None {A}.
Arguments Some {A} _.

Definition pred3 (n : nat) : optional nat :=
  match n with
  | O => None 
  | S p => Some p
  end.

Inductive list (A : Set) : Set :=
| nil : list A 
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} _ _.

Check nil.
Check cons.

Fixpoint append {A : Set} (l1 l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | cons h t => cons h (append t l2)
  end.

Lemma append_nil_left : 
  forall A (l : list A),
    append nil l = l.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Fixpoint rev {A : Set} (l : list A) : list A :=
    match l with
    | nil => nil
    | cons h t => append (rev t) (cons h nil)
    end.

Compute rev (cons (S O) (cons (S (S O)) (cons (S (S (S O))) nil))).

Fixpoint rev_tr {A : Set} (l : list A) (acc : list A) : list A :=
    match l with
    | nil => acc
    | cons h t => rev_tr t (cons h acc)
    end.

Compute 
  rev_tr 
    (cons (S O) (cons (S (S O)) (cons (S (S (S O))) nil)))
    nil.

Theorem rev_tr_correct : 
  forall (A : Set) (l : list A), 
    rev l = rev_tr l nil.
Admitted.