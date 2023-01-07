Require HW2.
Require Import String List.
Open Scope string.
Import ListNotations.

(*
 * This "Module Type" contains the type of everything we expect you to define or
 * prove in this homework.
 *)
Module Type HW2sig.
  Module Homework1_TimeTravel.
    Inductive nat : Type :=
    | O : nat
    | S : nat -> nat.

    Fixpoint add (n1 : nat) (n2 : nat) : nat :=
      match n1 with
      | O => n2
      | S m1 => S (add m1 n2)
      end.

    Fixpoint mult (n1 : nat) (n2 : nat) : nat :=
      match n1 with
      | O => O
      | S m1 => add n2 (mult m1 n2)
      end.

    Parameter add_n_S :
      forall n1 n2,
        add n1 (S n2) = S (add n1 n2).

    Parameter mult_comm :
      forall n1 n2,
        mult n1 n2 = mult n2 n1.

    (* Note: mult_assoc and le_abc are not listed here, because you have to figure out how
     * to state them yourself. We will manually check for them when grading.
     *)
  End Homework1_TimeTravel.

  Parameter and_comm :
    forall (A B : Prop), A /\ B -> B /\ A.
  
  Parameter or_comm :
    forall (A B : Prop), A \/ B -> B \/ A.

  Inductive even : nat -> Prop :=
    | even_O : even O
    | even_SS : forall n, even n -> even (S (S n)).
  
  Fixpoint double (n : nat) : nat :=
    match n with
    | O => O
    | S m => S (S (double m))
    end.
  
  Parameter double_even : forall n, even (double n).

  Parameter even_double : forall n, even n -> exists k, n = double k.

  Parameter plus_even :
    forall x  y, even x -> even y -> even (x + y).
  
  Parameter three_not_even : even 3 -> False.

  Module Data_Structures.
    Set Implicit Arguments.
    Inductive list (A : Type) : Type :=
    | nil
    | cons (hd : A) (tl : list A).

    Arguments nil {A}.
    Infix "::" := cons.
    Notation "[ ]" := nil.
    Notation "[ x1 ; .. ; xN ]" := (cons x1 (.. (cons xN nil) ..)).

    Fixpoint length {A} (ls : list A) : nat :=
      match ls with
      | nil => 0
      | _ :: ls' => 1 + length ls'
      end.

    Fixpoint app {A} (ls1 ls2 : list A) : list A :=
      match ls1 with
      | nil => ls2
      | x :: ls1' => x :: app ls1' ls2
      end.
    Infix "++" := app.

    Fixpoint rev {A} (ls : list A) : list A :=
      match ls with
      | nil => nil
      | x :: ls' => rev ls' ++ [x]
      end.

    Parameter length_rev :
      forall A (l : list A),
        length (rev l) = length l.

    Inductive tree (A : Type) : Type :=
    | Leaf
    | Node : tree A -> A -> tree A -> tree A.
    Arguments Leaf {A}.

    Fixpoint reverse {A} (t : tree A) : tree A :=
      match t with
      | Leaf => Leaf
      | Node l d r => Node (reverse r) d (reverse l)
      end.

    Fixpoint sum_list (l : list nat) : nat :=
      match l with
      | [] => 0
      | x :: xs => x + sum_list xs
      end.

    Parameter sum_tree : tree nat -> nat.

    Parameter sum_tree_reverse :
      forall t,
        sum_tree (reverse t) = sum_tree t.

    Parameter sum_list_rev :
      forall l,
        sum_list (rev l) = sum_list l.
  End Data_Structures.

  Parameter lem_implies_peirce :
    (forall P : Prop, P \/ ~P) -> forall P Q : Prop, ((P -> Q) -> P) -> P.
End HW2sig.

(* Check that HW2 has the above signature. *)
Module M <: HW2sig := HW2.
