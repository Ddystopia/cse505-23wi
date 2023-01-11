Module Phase1.

Inductive list (T : Type) : Type :=
| nil : list T
| cons : T -> list T -> list T.

(* infer some parameters *)
Arguments nil {T}.
Arguments cons {T} _ _.

Fixpoint length {A : Type} (l : list A) : nat :=
  match l with
  | nil => O
  | cons x xs => S (length xs)
  end.

Compute length nil.                   (* 0 ... but which nil?! *)
Compute length (cons 1 nil).          (* 1 *)
Compute length (cons 1 (cons 2 nil)). (* 2 *)

Fixpoint countdown (n : nat) : list nat :=
  match n with
  | O => cons n nil
  | S m => cons n (countdown m)
  end.

Compute countdown 1. (* cons 0 nil *)
Compute countdown 3. (* cons 3 (cons 2 (cons 1 (cons 0 nil))) *)

Lemma length_countdown :
  forall n,
    length (countdown n) = S n.
Proof.
Admitted.


Set Implicit Arguments.

Fixpoint app (A : Type) (l1 l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | cons x xs => cons x (app xs l2)
  end.

(* looks familiar! *)
Print Nat.add.
Print app.

Lemma app_nil_l :
  forall A (l : list A),
    app nil l = l.
Proof.
  auto.
Qed.

Lemma app_l_nil :
  forall A (l : list A),
    app l nil = l.
Proof.
  induction l; simpl.
  - reflexivity.
  - rewrite IHl. reflexivity.
Qed.

Lemma app_assoc :
  forall A (l1 l2 l3 : list A),
    app l1 (app l2 l3) = app (app l1 l2) l3.
Proof.
  intros A l1 l2 l3.
  induction l1 as [|x l4]; simpl.
  - reflexivity.
  - rewrite IHl4. reflexivity.
Qed.

Fixpoint rev {A : Set} (xs : list A) : list A :=
  match xs with
  | nil => nil
  | cons x l => app (rev l) (cons x nil) (* [x] *)
  end.

Fixpoint rev_append {A : Set} (xs : list A) (acc : list A) : list A :=
  match xs with
  | nil => acc
  | cons x l => rev_append l (cons x acc)
  end.

Compute rev_append (cons 1 (cons 2 nil)) (cons 3 (cons 4 nil)).

Definition rev_fast {A : Set} (xs : list A) : list A :=
  rev_append xs nil.

Lemma rev_append_correct : 
  forall (A : Set) (xs : list A) (acc : list A),
    rev_append xs acc = app (rev xs) acc.
Proof.
  intros A xs.
  induction xs as [|x l].
  - intros acc. simpl. reflexivity.
  - intros acc1. simpl.
    (* assert (forall acc : list A,
    rev_append l acc = app (rev l) acc).
      assumption. *)
    (* pose proof (IHl (cons x acc1)). *)
    specialize (IHl (cons x acc1)).
  
  rewrite IHl.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Theorem rev_fast_correct :
  forall (A : Set) (xs : list A), 
    rev_fast xs = rev xs.
Proof.
  intros A xs.
  unfold rev_fast.
  rewrite rev_append_correct.
  rewrite app_l_nil.
  reflexivity.
Qed.

End Phase1.

Require Import List.
Import ListNotations.

Check [1; 2; 3].
Check [].

Print nat.

Check (True /\ True).
Print and.

(*
Inductive and (A B : Prop) : Prop :=
| conj : A -> B -> and A B.
*)

Require Import Psatz.

Lemma foo :
  1 <= 2 /\ negb true = false.
Proof.
  
  constructor.
  - lia.
  - constructor.

(*
  apply conj.
  - Locate "<=".
    Print le.
    apply le_S.
    apply le_n.
    Show Proof.
  - Print negb.
    simpl.
    reflexivity.
  Show Proof.
*)
Qed.

Lemma and_elim_l :
  forall (A B : Prop),
    A /\ B ->
    A.
Proof.
  intros.
  destruct H.
  exact H.
Qed.


Check (True /\ False).

Check (True \/ False).
Locate "\/".
Print or.

(*
Inductive or (A B : Prop) : Prop :=
|	or_introl : A -> or A B
| or_intror : B -> or A B.
*)


Lemma foobar :
  2 <= 1 \/ negb true = false.
Proof.
  right. auto.
  Restart.
  apply or_intror. auto.
Qed.

Lemma foobar' :
  2 <= 1 \/ negb true = true ->
  False.
Proof.
  intros.
  destruct H.
  - lia.
  - simpl in H. congruence.
Qed.

Print True.
Print False.

Check (exists x, 1 <= x).
Locate "exists".
Print ex.

(*
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> exists y, P y.
*)

Lemma blorp :
  exists x, 1 <= x.
Proof.
  exists 1. lia.  

  Restart.

  econstructor.
  constructor.
  Show Proof.
Qed.


Lemma blorpFOO :
  (exists x, 1 <= x) ->
  True.
Proof.
  exact (fun _ => I).
  Show Proof.

  Restart.

  intros.
  destruct H.
  exact I.
  Show Proof.
Qed.

Inductive tree (A : Set) : Set :=
| leaf : tree A 
| branch : A -> tree A -> tree A -> tree A.

Inductive list (A : Set) : Set :=
| nil : list A 
| cons : A -> list A -> list A.