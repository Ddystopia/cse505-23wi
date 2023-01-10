Inductive option (A : Set) : Set :=
| None : option A
| Some : A -> option A.

Arguments None {_}.
Arguments Some {_} _.

Inductive list (A : Set) : Set :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {_}.
Arguments cons {_} _ _.

Check cons 1 (cons 2 (cons 3 nil)).

Fixpoint app {A : Set} (l1 : list A) (l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | cons x xs => cons x (app xs l2)
  end.

Compute app (cons 1 (cons 2 nil)) (cons 3 (cons 4 nil)).
(* = cons 1 (cons 2 (cons 3 (cons 4 nil))) *)

Lemma app_nil_l : 
  forall (A : Set) (l : list A),
    app nil l = l.
Proof. intros. simpl. reflexivity. Qed.

Lemma app_nil_r : 
  forall (A : Set) (l : list A),
    app l nil = l.
Proof. 
  intros A l.
  induction l as [|x xs].
  - simpl. reflexivity.
  - simpl. f_equal. apply IHxs.
Qed.

Lemma app_assoc : 
  forall (A : Set) (l1 l2 l3 : list A),
    app (app l1 l2) l3 = app l1 (app l2 l3).
Proof.
  induction l1.
Admitted.

Fixpoint rev {A : Set} (xs : list A) : list A := 
  match xs with
  | nil => nil
  | cons x l => app (rev l) (cons x nil)
  end.

(* this definition is slow *)

Fixpoint rev_append {A : Set} (xs : list A) (acc : list A) : list A :=
  match xs with
  | nil => acc
  | cons x l => rev_append l (cons x acc) 
  end.
(* fast *)

Definition rev_tailrec {A : Set} (xs : list A) : list A := 
  rev_append xs nil.

Lemma rev_append_rev :
  forall (A : Set) (xs : list A) acc,
  rev_append xs acc = app (rev xs) acc. 
Proof.
  intros A xs.
  induction xs as [|x l]; simpl.
  - intros acc. reflexivity.
  - intros acc1.
    (* specialize (IHl (cons x acc1)) *)
  rewrite IHl.
  rewrite app_assoc.
  reflexivity.
  Qed.

(* rev_tailrec is equivalent to rev *)
Theorem rev_tailrec_equiv_rev :
  forall (A : Set) (l : list A),
    rev_tailrec l = rev l.
Proof.
  intros A l.

  