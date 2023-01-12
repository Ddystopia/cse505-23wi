Check (True /\ True).

Locate "/\".

Print and.

(*
Inductive and (A B : Prop) : Prop :=
| conj : A -> B -> and A B.
*)

Require Import Psatz.

Lemma foo :
  1 <= 2 /\ negb true = false.
Proof.
  auto.

  Restart.
  apply conj.
  Show Proof.
  - Locate "<=". Print le.
    apply le_S.
    apply le_n.
  - simpl. reflexivity.

  Restart.
  split.
  Show Proof.
  - lia.
  - auto.
  
  Restart.
  constructor.
  - constructor. Show Proof. 
    constructor. Show Proof.
  - auto.

  Show Proof.
Qed.

Lemma bar :
  1 <= 2 /\ negb true = false ->
  1 <= 2.
Proof.
  intros.
  destruct H.
  auto.

  (* Show Proof.
  exact H.

  assumption.  *)
Qed.

Locate "\/".
Print or.

(*
Inductive or (A B : Prop) : Prop :=
|	or_introl : A -> or A B
| or_intror : B -> or A B.
*)

Lemma foo_or :
  1 <= 2 \/ negb true = false.
Proof.
  auto.
  Restart.

  apply or_intror.
  auto.
  Show Proof.
Qed.

Lemma foo_or' :
  False \/ 1 <= 2.
Proof.
  apply or_intror.
  auto.
Qed.

Lemma foo_or'' :
  False \/ 1 <= 2 ->
  1 <= 2.
Proof.
  intros.
  destruct H.
  - destruct H. (* contradiction. TODO *)
  - assumption.
Qed.

Print True.
Print False.

Locate "exists".
Print ex.

(* 
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex A P. *)

Lemma blorp:
  exists n, 1 <= n.
Proof.
  econstructor.
  apply le_n.

  Restart.
  exists 100.
  lia.
Qed.

Lemma blorp':
  (exists n, n < 0) ->
  False.
Proof.
  intros.
  destruct H.
  inversion H.
Qed.

(*
and, or, True, False, exists 

are all inductive types!!!!!!!!!!!


to produce a value of an inductive type: 
  - use a constructor
  - use the constructor tactic
  - or apply the name of a constructor

to consume/use/when-it's-above-the-horizontal-line a value of an inductive type:
- destruct

*)

Inductive tree (A : Set) : Set :=
| Leaf : tree A
| Node : tree A -> A -> tree A -> tree A.
Arguments Leaf {_}.
Arguments Node {_} _ _ _.

Fixpoint tree_reverse {A : Set} (t : tree A) : tree A :=
  match t with
  | Leaf => Leaf
  | Node l x r => Node (tree_reverse r) x (tree_reverse l)
  end.

Require Import List.
Import ListNotations.

Fixpoint tree_to_list {A : Set} (t : tree A) : list A :=
  match t with
  | Leaf => []
  | Node l x r => tree_to_list l ++ [x] ++ tree_to_list r 
  end.

Print tree_to_list.

Lemma tree_reverse_tree_to_list : 
  forall A (t : tree A),
    tree_to_list (tree_reverse t) = rev (tree_to_list t).
Proof.
  intros A t.
  induction t.
  - simpl. reflexivity.
  - simpl. rewrite IHt2. rewrite IHt1.
    Search (rev (_ ++ _)).
    rewrite rev_app_distr.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
    Qed.