(*

  _   _    ___    __  __   _____  __        __   ___    ____    _  __    ____
 | | | |  / _ \  |  \/  | | ____| \ \      / /  / _ \  |  _ \  | |/ /   |___ \
 | |_| | | | | | | |\/| | |  _|    \ \ /\ / /  | | | | | |_) | | ' /      __) |
 |  _  | | |_| | | |  | | | |___    \ V  V /   | |_| | |  _ <  | . \     / __/
 |_| |_|  \___/  |_|  |_| |_____|    \_/\_/     \___/  |_| \_\ |_|\_\   |_____|


Howdy folks! In this homework assignment we'll explore more Coq programming
and proving and get some practice with interpreters.

There are 21 problems worth a total of 120 core points and
30 challenge points.

*)


Require Import Arith Lia List String.
Import ListNotations.
Open Scope string.

(*
               ____                  _     _                     _
              / ___|    ___    ___  | |_  (_)   ___    _ __     / |
              \___ \   / _ \  / __| | __| | |  / _ \  | '_ \    | |
               ___) | |  __/ | (__  | |_  | | | (_) | | | | |   | |
              |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |_|

                          SECTION 1 : More Coq Practice
*)

(*
 * In this part of the homework, we get some practice with lists and other
 * data structures.
 *
 * Step through this file with VSCode (or another IDE for Coq), and complete the
 * problems. Search for "PROBLEM" to be sure you find them all---not all
 * problems correspond to Coq code!
 *
 * Throughout, we include the approximate lines of code (LOC) or number of
 * tactics for each of our solutions to these problems.  These are rough
 * guidelines to help you figure out if you are getting off track.
 *
 * There is no penalty for writing a shorter or longer solution! However, if
 * you find yourself writing a much longer solution, you might save yourself
 * some time by taking a step back and seeing if you can find a simpler way.
 *
 *)

(* --- More arithmetic --- *)

(* This module creates a namespace where we can travel back in time to
 * Homework 1. Later in this homework we will be using the Coq standard library
 * version of nat, so we hide our own definitions in this namespace so we can
 * close it later.
 *)
Module Homework1_TimeTravel. (* get in the DeLorean *)
Set Implicit Arguments.

(*
 * Here are some definitions again from Homework 1.
 *)
Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Fixpoint add (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => n2
  | S m1 => S (add m1 n2)
  end.

Lemma eq_S:
  forall n1 n2,
    n1 = n2 -> S n1 = S n2.
Proof.
  intros.
  destruct n1; rewrite H; reflexivity.
Qed.

(*
 * PROBLEM 1 [0 points, ~4 tactics]
 *
 * You'll need this, which you proved in Homework 1. Feel free to copy/paste
 * your solution.
 *)
Lemma add_n_S :
  forall n1 n2,
    add n1 (S n2) = S (add n1 n2).
Proof.
  induction n1; simpl.
   - reflexivity.
   - intros.
     simpl.
     apply eq_S.
     apply IHn1.
Qed. (* Change to Qed when done *)

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
    (*todo*)
    induction n as [| p IHp].
    - auto.
    - simpl.
    (*
     f_equal. assumption.
    *)
     rewrite IHp.
     reflexivity.
Qed.

Lemma add_assoc : 
  forall n1 n2 n3, add n2 (add n1 n3) = add n1 (add n2 n3).
Proof.
 intros.
 induction n2.
 - apply add_0_n.
 - simpl.
   rewrite add_n_S.
   apply eq_S.
   apply IHn2.
Qed.


(* We can define multiplication recursively as repeated addition. *)

Fixpoint mult (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => O
  | S m1 => add n2 (mult m1 n2)
  end.

(*
 * PROBLEM 2 [8 points, ~35 tactics]
 *
 * Prove that multiplication is commutative, as stated by the lemma below.
 *
 * Hint: Proceed by induction.
 *
 * Hint: Don't use more than one induction inside a single proof.  Instead,
 * figure out lemmas that might be useful, and then prove those separately
 * (by induction, probably). See the style guide for more information.
 *
 * Hint: It might be useful to review all the lemmas about `add` in Homework 1.
 * Feel free to copy them over if you need to use them. You might need to
 * state and prove some analogous lemmas about `mult`.
 *
 * Hint: In order to prove your helpers about `mult`, you might need 1 or 2
 * additional facts about `add`.  Try to keep these simple, based on facts
 * you know from math, and prove them by induction.
 *)

Lemma mult_0_n:
 forall n, mult O n = O.
Proof.
 destruct n; simpl; reflexivity.
Qed.

Lemma mult_n_0:
 forall n, mult n O = O.
Proof.
 induction n; simpl.
 - reflexivity.
 - apply IHn.
Qed.

Lemma mult_n_1:
  forall n, mult n (S O) = n.
Proof.
  induction n; simpl.
  - reflexivity.
  - rewrite IHn; reflexivity.
Qed.


Lemma mult_n_S :
  forall n1 n2, mult n1 (S n2) = add n1 (mult n1 n2).
Proof.
  intros.
  induction n1; simpl.
  - reflexivity.
  - apply eq_S.
    rewrite IHn1.
    apply add_assoc.
Qed.

Lemma mult_comm :
  forall n1 n2,
    mult n1 n2 = mult n2 n1.
Proof.
  intros.
  induction n1.
  - rewrite mult_0_n.
    rewrite mult_n_0.
    reflexivity.
  - simpl.
    apply eq_sym.
    rewrite IHn1.
    apply mult_n_S.
Qed. (* Change to Qed when done *)


(*
 * PROBLEM 3 [10 points, ~25 tactics]
 *
 * State and prove that the `mult` function is associative.
 *
 * Hint: You'll probably need ~2 more lemmas about mult and/or add.
 *)
(* YOUR LEMMA STATEMENT AND PROOF HERE *)

Lemma add_sym :
  forall a b, add a b = add b a.
Proof.
  intros.
  induction a; simpl.
  - rewrite add_n_0; reflexivity.
  - rewrite IHa. apply eq_sym. apply add_n_S.
Qed.

Lemma add_S_n:
  forall n1 n2,
    add (S n1) n2 = S (add n1 n2).
Proof.
  intros.
  rewrite add_sym.
  rewrite add_n_S.
  apply eq_S.
  apply add_sym.
Qed. (* Change to Qed when done *)


Lemma add_right:
  forall a b c, c = b -> add a b = add a c.
Proof.
  intros a b c.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Lemma add_it :
  forall a b c d,
    add (add a b) (add c d) = add (add a c) (add b d).
Proof.
  intros.
  rewrite add_assoc.
  rewrite <- (add_sym d _).
  apply eq_sym.
  rewrite add_assoc.
  rewrite <- (add_sym d _).
  rewrite <- (add_assoc _ d).
  apply eq_sym.
  rewrite <- (add_assoc _ d).
  apply add_right.
  rewrite add_assoc.
  apply eq_sym.
  rewrite add_assoc.
  apply add_right.
  apply add_sym.
Qed.

Lemma mult_dist :
  forall a b c,
    mult a (add b c) = add (mult a b) (mult a c).
Proof.
  intros.
  induction a.
  - simpl. reflexivity.
  - simpl.
    rewrite IHa.
    rewrite add_it.
    reflexivity.
Qed.

Lemma mult_assoc :
  forall n1 n2 n3, mult n1 (mult n2 n3) = mult (mult n1 n2) n3.
Proof.
  intros.
  induction n1.
  - repeat rewrite mult_0_n.
    reflexivity.
  - simpl mult.
    apply eq_sym.
    rewrite mult_comm.
    rewrite mult_dist.
    rewrite IHn1.
    rewrite mult_comm.
    apply add_right.
    rewrite mult_comm.
    reflexivity.
Qed.


Lemma mult_assoc_2:
  forall n1 n2 n3, mult n1 (mult n2 n3) = mult n2 (mult n1 n3).
Proof.
  intros.
  induction n1.
  - repeat rewrite mult_0_n.
    rewrite mult_n_0.
    reflexivity.
  - simpl mult.
    rewrite mult_dist.
    rewrite IHn1.
    reflexivity.
Qed.

(* Here's the definition of `le` from lecture (and the standard library). *)
Inductive le (n : nat) : nat -> Prop :=
| le_n : le n n
| le_S : forall m, le n m -> le n (S m).

(*
 * PROBLEM 4 [10 points, ~9 tactics]
 *
 * State and prove the following:
 * If a <= b then a + c <= b + c
 *
 * Hint: Proceed by induction.
 *)
(* YOUR LEMMA STATEMENT AND PROOF HERE *)

Lemma add_le:
 forall a b c, le a b -> le (add a c) (add b c).
Proof.
 intros a b c Hle.
 induction Hle as [| m H' IH].
 - apply le_n.
 - rewrite add_S_n.
   apply le_S.
   exact IH.
Qed.

Lemma le_a_0:
  forall a, le a O -> a = O.
Proof.
  intros a.
  induction a.
  - intros; reflexivity.
  - intros HC.
    inversion HC.
Qed.

Lemma le_0:
 forall a, le O a.
Proof.
 induction a.
 - apply le_n.
 - apply le_S.
   apply IHa.
Qed.

Lemma le_transform :
  forall a b, le a b -> exists c, b = add a c.
Proof.
  intros a b H.
  induction H as [| m H' IH].
  - exists O. rewrite add_n_0. reflexivity.
  - destruct IH as [c Hc].
    exists (S c).
    rewrite Hc. rewrite add_n_S.
    reflexivity.
Qed.

Lemma left_S_le:
 forall a b, le (S a) b -> le a b.
Proof.
  intros a b H.
  induction H as [| m H' IH].
  - apply le_S. apply le_n.
  - apply le_S. exact IH.
Qed.

Lemma eq_le_S:
  forall a b, le (S a) (S b) -> le a b.
Proof.
  intros a b H.
  inversion H as [| b' H' IH].
  - apply le_n.
  - apply left_S_le.
    apply H'.
Qed.

Lemma eq_le_S_new:
  forall a b, le a b -> le (S a) (S b).
Proof.
  intros a b H.
  induction H as [| b' H' IH].
  - apply le_n.
  - apply le_S.
    apply IH.
Qed.

Lemma le_transitivity:
  forall a b c, le a b /\ le b c -> le a c.
Proof.
  intros a b c left_and_right.
  destruct left_and_right as [alb blc].
  induction alb as [| m alb' IH].
  - exact blc.
  - apply left_S_le in blc.
    apply IH.
    exact blc.
Qed.

Lemma eq_S_new:
  forall a b, S a = S b -> a = b.
Proof.
  intros a b H.
  inversion H.
  reflexivity.
Qed.

Lemma add_n_S_new:
  forall a b,  S (add a b) = add a (S b).
Proof.
  intros a b.
  rewrite add_n_S.
  reflexivity.
Qed.

Lemma add_find:
  forall a b, a = add b a -> b = O.
Proof.
  intros a b H.
  induction a.
  - rewrite add_n_0 in H.
    apply eq_sym.
    exact H.
  - apply IHa.
    apply eq_S_new.
    rewrite add_n_S_new.
    apply H.
Qed.

Lemma add_find_rev:
  forall a b, b = O -> a = add b a.
Proof.
  intros a b H.
  induction a.
  - rewrite add_n_0.
    apply eq_sym.
    exact H.
  - rewrite add_n_S.
    apply eq_S.
    apply IHa.
Qed.

Lemma not_eq_S:
  forall n m, S n <> m -> S (S n) <> S m.
Proof.
  intros n m H.
  unfold not in *.
  intro H1.
  apply H.
  inversion H1.
  reflexivity.
Qed.

Lemma seq_not_eq:
  forall n, S n <> n.
Proof.
  intros n.
  induction n.
  - discriminate.
  - apply not_eq_S.
    exact IHn.
Qed.

Lemma not_le_S_n:
  forall n, ~ le (S n) n.
Proof.
  induction n as [| n IH]; intros H.
  - inversion H.
  - apply eq_le_S in H. 
    contradict H.
    exact IH.
Qed.

Lemma squash:
  forall n m, le n m /\ le m n -> m = n.
Proof.
  intros n m left_and_right.
  destruct left_and_right as [nlm mln].
  induction nlm as [| m nlm' IH].
  - reflexivity.
  - apply eq_le_S_new in nlm'.
    assert (HT := conj nlm' mln).
    apply le_transitivity in HT.
    contradict HT.
    apply not_le_S_n.
Qed.

End Homework1_TimeTravel. (* return to the present *)

(*
 * Now that you've seen how nat, add, and mult are defined under the hood,
 * from now on we'll use the versions in Coq's standard library. These come
 * with nice notations like `1 + 3 * 4`, and with lots of free lemmas.
 *
 * There are also some useful tactics for working with arithmetic.
 *
 * Here are some automated proofs that the Coq standard library versions
 * of add and mult are commutative. (These lemmas are also in the standard
 * library, but we prove them from scratch just to demonstrate the tactics.)
 *)

Lemma add_comm_again :
  forall a b, a + b = b + a.
Proof.
  intros.
  lia.
Qed.

Lemma mult_comm_again :
  forall a b, a * b = b * a.
Proof.
  intros.
  ring.
Qed.

(*
 * PROBLEM 5 [4 points, ~5 tactics]
 *
 * Prove this simple fact about and.
 *
 * Hint: Review tactics that are useful for taking apart hypotheses.
 *
 * Hint: Review tactics that are useful for decomposing goals.
 *
 * Hint: Our solution uses little automation. If you feel like it, you can solve
 * it with ~1 tactic as well, using automation.
 *)
Lemma and_comm :
  forall (A B : Prop),
    A /\ B ->
    B /\ A.
Proof.
  intros A B AB.
  split; destruct AB as [HA HB].
  - exact HB.
  - exact HA.
Qed. (* Change to Qed when done *)

Lemma and_comm_easy:
  forall (A B : Prop),
    A /\ B ->
    B /\ A.
Proof.
  easy.
Qed. (* Change to Qed when done *)

(*
 * PROBLEM 6 [4 points, ~7 tactics]
 *
 * Prove this simple fact about or.
 *
 * Hint: Review tactics that are useful for taking apart hypotheses.
 *
 * Hint: Review tactics that are useful for decomposing goals.
 *
 * Hint: Our solution uses little automation. If you feel like it, you can solve
 * it with ~1 tactic as well, using automation.
 *)

Lemma or_comm_intuition:
  forall (A B : Prop),
    A \/ B ->
    B \/ A.
Proof.
  intuition.
Qed. (* Change to Qed when done *)

Lemma or_comm :
  forall (A B : Prop),
    A \/ B ->
    B \/ A.
Proof.
  intros A B AB.
  destruct AB as [HA | HB].
  - right. apply HA.
  - left. apply HB.
Qed. (* Change to Qed when done *)

(* Here is an inductive definition of evenness for natural numbers. *)
Inductive even : nat -> Prop :=
| even_O : even O
| even_SS : forall n, even n -> even (S (S n)).

(*
 * There are two constructors that can prove even. 0 is even. And a number of
 * the form S (S n) is even if n is even.
 *)

(*
 * PROBLEM 7 [9 points, ~3 sentences]
 *
 * Write a comment answering the following questions.
 *
 * (a) If n is a nat in Coq, how many constructors of the type nat (O or S) is
 *     it built with? How many of those are S constructors and how many are O?
 *
 * (b) If n is a nat in Coq, and pf is a proof of even n, how many constructors
 *     of the proposition even is pf built with? How many are even_O and how
 *     many are even_SS?
 *
 * (c) If n is a nat in Coq, and n is odd, explain intuitively why your answer
 *     to part (b) implies that there is no proof of "even n".
 *
 * Hint: Your answer to part (a) should be three quantities: how many
 * constructors total, how many are O, and how many are S? Each quantity should
 * be expressed in terms of n. For example, one (wrong) answer would be "There
 * are n / 3 + 7 constructors total, n / 3 are O, and 7 are S."
 *
 * Hint: Your answer to part (b) should be of a similar "shape" to part (a):
 * three quantities expressed in terms of n.
 *)
(*
 * (a) 1 O constructors and n S constructors. n + 1 constructors in total.
 * (b) 1 even_O constructors and n / 2 even_SS constructors. n / 2 + 1 constructors in total.
 * (c) Intuitively, because we cannot divide odd number by 2.
 *)

(* Here is a function that returns twice its argument. *)
Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S m => S (S (double m))
  end.

(*
 * PROBLEM 8 [4 points, ~5 tactics]
 *
 * Prove that double always returns an even number.
 *
 * Hint: Proceed by induction.
 *)
Lemma double_even :
  forall n,
    even (double n).
Proof.
  induction n as [| n IH].
  - simpl. apply even_O.
  - simpl double. apply even_SS. apply IH.
Qed. (* Change to Qed when done *)

(*
 * PROBLEM 9 [4 points, ~2 sentences]
 *
 * Consider the following lemma, which says that every even number is the output
 * of double on some input.
 *
 * Attempt to prove this lemma by induction on n. No need to turn in your
 * partial proof.
 *
 * Explain in a comment where you get stuck.
 *)

Lemma even_SS_reverse:
  forall n, even (S (S n)) -> even n.
Proof.
  intros n H. 
  inversion H.
  apply H1.
Qed.

Lemma or_not_and :
  forall A B ,
    ~A \/ ~B -> ~ (A /\ B).
Proof.
  intros A B H.
  destruct H as [NA | NA];
  intro HAB;
  destruct HAB as [HA HB];
  contradiction.
Qed.

Lemma even_odd :
  forall n, ~ (even n /\ even (S n)).
Proof.
  intros n.
  induction n.
  - apply or_not_and.
    right.
    unfold not.
    intros.
    inversion H.
  - unfold not.
    intros.
    destruct H as [ HSN HSSN ].
    apply even_SS_reverse in HSSN.
    assert (H3 := conj HSSN HSN).
    contradiction H3.
Qed.

Require Import Classical.

Lemma even_double :
  forall n,
    even n ->
    exists k,
      n = double k.
Proof.
  induction n as [| n IH].
  - exists 0. reflexivity.
  - destruct (classic (even n)) as [ HA | HNA ].
    + intros EV.
      assert (C := conj HA EV).
      contradict C.
      apply even_odd.
    + 
Abort.
(* YOUR ANSWER HERE *)
(*
   I cannot prove it by induction on natural numbers because I
   cannot reuse result from the previous induction step. I should make 
   steps in 2 numbers, then it may be possible.
 *)

(* Like prove 2 base cases and then I can make steps by 2 *)
Theorem nat_ind2 : 
  forall P : nat -> Prop,
  P 0 -> 
  P 1 -> 
  (forall n : nat, P n -> P (S (S n))) -> 
  forall n : nat, P n.
Proof.
  intros P H0 H1 Hstep n.
  enough (P n /\ P (S n)) as [Hn _].
  - exact Hn.
  - induction n as [|n IH].
    + split.
      * exact H0.
      * exact H1.
    + destruct IH as [IHn IHn1].
      split.
      * exact IHn1.
      * apply Hstep. exact IHn.
Qed.

Lemma even_double_nat_ind2:
  forall n,
    even n ->
    exists k,
      n = double k.
Proof.
  induction n as [| | n IH] using nat_ind2.
  - exists 0. reflexivity.
  - intros H.
    inversion H.
  - intros H.
    apply even_SS_reverse in H.
    apply IH in H.
    destruct H as [c cH].
    exists (S c).
    simpl.
    repeat apply eq_S.
    exact cH.
Qed.


(*
 * PROBLEM 10 [5 points, ~9 tactics]
 *
 * Now prove the lemma by induction on the derivation of even n.
 *)
Lemma even_double :
  forall n,
    even n ->
    exists k,
      n = double k.
Proof.
  intros n even.
  induction even as [| n even' IH].
  - exists 0. reflexivity.
  - destruct IH as [c cH].
    exists (S c).
    simpl.
    rewrite cH.
    reflexivity.
Qed. (* Change to Qed when done *)

(*
 * PROBLEM 11 [5 points, ~6 tactics]
 *
 * Prove that the sum of two even numbers is even.
 *
 * Hint: What should you induct on?
 *)
Lemma plus_even :
  forall x y,
    even x ->
    even y ->
    even (x + y).
Proof.
  intros x y EX EY.
  induction EX as [|x EX' IH].
  - simpl. exact EY.
  - repeat rewrite plus_Sn_m.
    apply even_SS.
    exact IH.
Qed. (* Change to Qed when done *)

(*
 * PROBLEM 12 [5 points, ~4 tactics]
 *
 * Prove that 3 is not even.
 *
 * Hint: No need for induction. "Call Coq's bluff".
 *)
Lemma three_not_even :
  even 3 -> False.
Proof.
  intros H.
  inversion H.
  inversion H1.
Qed. (* Change to Qed when done *)

Module Data_Structures.
Set Implicit Arguments.

(* --- List practice --- *)

(* Here are some definitions copied from the Coq standard library. *)
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

(*
 * PROBLEM 13 [12 points, ~15 tactics]
 *
 * Prove the following theorem about the length of a reversed list.
 *
 * Hint: Proceed by induction on l.
 *
 * Hint: You'll need a helper lemma!
 *)

 Lemma append_len_sum:
   forall A (l1 l2: list A), 
     length (l1 ++ l2) = length l1 + length l2.
 Proof.
   intros A l1 l2.
   induction l1.
   - reflexivity.
   - simpl.
     apply eq_S.
     assumption.
 Qed.


Lemma length_rev :
  forall A (l : list A),
    length (rev l) = length l.
Proof.
  induction l as [| head tail IH].
  - reflexivity.
  - simpl.
    rewrite append_len_sum.
    simpl.
    rewrite IH.
    apply Nat.add_1_r.
Qed.

(*
 * Here is a function that adds up all the elements of a list of nats.
 *)
Fixpoint sum_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

(*
 * And here are two functions that computes the same result with tail recursion.
 *)
Fixpoint sum_list_tr (l : list nat) (acc : nat) : nat :=
  match l with
  | [] => acc
  | x :: xs => sum_list_tr xs (x + acc)
  end.

Definition sum_list_tailrec (l : list nat) : nat :=
  sum_list_tr l 0.

(*
 * PROBLEM 14 [5 points, ~1 sentences]
 *
 * Consider the following theorem about the two ways of summing a list. You will
 * be asked to prove it in the next problem. For now, make a proof attempt that
 * proceeds directly by induction on `l`, without any nested inductions or
 * extra lemmas. At some point, you should get stuck.
 *
 * Write a sentence or two explaining why your proof attempt fails. Focus on the
 * induction hypothesis and whether it gives you enough information to complete
 * the proof.
 *
 * There is no need to turn in your proof attempt. Just turn in your
 * explanation.
 *
 * Hint: The base case should be provable.
 *
 * Hint: You might be able to make slightly more progress if you use the
 * `unfold` tactic to see inside the definition of `sum_list_tailrec`.
 *)
Theorem sum_list_tailrec_ok : forall l,
  sum_list_tailrec l = sum_list l.
Proof.
  unfold sum_list_tailrec.
  induction l as [| head tail IH].
  - reflexivity.
  - simpl.
    rewrite Nat.add_0_r.
    unfold sum_list_tailrec in IH.
Abort.
  (* YOUR EXPLANATION HERE (no need to prove it yet!) *)

(*
 * PROBLEM 15 [8 points, ~15 tactics]
 *
 * Now fix your broken proof by backing up and stating and proving a more
 * general helper lemma. Then use your helper lemma to finish the proof.
 *
 * Hint: Since `sum_list_tailrec` is defined in terms of the recursive function
 * `sum_list_tr`, it makes sense for your lemma to be about `sum_list_tr`.
 *
 * Hint: Your lemma should be proved by induction.
 *
 * Hint: Your fixed proof of `sum_list_tailrec_ok` should *not* use induction.
 *)

Lemma separate_sum_tr:
  forall l a, a + sum_list l = sum_list_tr l a.
Proof.
  induction l as [| head tail IH]; intro; simpl; auto.

  rewrite <- IH.
  rewrite Nat.add_assoc.
  rewrite <- (Nat.add_comm _ a).
  reflexivity.
Qed.

Lemma separate_sum_tr_2:
  forall l a b, sum_list_tr l (a + b) = a + sum_list_tr l b.
Proof.
  induction l as [| head tail IH]; intros; auto.
  simpl.
  repeat rewrite IH.
  lia.
Qed.

Theorem sum_list_tailrec_ok : forall l,
  sum_list_tailrec l = sum_list l.
Proof.
  intros.
  unfold sum_list_tailrec.
  rewrite plus_n_O.
  rewrite Nat.add_comm.
  apply eq_sym.
  apply separate_sum_tr.
Qed. (* Change to Qed when done *)

(* --- Binary Tree practice --- *)

Inductive tree (A : Type) : Type :=
| Leaf
| Node : tree A -> A -> tree A -> tree A.
Arguments Leaf {A}.

Fixpoint reverse {A} (t : tree A) : tree A :=
  match t with
  | Leaf => Leaf
  | Node l d r => Node (reverse r) d (reverse l)
  end.

(*
 * PROBLEM 16 [5 points, ~5 LOC]
 *
 * Define a function that adds up all the elements of a tree of nats.
 *)
Fixpoint sum_tree (t : tree nat) : nat :=
  match t with
  | Leaf => 0
  | Node l d r => d + (sum_tree l) + (sum_tree r)
  end.

(*
 * PROBLEM 17 [5 points, ~5 tactics]
 *
 * Prove that `reverse` has no effect on the sum of the elements in a tree.
 *)
Lemma sum_tree_reverse :
  forall t,
    sum_tree (reverse t) = sum_tree t.
Proof.
  induction t; simpl; auto.

  rewrite IHt1.
  rewrite IHt2.
  lia.
Qed. (* Change to Qed when done *)

(*
 * PROBLEM 18 [12 points, ~20 tactics]
 *
 * Prove the following similar lemma about `sum_list` and `rev`.
 *
 * Hint: Proceed by induction on l.
 *
 * Hint: You'll need a helper lemma about sum_list.
 *)


Lemma sum_list_split :
  forall l1 l2,
    sum_list (l1 ++ l2) = sum_list l1 + sum_list l2.
Proof.
  induction l1 as [| head tail IH]; intros; simpl; auto.
  rewrite IH.
  lia.
Qed.

Lemma sum_list_rev :
  forall l,
    sum_list (rev l) = sum_list l.
Proof.
  induction l as [| head tail IH]; simpl; auto.
  rewrite sum_list_split.
  rewrite IH.
  simpl.
  rewrite Nat.add_0_r.
  rewrite Nat.add_comm.
  reflexivity.
Qed. (* Change to Qed when done *)

End Data_Structures.

(*
 * PROBLEM 19 [5 points, ~3 sentences]
 *
 * Please take a moment to let us know how the homework went for you by
 * answering the following three questions:
 *    1. How long did the homework take you?
 *    2. Which parts were most interesting or helpful for you?
 *    3. Which parts were especially frustrating, confusing, or tedious?
 *       What should we do better next time?
 *
 * It's fine if your answers are short if you don't have much to say!
 *)

(* Your feedback here! *)

(*
1. Homework took a lot of hours
2. I personally took adjasent branch at the start and enjoyed it a lot.
   Also I think `sum_list_tailrec_ok` was quite helpful for me.
3. `sum_list_tailrec_ok` was really difficult for me. I had bad idea
   and wasted a lot of time on it. I think it is my fault though
*)


(* --- End of Core Points --- *)

(*
 * This is the end of the core points available for Homework 2. See below for
 * challenge points.
 *
 * To submit your homework, please follow the instructions at the end of the
 * README.md file in this directory.
 *
 * Please also see the README.md file to read about how we will grade this
 * homework assignment.
 *)

(*
             ____                  _     _                     ____
            / ___|    ___    ___  | |_  (_)   ___    _ __     |___ \
            \___ \   / _ \  / __| | __| | |  / _ \  | '_ \      __) |
             ___) | |  __/ | (__  | |_  | | | (_) | | | | |    / __/
            |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |_____|

                          SECTION 2 : Challenge Problem
*)

(*
 * CHALLENGE 20 [10 points, ~20 tactics]
 *
 * Give an alternative characterization of evenness as follows.
 *)
Lemma even_iff_exists_half_left: 
  forall n,
    even n -> exists k, n = 2 * k.
Proof.
 induction n using nat_ind2.
  - exists 0. auto.
  - intros H. inversion H.
  - intros H.
    apply even_SS_reverse in H.
    apply IHn in H.
    destruct H as [c cH].
    exists (S c).
    rewrite cH.
    lia.
Qed.

Lemma mul_2_not_1:
  forall n,
    1 <> 2 * n.
Proof.
  destruct n; simpl; auto.

  rewrite <- plus_n_Sm.
  rewrite <- plus_n_O.
  auto.
Qed.

Lemma even_iff_exists_half_right: 
  forall n,
   (exists k, n = 2 * k) -> even n.
Proof.
 induction n using nat_ind2.
  - intros.
    apply even_O.
  - intros.
    inversion H.
    contradict H0.
    apply mul_2_not_1.
  - intros.
    assert (Hm: exists k : nat, n = 2 * k).
    + destruct H as [c cH].
      destruct c. inversion cH.
      exists c.
      simpl.
      rewrite <- plus_n_O.
      simpl in cH.
      rewrite <- plus_n_O in cH.
      rewrite <- plus_n_Sm in cH.
      repeat apply Nat.succ_inj in cH.
      exact cH.
    + apply IHn in Hm.
      apply even_SS.
      exact Hm.
Qed.

Lemma even_iff_exists_half :
  forall n,
    even n <-> exists k, n = 2 * k.
Proof.
  split.
  - apply even_iff_exists_half_left.
  - apply even_iff_exists_half_right.
Qed.

(*
 * CHALLENGE 21 [20 points, ~8 tactics]
 *
 * In class we saw a proof that Peirce's law implies the law of excluded middle.
 * Now prove the reverse direction
 *
 * Hint: This way should be easier than the proof from lecture.
 *)
Lemma lem_implies_peirce :
  (forall P : Prop, P \/ ~P) -> forall P Q : Prop, ((P -> Q) -> P) -> P.
Proof.
  intros OR P Q A1.
  destruct OR with P as [ HP | HP ].
  - apply HP.
  - assert (CONT: P -> Q).
   + intros HNP. contradict HNP. apply HP.
   + apply A1 in CONT.
     apply CONT.
Qed. (* Change to Qed when done *)
