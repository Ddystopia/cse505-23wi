(*

    _   _    ___    __  __   _____  __        __   ___    ____    _  __    _
   | | | |  / _ \  |  \/  | | ____| \ \      / /  / _ \  |  _ \  | |/ /   / |
   | |_| | | | | | | |\/| | |  _|    \ \ /\ / /  | | | | | |_) | | ' /    | |
   |  _  | | |_| | | |  | | | |___    \ V  V /   | |_| | |  _ <  | . \    | |
   |_| |_|  \___/  |_|  |_| |_____|    \_/\_/     \___/  |_| \_\ |_|\_\   |_|


*)


(*
 * This homework assignment is a tutorial introduction to Coq.
 *
 * Set up Coq as described in README.md. Then step through this file with VSCode
 * (or another IDE for Coq), and complete the problems. Search for "PROBLEM" to
 * be sure you find them all---not all problems correspond to Coq code!
 *
 * Throughout, we include the approximate lines of code (LOC) or number of
 * tactics for each of our solutions to these problems.  These are rough
 * guidelines to help you figure out if you are getting off track.
 *
 * There is no penalty for writing a shorter or longer solution! However, if
 * you find yourself writing a much longer solution, you might save yourself
 * some time by taking a step back and seeing if you can find a simpler way.
 *
 * Every problem on this homework is designed to be conceptually
 * straightforward; the hard part is just getting up to speed on Coq.
 *
 * There are 9 problems worth a total of 50 points.
 *
 * See the bottom of README.md for quite a bit more information, including some
 * advice on how to do this homework, how this homework will be graded, and a
 * list of tactics used in our solution.
 *)

(* --- Setting up Coq --- *)

(*
 * PROBLEM 1 [0 points, ~1 LOC]
 * Set up Coq as described in README.md
 *
 * Once Coq is installed according to directions, you should be able to step
 * through this entire file in your IDE.
 *
 * We will always have a non-problem PROBLEM 1, because Gradescope makes the
 * autograder results "Problem 1" :)
 *
 * You've heard of computer scientists counting from zero, but have you heard of
 * them counting from two?!
 *)

(* infer type arguments *)
Set Implicit Arguments.

(* --- Boolean practice --- *)

(* Here are some definitions about booleans from lecture.  *)

Inductive bool : Type :=
| true : bool
| false : bool.

Definition notb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.


(*
 * PROBLEM 2 [4 points, ~5 LOC]
 * Write a function called `orb` that implements boolean disjunction.
 *
 * Hint: Kinda like `andb`, but different.
 *)
Definition orb (b1 : bool) (b2 : bool) : bool :=
  false. (* YOUR CODE HERE *)


(*
 * Remember that `Compute` just runs programs.
 * We can use it for simple testing.
 *)
Compute orb true true.   (* should be true. *)
Compute orb true false.  (* should be true. *)
Compute orb false true.  (* should be true. *)
Compute orb false false. (* should be false. *)


(*
 * PROBLEM 3 [4 points, ~15 tactics]
 * Prove the following theorem, that `orb` is commutative.
 *
 * Hint: Kinda like `andb_comm` from lecture.
 * Hint: You may need fewer tactics if you use semicolon chains.
 *)
Lemma orb_comm :
  forall b1 b2,
    orb b1 b2 = orb b2 b1.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


(*
 * PROBLEM 4 [4 points, ~7 tactics]
 * Prove the following theorem about `notb`, `orb`, and `andb`.
 *
 * Hint: You may need fewer tactics if you use semicolon chains.
 * Hint: All these proofs start to look the same after a while...
 *)
Lemma notb_andb_is_orb_notb :
  forall b1 b2,
    notb (andb b1 b2) = orb (notb b1) (notb b2).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


(* --- Natural numbers practice --- *)

(*
 * Here are some more definitions from lecture,
 * this time about natural numbers.
 *)

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Fixpoint add (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => n2
  | S m1 => S (add m1 n2)
  end.


(*
 * PROBLEM 5 [4 points, ~4 tactics]
 * Prove the following theorem about add.
 *
 * Hint: Do you think you'll need induction? Hmm...
 *)
Lemma add_S_n :
  forall n1 n2,
    add (S n1) n2 = S (add n1 n2).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


(*
 * PROBLEM 6 [8 points, ~1 sentences]
 * Consider the following theorem, superficially similar to the previous one.
 *
 * The problem below asks you to prove it, but before that, describe here
 * whether you expect it to be less difficult than, more difficult than,
 * or about the same difficulty as the previous theorem.
 *
 * Please explain your answer in 1 to 2 sentences, using your mental model
 * for what kinds of things different tactics are good at.
 *
 * Hint: If you don't know, it's okay to try to prove it (the next problem
 *       below), and then come back and explain the outcome.
 *)
Lemma add_n_S :
  forall n1 n2,
    add n1 (S n2) = S (add n1 n2).
Proof.
Abort.
  (* YOUR EXPLANATION HERE (no need to prove it yet!) *)


(*
 * PROBLEM 7 [8 points, ~8 tactics]
 * Now go ahead and prove the theorem from the previous problem
 * (restated below).
 *
 * Hint: You may need fewer tactics than we did if you use semicolon chains.
 *
 * Hint: Do you think you'll need induction? Hmm...
 *)
Lemma add_n_S :
  forall n1 n2,
    add n1 (S n2) = S (add n1 n2).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


(*
 * PROBLEM 8 [15 points, ~20 tactics]
 * Prove the following theorem about add.
 *
 * Hint: Proceed by induction.
 *
 * Hint: Don't forget to reuse previously proved Lemmas by using
 *       the `rewrite` tactic.
 *
 * Hint: It's okay to copy-paste lemmas we proved in lecture if you need them.
 *)
Lemma add_comm :
  forall n1 n2,
    add n1 n2 = add n2 n1.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * PROBLEM 9 [3 points, ~3 sentences]
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
 * This is the end of Homework 1.  It's never too early to get started on
 * Homework 2!
 *
 * To submit your homework, please follow the instructions at the end of the
 * README.md file in this directory.
 *
 * Please also see the README.md file to read about how we will grade this
 * homework.
 *)
