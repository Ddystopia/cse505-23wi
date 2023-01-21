(*

  _   _    ___    __  __   _____  __        __   ___    ____    _  __    _____
 | | | |  / _ \  |  \/  | | ____| \ \      / /  / _ \  |  _ \  | |/ /   |___ /
 | |_| | | | | | | |\/| | |  _|    \ \ /\ / /  | | | | | |_) | | ' /      |_ \
 |  _  | | |_| | | |  | | | |___    \ V  V /   | |_| | |  _ <  | . \     ___) |
 |_| |_|  \___/  |_|  |_| |_____|    \_/\_/     \___/  |_| \_\ |_|\_\   |____/


Welcome back! This homework covers abstract syntax trees, transition
systems, and a little bit of Imp. We don't expect you to be able to
do the Imp problems until after Tuesday of Week 5. But everything else
(including all challenge points) should be doable after Thursday of Week 4.

There are 26 problems worth a total of 150 points.

*)


Require Import Arith Lia List String.
Import ListNotations.
Open Scope string.

Set Implicit Arguments.

(*
 * PROBLEM 1 [0 points, ~0 tactics]
 *
 * Fake problem to make Gradescope numbers match problem numbers.
 *)
(* Nothing to do here. *)

(*
               ____                  _     _                     _
              / ___|    ___    ___  | |_  (_)   ___    _ __     / |
              \___ \   / _ \  / __| | __| | |  / _ \  | '_ \    | |
               ___) | |  __/ | (__  | |_  | | | (_) | | | | |   | |
              |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |_|

                        SECTION 1 : Abstract Syntax Trees
*)

Module AST.

(*
 * Here is a definition for a kind of binary tree, which we'll call
 * an `optree`. There are a couple of differences from the binary
 * trees we saw on homework 2:
 *   1. The data is now stored in the leaves (which we call `Const`).
 *   2. There are two kinds of internal nodes, called `Plus` and `Times`.
 *)
Inductive optree : Set :=
| Const (n : nat)
| Plus  (e1 e2 : optree)
| Times (e1 e2 : optree).

(*
 * Here's a function that kind of sums up the constants in the `optree`,
 * just like `sum_tree` did on homework 2. The difference is that at a
 * `Times` node, we multiply the values instead of adding them.
 *)
Fixpoint kinda_sum (e : optree) : nat :=
  match e with
  | Const n => n
  | Plus e1 e2 => kinda_sum e1 + kinda_sum e2
  | Times e1 e2 => kinda_sum e1 * kinda_sum e2
end.

(*
 * The cool thing about `kinda_sum` is it turns `optree` into a kind of
 * programming language (albeit incredibly simple). Check it out!
 *)
Compute kinda_sum (Plus (Const 1) (Const 1)).  (* 2 *)
Compute kinda_sum (Times (Const 2) (Const 3)). (* 6 *)

(*
 * It's worth reflecting on the differences between `tree nat` "interpreted" by
 * `sum_tree` versus `optree` interpreted by `kinda_sum`.
 *
 * Most people would probably not call `tree nat` a "programming language", but
 * our gut reaction about `optree` is different! It feels like programming all
 * of a sudden. But if you think about it, there's really not much  difference
 * between the "data" of a `tree nat` and the "program" of an `optree`.
 *
 * To sum up (heh), `kinda_sum` is an interpreter! We'll keep calling it
 * `kinda_sum` for a while, just for fun.
 *)


(*
 * Here's a function that "reverses" an `optree`.
 *
 * Since we think of `optree`s as programs, it's fair to say `commuter` is a
 * *program transformation*, similar to those that might happen inside the
 * optimizer of a compiler!
 *)

Fixpoint commuter (e : optree) : optree :=
  match e with
  | Const n => e
  | Plus e1 e2 => Plus (commuter e2) (commuter e1)
  | Times e1 e2 => Times (commuter e2) (commuter e1)
end.

(*
 * PROBLEM 2 [5 points, ~7 tactics]
 *
 * Prove the following theorem about kinda_sum and commuter, which
 * says that the program transformation preserves the semantics of
 * the `optree`.
*)
Lemma kinda_sum_commuter :
  forall e, kinda_sum e = kinda_sum (commuter e).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * The next problem is a bit more challenging, but you will get to continue to
 * play the video game called Coq. You already have all the techniques you
 * need to solve it, but it is slightly longer than the previous problems.
 *)

(*
 * We can define another program version, this time a version of the famous
 * "constant folding" program transformation from compilers.
 *)


Fixpoint constant_fold (e : optree) : optree :=
  match e with
  | Const _ => e
  | Plus e1 e2 =>
    let e1' := constant_fold e1 in
    let e2' := constant_fold e2 in
    match e1', e2' with
      | Const n1, Const n2 => Const (n1 + n2)
      | Const 0, _ => e2'
      | _, Const 0 => e1'
      | _, _ => Plus e1' e2'
    end
  | Times e1 e2 =>
    let e1' := constant_fold e1 in
    let e2' := constant_fold e2 in
    match e1', e2' with
      | Const n1, Const n2 => Const (n1 * n2)
      | Const 1, _ => e2'
      | _, Const 1 => e1'
      | Const 0, _ => Const 0
      | _, Const 0 => Const 0
      | _, _ => Times e1' e2'
    end
end.

(*
 *PROBLEM 3 [12 points, ~25 tactics]
 *
 * Prove that `constant_fold` preserves semantics.
 *
 * Hint: Sometimes `rewrite <-` is useful.
 *
 * Hint: There are many repetitive cases. Try to strike a balance
 * between using semicolons and automation to alleviate tedium versus
 * spending a million hours reducing the proof into one magical
 * undebuggable line.
 *)
Lemma kinda_sum_constant_fold :
  forall e,
    kinda_sum (constant_fold e) = kinda_sum e.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done. *)

End AST.

(*
             ____                  _     _                     ____
            / ___|    ___    ___  | |_  (_)   ___    _ __     |___ \
            \___ \   / _ \  / __| | __| | |  / _ \  | '_ \      __) |
             ___) | |  __/ | (__  | |_  | | | (_) | | | | |    / __/
            |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |_____|

                            SECTION 2 : Interpreters
*)

Module Interpreters.

(* PROBLEM 4 [2 points, ~1 tactics]
 *
 * Define a function that sums the natural numbers up to (and including) n.
 *)
Fixpoint sum_upto (n : nat) : nat :=
  0. (* YOUR CODE HERE *)

(* Copied from Week 3 lecture code *)
Definition eq_dec (A : Type) :=
  forall (x : A),
    forall (y : A),
      {x = y} + {x <> y}.

Notation var := string.
Definition var_eq : eq_dec var := string_dec.

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).
Declare Scope arith_scope. (* defines a name for our collection of notations *)
Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Infix "+" := Plus : arith_scope.
Infix "-" := Minus : arith_scope.
Infix "*" := Times : arith_scope.
Delimit Scope arith_scope with arith. (* lets us use "%arith" annotations *)
Bind Scope arith_scope with arith.

Definition valuation := list (var * nat).

Fixpoint lookup (x : var) (v : valuation) : option nat :=
  match v with
  | [] => None
  | (y, n) :: v' =>
    if var_eq x y
    then Some n
    else lookup x v'
  end.

Fixpoint eval_arith (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
      match lookup x v with
        | None => 0
        | Some n => n
      end
  | Plus  e1 e2 => eval_arith e1 v + eval_arith e2 v
  | Minus e1 e2 => eval_arith e1 v - eval_arith e2 v
  | Times e1 e2 => eval_arith e1 v * eval_arith e2 v
  end.

Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| Repeat (e : arith) (body : cmd).

Fixpoint do_n_times {A} (f : A -> A) (n : nat) (x : A) : A :=
  match n with
  | O => x
  | S n' => do_n_times f n' (f x)
  end.

Fixpoint eval_cmd (c : cmd) (v : valuation) : valuation :=
  match c with
  | Skip => v
  | Assign x e => (x, eval_arith e v) :: v
  | Sequence c1 c2 => eval_cmd c2 (eval_cmd c1 v)
  | Repeat e body => do_n_times (eval_cmd body) (eval_arith e v) v
  end.

Declare Scope cmd_scope.
Delimit Scope cmd_scope with cmd.
Bind Scope cmd_scope with cmd.
Notation "x <- e" := (Assign x e%arith) (at level 75) : cmd_scope.
Infix ";" := Sequence (at level 76) : cmd_scope.
Notation "'repeat' e 'doing' body 'done'" :=
  (Repeat e%arith body) (at level 75) : cmd_scope.

Definition map_equiv m1 m2 := forall v, lookup v m1 = lookup v m2.

Ltac solve_map_cases :=
  unfold map_equiv; intros; simpl;
  repeat destruct (var_eq _ _); try congruence.

(* End copied stuff *)

Definition sum_n : cmd :=
  "output" <- 0;
  repeat "input" doing
    "output" <- "output" + "input";
    "input" <- "input" - 1
  done.

(* PROBLEM 5 [20 points, ~35 tactics]
 *
 * Prove this lemma that states that our `sum_n` command
 * results in the same output value as `sum_upto`.
 *
 * Hint: You might want to define and prove a helper lemma about
 * the loop body.
 *)
Theorem sum_n_ok :
  forall v input,
    lookup "input" v = Some input ->
    lookup "output" (eval_cmd sum_n v) = Some (sum_upto input).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done. *)

End Interpreters.

(*
             ____                  _     _                     _____
            / ___|    ___    ___  | |_  (_)   ___    _ __     |___ /
            \___ \   / _ \  / __| | __| | |  / _ \  | '_ \      |_ \
             ___) | |  __/ | (__  | |_  | | | (_) | | | | |    ___) |
            |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |____/

                         SECTION 3 : Transition Systems
*)

(* Copied from Week 4 lecture code. *)

Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| trc_refl :
    forall x,
      trc R x x
| trc_front :
    forall x y z,
      R x y ->
      trc R y z ->
      trc R x z.

Lemma trc_transitive :
  forall {A} (R : A -> A -> Prop) x y,
    trc R x y ->
    forall z,
      trc R y z ->
      trc R x z.
Proof.
  intros A R x y Hxy.
  induction Hxy; auto.
  econstructor; eauto.
Qed.

Record trsys state :=
  { Init : state -> Prop
  ; Step : state -> state -> Prop }.

Definition is_invariant {state} (sys : trsys state) (P : state -> Prop) :=
  forall s0,
    sys.(Init) s0 ->
    forall sN,
      trc sys.(Step) s0 sN ->
      P sN.

Definition initially_holds {state} (sys : trsys state) (P : state -> Prop) :=
  forall s,
    sys.(Init) s ->
    P s.

Definition closed_under_step {state} (sys : trsys state) (P : state -> Prop) :=
  forall s1,
    P s1 ->
    forall s2,
      sys.(Step) s1 s2 ->
      P s2.

Lemma closed_under_step_trc :
  forall {state} (sys : trsys state) (P : state -> Prop) s0 sN,
    trc sys.(Step) s0 sN ->
    closed_under_step sys P ->
    P s0 ->
    P sN.
Proof.
  unfold closed_under_step.
  intros state sys P s0 sN Htrc.
  induction Htrc; intros Hclosed HP0.
  - assumption.
  - apply IHHtrc; auto.
    eapply Hclosed; eauto.
Qed.

Theorem invariant_induction :
  forall {state} (sys : trsys state) (P : state -> Prop),
    initially_holds sys P ->
    closed_under_step sys P ->
    is_invariant sys P.
Proof.
  unfold is_invariant. intros.
  eapply closed_under_step_trc; eauto.
Qed.

Definition reachable {state} (sys : trsys state) (sN : state) : Prop :=
  exists s0,
    sys.(Init) s0 /\
    trc sys.(Step) s0 sN.

Theorem by_invariant :
  forall {state} (sys : trsys state) (P : state -> Prop) s,
    is_invariant sys P ->
    reachable sys s ->
    P s.
Proof.
  unfold is_invariant.
  intros state sys P s Hinv Hreach.
  destruct Hreach as [s0 [Hinit Htrc]].
  eapply Hinv; eauto.
Qed.

Lemma reachable_transitive :
  forall {state} (sys : trsys state) s1 s2,
    reachable sys s1 ->
    trc sys.(Step) s1 s2 ->
    reachable sys s2.
Proof.
  unfold reachable.
  intros state sys s1 s2 [s0 [Hinit Htrc01]] Htrc12.
  exists s0.
  split; auto.
  eapply trc_transitive; eauto.
Qed.

Lemma invariant_implies :
  forall {state} (sys : trsys state) (P Q : state -> Prop),
    is_invariant sys P ->
    (forall s, P s -> Q s) ->
    is_invariant sys Q.
Proof.
  unfold is_invariant.
  eauto.
Qed.

Lemma invariant_and :
  forall {state} (sys : trsys state) (P Q : state -> Prop),
    is_invariant sys P ->
    is_invariant sys Q ->
    is_invariant sys (fun s => P s /\ Q s).
Proof.
  unfold is_invariant.
  eauto.
Qed.

Ltac unfold_predicate P :=
  match P with
  | ?head _ => unfold_predicate head
  | _ => try unfold P
  end.

Ltac invariant_induction_boilerplate :=
  intros;
  apply invariant_induction; [
    unfold initially_holds; simpl;
    match goal with
    | [ |- forall _, ?P _ -> ?Q _ ] =>
      unfold_predicate P;
      unfold_predicate Q;
      intros s Hinit;
      try subst
    end
  |
    unfold closed_under_step; simpl;
    match goal with
    | [ |- forall _, ?P _ -> forall _, ?Q _ _ -> _ ] =>
      unfold_predicate P;
      unfold_predicate Q;
      intros s1 IH s2 Hstep;
      try inversion Hstep;
      try subst
    end
  ].

(* End of copied stuff. *)

(*
 * PROBLEM 6 [5 points, ~15 tactics]
 *
 * The inductive definition of trc allows us to "add steps to the front" using
 * the trc_front constructor. Prove the following lemma, which says that we can
 * also add steps to the back.
 *
 * Hint: You can do this by induction or by using trc_transitive. Our solution
 * did it the first way, so if you do it the second way, yours may have a
 * different number of tactics.
 *)
Lemma trc_back :
  forall {A} (R : A -> A -> Prop) x y,
    trc R x y ->
    forall z,
      R y z ->
      trc R x z.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * Here is a definition of a transition system that is similar to the "counter"
 * transition system from lecture, but it starts at 0 and increments by two
 * each time.
 *)

Definition counter2_state : Type := nat.

Definition counter2_init (s : counter2_state) : Prop :=
  s = 0.

Definition counter2_step (s1 s2 : counter2_state) : Prop :=
  s2 = S (S s1).

Definition counter2_sys : trsys counter2_state := {|
  Init := counter2_init;
  Step := counter2_step
|}.

(* Let's prove the system never reaches state 3. *)

Definition counter2_safe (s : counter2_state) : Prop :=
  s <> 3.

(*
 * PROBLEM 7 [5 points, ~1 sentences]
 *
 * Give a counterexample to induction (CTI) that demonstrates that counter2_safe
 * is not inductive.
 *
 * Hint: Recall that a CTI is two states s1 and s2 such that s1 steps to s2 in
 * one step, s1 satisfies the property, but s2 violates the property.
 * Since a state of this system is just a single number, you are looking for two
 * numbers.
 *)
(* YOUR ANSWER HERE *)

(*
 * PROBLEM 8 [8 points, ~25 tactics]
 *
 * Prove that counter2_safe is an invariant of the counter2_sys transition
 * system.
 *
 * Hint: By the previous problem, a direct proof by induction is doomed to fail.
 *
 * Hint: Strengthen the invariant. Prove *that* by induction. And then conclude
 * that counter2_safe is also an invariant.
 *
 * Hint: You may find that you need the definition of `even`.
 * Feel free to copy/paste it.
 *)
Theorem counter2_safe_invariant :
  is_invariant counter2_sys counter2_safe.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * PROBLEM 9 [5 points, ~6 tactics]
 *
 * Prove that counter2_sys steps never decrease the state.
 *
 * Hint: Proceed by induction. (On what?)
 *)
Theorem counter2_ge :
  forall s0 sN,
    trc counter2_sys.(Step) s0 sN ->
    sN >= s0.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * Here is another transition system. Part of this homework is to understand
 * what it does.
 *)

Definition rotater_state : Type := nat * nat * nat.

Definition rotater_init (s : rotater_state) : Prop :=
  s = (0, 1, 2).

Inductive rotater_step : rotater_state -> rotater_state -> Prop :=
| rotater_step_step :
  forall a b c,
    rotater_step (a, b, c) (b, c, a).

Definition rotater_sys : trsys rotater_state := {|
  Init := rotater_init;
  Step := rotater_step
|}.

(* Here is a property of rotater_sys states. *)
Definition rotater_a_ne_b (s : rotater_state) : Prop :=
  let '(a, b, c) := s in
  a <> b.

(*
 * PROBLEM 10 [8 points, ~20 tactics]
 *
 * Prove that rotater_a_ne_b is an invariant of rotater_sys.
 *
 * Hint: Is the property inductive? If not, strengthen it.
 *)
Theorem rotater_a_ne_b_invariant :
  is_invariant rotater_sys rotater_a_ne_b.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(* Here is another property of rotater_sys states. *)
Definition rotater_a_in_range (s : rotater_state) : Prop :=
  let '(a, b, c) := s in
  0 <= a <= 2.

(*
 * PROBLEM 11 [8 points, ~20 tactics]
 *
 * Prove that rotater_a_in_range is an invariant of rotater_sys.
 *
 * Hint: Is the property inductive? If not, strengthen it.
 *)
Theorem rotater_a_in_range_invariant :
  is_invariant rotater_sys rotater_a_in_range.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * PROBLEM 12 [5 points, ~2 sentences]
 *
 * (a) How many reachable states of the rotater system are there?
 *     (Just give the number. No need to prove your answer.)
 *
 * (b) In your solutions to either of the previous two problems, did your
 *     strengthened invariant(s) exactly characterize the set of reachable
 *     states, or did you overapproximate it?
 *     (There is more than one answer to this subproblem, since it depends on
 *     how you did the previous problems. Again, no need to prove your answer.)
 *)
(*
 * (a) YOUR ANSWER HERE
 * (b) YOUR ANSWER HERE
 *)

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(*
  Consider the following Imp program:

      "output" <- 0;
      while "input" loop
        "output" <- "output" + "input";
        "input" <- "input" - 1
      done.

  Intuitively, it sums the integers from 1 to "input" and returns that value in
  "output"
*)

(*
 * We're going to model the program above as "course-grained" transition system,
 * where each step in the transition system corresponds to one iteration of
 * the program's main loop. Define your transition system called "sum_sys"
 * as parameterized on a natural number. Don't worry, we've provided some
 * structure to help you get started, and remember, the recipe is always
 * the same:
 *
 * (A) Given a program, define a transition system for it by answering
 *   the 3 questions:
 *     (1) What are the states?
 *     (2) What are the initial states?
 *     (3) What is the transition relation?
 *
 * (B) Figure out what you want to prove about all the reachable states
 *    of the system.
 *
 * (C) The property from (B) is usually not inductive, so figure out a
 *    *stronger* property that IS inductive an prove that using
 *    "invariant_induction".
 *
 * (D) Come back and finish the proof for (B) using "invariant_implies".
 *)

(* PROBLEM 13 [1 points, ~2 LOC]
 * Fill  in the definition for sum_state.
 *)
Definition sum_state : Type :=
  bool. (* Change bool to your definition. *)

(* PROBLEM 14 [1 points, ~2 LOC]
 * Fill  in the definition for sum_init.
 *)
Definition sum_init (input : nat) (s : sum_state) : Prop :=
  False. (* Change False to your definition. *)

(* PROBLEM 15 [4 points, ~4 LOC]
 * Fill in the type definition for sum_step.
 *)
Inductive sum_step : sum_state -> sum_state -> Prop :=
  . (* Your definition here. *)

(* Here's the definition for our transition system. *)
Definition sum_sys (input : nat) : trsys sum_state := {|
  Init := sum_init input;
  Step := sum_step
|}.

(* PROBLEM 16 [4 points, ~4 LOC]
 * Write a definition for what it means for sum to be safe.
 *
 * Hint: You may find your `sum_upto` function from a previous problem useful.
 * Since it was defined in a different module, you can refer to it as
 * Interpreters.sum_upto, or you can copy paste it closer to here.
 *)
Definition sum_safe (input : nat) (s : sum_state) : Prop :=
  False. (* Change False to your definition. *)

(* PROBLEM 17 [6 points, ~3 LOC]
 * sum_safe is not an inductive invariant. Come up with and define
 * a property that *is* inductive and will help us prove sum_safe.
 *)
Definition sum_inv (input : nat) (s : sum_state) : Prop :=
  False. (* Change False to your definition. *)

(* PROBLEM 18 [6 points, ~5 tactics]
 * Prove that your inductive invariant holds.
 *)
Lemma sum_inv_invariant :
  forall input,
    is_invariant (sum_sys input) (sum_inv input).
Proof.
Admitted. (* Change to Qed. when done *)

(* PROBLEM 19 [6 points, ~10 LOC]
 * Finally, we can prove that sum_safe holds!
 *
 * Hint: You'll want to use sum_inv_invariant in your proof.
 *)
Theorem sum_safe_invariant :
  forall input,
    is_invariant (sum_sys input) (sum_safe input).
Proof.
Admitted. (* Change to Qed. when done *)

(*
            ____                  _     _                     _  _
           / ___|    ___    ___  | |_  (_)   ___    _ __     | || |
           \___ \   / _ \  / __| | __| | |  / _ \  | '_ \    | || |_
            ___) | |  __/ | (__  | |_  | | | (_) | | | | |   |__   _|
           |____/   \___|  \___|  \__| |_|  \___/  |_| |_|      |_|

                            SECTION 4 : Intro to Imp
*)

(*
 * Copied from Week 4 lecture code.  We won't explain this code until Tuesday
 * of Week 4.
 *)

Definition eq_dec (A : Type) :=
  forall (x : A),
    forall (y : A),
      {x = y} + {x <> y}.

Notation var := string.
Definition var_eq : eq_dec var := string_dec.
Definition valuation := list (var * nat).

Fixpoint lookup (x : var) (v : valuation) : option nat :=
  match v with
  | [] => None
  | (y, n) :: v' =>
    if var_eq x y
    then Some n
    else lookup x v'
  end.

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

Fixpoint eval_arith (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match lookup x v with
    | None => 0
    | Some n => n
    end
  | Plus  e1 e2 => eval_arith e1 v + eval_arith e2 v
  | Minus e1 e2 => eval_arith e1 v - eval_arith e2 v
  | Times e1 e2 => eval_arith e1 v * eval_arith e2 v
  end.

Declare Scope arith_scope.
Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Infix "+" := Plus : arith_scope.
Infix "-" := Minus : arith_scope.
Infix "*" := Times : arith_scope.
Delimit Scope arith_scope with arith.
Bind Scope arith_scope with arith.

Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| If (e : arith) (then_ else_ : cmd)
| While (e : arith) (body : cmd).

Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";;" := Sequence (at level 76).
Notation "'when' e 'then' then_ 'else' else_ 'done'" :=
  (If e%arith then_ else_) (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" :=
  (While e%arith body) (at level 75).

Inductive step : valuation * cmd -> valuation * cmd -> Prop :=
| StepAssign :
    forall v x e v',
      v' = (x, eval_arith e v) :: v ->
      step (v, Assign x e) (v', Skip)
| StepSeqLStep :
    forall v c1 c2 v' c1',
      step (v, c1) (v', c1') ->
      step (v, Sequence c1 c2) (v', Sequence c1' c2)
| StepSeqLDone :
    forall v c2,
      step (v, Sequence Skip c2) (v, c2)
| StepIfTrue :
    forall v e then_ else_,
      eval_arith e v <> 0 ->
      step (v, If e then_ else_) (v, then_)
| StepIfFalse :
    forall v e then_ else_,
      eval_arith e v = 0 ->
      step (v, If e then_ else_) (v, else_)
| StepWhileTrue :
    forall v e body,
      eval_arith e v <> 0 ->
      step (v, While e body) (v, Sequence body (While e body))
| StepWhileFalse :
    forall v e body,
      eval_arith e v = 0 ->
      step (v, While e body) (v, Skip).

(* End of copied stuff. *)

(* Here is that same program, now in actual syntax. *)
Definition sum : cmd :=
  "output" <- 0;;
  while "input" loop
    "output" <- "output" + "input";;
    "input" <- "input" - 1
  done.

(*
 * PROBLEM 20 [10 points, ~70 tactics]
 *
 * Prove this kind of weird theorem about a particular concrete execution of
 * the sum program on the input 3.
 *
 * Hint: Our solution uses a lot of tactics, but it's pretty repetitive. This is
 * another example of proving specific ("easy") things being more difficult (or
 * at least, more tedious) than proving general ("hard") things.
 *
 * Hint: If you use the tactics provided in Week04.v, you can get a much shorter
 * proof.
 *)
Theorem sum_3 :
  forall v1,
    lookup "input" v1 = Some 3 ->
    exists v2,
      trc step (v1, sum) (v2, Skip) /\
      lookup "output" v2 = Some 6.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * PROBLEM 21 [5 points, ~3 sentences]
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


(* --- End of Core Points --- *)

(*
 * This is the end of the core points available for Homework 3. See below for
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
            / ___|    ___    ___  | |_  (_)   ___    _ __     | ___|
            \___ \   / _ \  / __| | __| | |  / _ \  | '_ \    |___ \
             ___) | |  __/ | (__  | |_  | | | (_) | | | | |    ___) |
            |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |____/

                         SECTION 5 : Challenge Problems
*)

(*
 * PROBLEM 22 [10 points, ~20 tactics]
 *
 * (a) Define a property on rotater_states that characterizes the reachable
 *     states. Don't use any other definitions. Essentially you should just list
 *     the reachable states directly here.
 *
 * (b) Prove that your property from part (a) is an invariant of rotater_sys.
 *
 * (c) Prove that every state that satisfies your property from part (a) is
 *     actually reachable in rotater_sys.
 *)
(* YOUR CODE HERE *)
(* Don't forget to do all three subproblems, unless you intentionally plan to
 * skip one because you don't need the points.
 *)

(*
 * PROBLEM 23 [2 points, ~6 tactics]
 *
 * Prove that counter2_sys is deterministic. In other words, every state has at
 * most one successor.
 *)
Lemma counter2_deterministic :
  forall s1 s2 s3,
    counter2_step s1 s2 ->
    counter2_step s1 s3 ->
    s2 = s3.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


(* Here is yet another transition system. *)
Definition parallel_counter_state : Type := nat * nat * nat.

Definition parallel_counter_init
  (input : nat)
  (s : parallel_counter_state)
: Prop :=
  s = (input, 0, 0).

Inductive parallel_counter_step :
  parallel_counter_state ->
  parallel_counter_state ->
  Prop
:=
| parallel_counter_step_step_ab :
  forall a b c,
    parallel_counter_step
      (S a, b, c)
      (a, S b, c)
| parallel_counter_step_step_bc :
  forall a b c,
    parallel_counter_step
      (a, S b, c)
      (a, b, S c).

Definition parallel_counter_sys (input : nat) : trsys parallel_counter_state :=
{|
  Init := parallel_counter_init input;
  Step := parallel_counter_step
|}.

(*
 * PROBLEM 24 [2 points, ~9 tactics]
 *
 * This system is not deterministic. Prove it!
 *)
Example parallel_counter_not_deterministic :
  exists s1 s2 s3,
    parallel_counter_step s1 s2 /\
    parallel_counter_step s1 s3 /\
    s2 <> s3.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(* Here is the safety property. *)
Definition parallel_counter_safe
  (input : nat)
  (s : parallel_counter_state)
: Prop :=
  let '(a, b, c) := s in
  a = 0 ->
  b = 0 ->
  c = input.

(*
 * PROBLEM 25 [5 points, ~15 tactics]
 *
 * Prove that the safety property is an invariant.
 *)
Theorem parallel_counter_safe_invariant :
  forall input,
    is_invariant (parallel_counter_sys input) (parallel_counter_safe input).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * PROBLEM 26 [5 points, 1 picture]
 *
 * Find a nice way to visualize the state space of the parallel counter for a
 * fixed value of "input". (Say, input = 5 or something to keep things simple.)
 * Draw a picture shows the reachable states, the "bad" states (that violate
 * parallel_counter_safe), and the states that satisfy your strengthened
 * from the previous problem.
 *)
(* YOUR PICTURE HERE *)
(* You can draw it in ascii art, or upload it to Gradescope as a separate file
 * and mention the filename here, or upload it somewhere else on the internet
 * and put a link here.
 *)
