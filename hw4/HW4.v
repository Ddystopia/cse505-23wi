(*

       _   _    ___    __  __   _____  __        __   ___    ____    _  __
      | | | |  / _ \  |  \/  | | ____| \ \      / /  / _ \  |  _ \  | |/ /
      | |_| | | | | | | |\/| | |  _|    \ \ /\ / /  | | | | | |_) | | ' /
      |  _  | | |_| | | |  | | | |___    \ V  V /   | |_| | |  _ <  | . \
      |_| |_|  \___/  |_|  |_| |_____|    \_/\_/     \___/  |_| \_\ |_|\_\

                                     _  _
                                    | || |
                                    | || |_
                                    |__   _|
                                       |_|


Welcome back! This homework covers inductive propositions, Imp as transition
systems, Hoare logic, and a little bit of lambda calculus. We don't expect you
to be able to do the lambda calculus problems until after Tuesday of Week 7.
But everything else (including all of the other challenge points) should be
doable after Thursday of Week 6.

There are 25 problems worth a total of 150 points.

*)


Require Import Arith Lia List String.
Require Import ListSet.
Import ListNotations.
Open Scope string.

Set Implicit Arguments.

(*
 * PROBLEM 1 [0 points, ~0 tactics]
 *
 * Fake problem to make Gradescope numbers match problem numbers.
 *)
(* Nothing to do here. *)

(* Bunch of copied stuff from week 3 *)
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
(* end of week 3 stuff *)

(* copied from week 4 *)
Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| trc_refl :
    forall x,
      trc R x x
| trc_front :
    forall x y z,
      R x y ->
      trc R y z ->
      trc R x z.
Local Hint Constructors trc : core.

Lemma trc_transitive :
  forall {A} (R : A -> A -> Prop) x y,
    trc R x y ->
    forall z,
      trc R y z ->
      trc R x z.
Proof.
  intros A R x y Hxy.
  induction Hxy; eauto.
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

Lemma invariant_implies :
  forall {state} (sys : trsys state) (P Q : state -> Prop),
    is_invariant sys P ->
    (forall s, P s -> Q s) ->
    is_invariant sys Q.
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
      intros s1 IH s2 Hstep
    end
  ].
(* end of week 4 stuff *)

(* tweaked from week 5 and 6 *)
Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| If (e : arith) (then_ else_ : cmd)
| While (e : arith) (body : cmd)
(* Here we add a new statement to Imp, namely assertion. *)
| Assert (p: arith)
| Panic.

Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";;" := Sequence (at level 76).
Notation "'when' e 'then' then_ 'else' else_ 'done'" :=
  (If e%arith then_ else_) (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" :=
  (While e%arith body) (at level 75).
Notation "'assert' e" :=
  (Assert e%arith) (at level 75).

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
    step (v, While e body) (v, Skip)
| StepAssertionTrue :
  forall v e,
    eval_arith e v <> 0 ->
    step (v, Assert e) (v, Skip)
| StepAssertionFalse :
  forall v e,
    eval_arith e v = 0 ->
    step (v, Assert e) (v, Panic)
| StepSeqPanic :
  forall v c2,
    step (v, Sequence Panic c2) (v, Panic).
Local Hint Constructors step : core.

Definition cmd_init (v : valuation) (c : cmd) (s : valuation * cmd) : Prop :=
  s = (v, c).

Definition cmd_to_trsys (v : valuation) (c : cmd) : trsys (valuation * cmd) :=
  {| Init := cmd_init v c
   ; Step := step
   |}.

Ltac invc H := inversion H; subst; clear H.
Ltac invert_one_step :=
  match goal with
  | [ H : step _ _ |- _ ] => invc H
  end.
Ltac invert_steps :=
  repeat invert_one_step.
Ltac invert_one_trc :=
  match goal with
  | [ H : trc step _ _ |- _ ] => invc H
  end.
Ltac bash_execution :=
  intros;
  repeat (invert_one_trc; invert_steps);
  auto.
Ltac break_up_hyps :=
  repeat match goal with
  | [ H : exists _, _ |- _ ] => destruct H
  | [ H : _ /\ _ |- _ ] => destruct H
  end.
Ltac break_up_hyps_or :=
  repeat match goal with
  | [ H : exists _, _ |- _ ] => destruct H
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ H : _ \/ _ |- _ ] => destruct H
  end.
Ltac prepare_induct_step H :=
  match type of H with
  | step (?v, ?c) (?v', ?c') =>
    let s := fresh "s" in
    let Heqs := fresh "Heqs" in
    let s' := fresh "s'" in
    let Heqs' := fresh "Heqs'" in
    remember (v, c) as s eqn:Heqs;
    remember (v', c') as s' eqn:Heqs';
    revert Heqs Heqs';
    try revert c';
    try revert v';
    try revert c;
    try revert v
  end.

Ltac induct_step H :=
  prepare_induct_step H;
  induction H; intros; subst.

Ltac prepare_induct_trc_step H :=
  match type of H with
  | trc step (?v, ?c) (?v', ?c') =>
    let s := fresh "s" in
    let Heqs := fresh "Heqs" in
    let s' := fresh "s'" in
    let Heqs' := fresh "Heqs'" in
    remember (v, c) as s eqn:Heqs;
    remember (v', c') as s' eqn:Heqs';
    revert Heqs Heqs';
    try revert c';
    try revert v';
    try revert c;
    try revert v
  end.

Ltac induct_trc_step H :=
  prepare_induct_trc_step H;
  induction H; intros; subst.

Ltac magic_select_case :=
  repeat match goal with
  | [ |- _ \/ _ ] => (left; split; [reflexivity|]) || right
  | _ => try split; [reflexivity|]
  end.


Ltac find_rewrites :=
  repeat match goal with
  | [ H : _ = _ |- _ ] => rewrite H in *
  end.

Lemma trc_seq_l_trc :
  forall v1 c1 v2 c2 c3,
    trc step (v1, c1) (v2, c2) ->
    trc step (v1, c1;;c3) (v2, c2;;c3).
Proof.
  intros v1 c1 v2 c2 c3 Hstep.
  revert c3.
  induct_trc_step Hstep.
  - invc Heqs'. auto.
  - destruct y as [v1' c1'].
    eauto.
Qed.

Notation "e '-->' e'" := (step e e') (at level 75).
Notation "e '-->*' e'" := (trc step e e') (at level 75).

Lemma deconstruct_panicked_execution :
  forall v v' c,
    (v, Panic) -->* (v', c) ->
    v' = v /\
    c = Panic.
Proof.
  bash_execution.
Qed.

Lemma deconstruct_sequence_execution :
  forall v v' c1 c2 c',
    (v, c1;; c2) -->* (v', c') ->
    exists v1' c1',
      trc step (v, c1) (v1', c1') /\
      (c' = (c1';; c2) \/
        (c1' = Skip /\ trc step (v1', c2) (v', c')) \/
        (c' = Panic /\ c1' = Panic /\ v1' = v')).
Proof.
  intros v v' c1 c2 c' Hstep.
  prepare_induct_trc_step Hstep.
  revert c1 c2.
  induction Hstep; intros; subst.
  - invc Heqs'. eauto.
  - invc H; eauto 10.
    + specialize (IHHstep _ _ _ _ _ eq_refl eq_refl).
      break_up_hyps.
      eauto.
    + apply deconstruct_panicked_execution in Hstep.
      break_up_hyps; subst; eauto 10.
Qed.
(* end of week 5 and 6 stuff *)


(*
               ____                  _     _                     _
              / ___|    ___    ___  | |_  (_)   ___    _ __     / |
              \___ \   / _ \  / __| | __| | |  / _ \  | '_ \    | |
               ___) | |  __/ | (__  | |_  | | | (_) | | | | |   | |
              |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |_|

                     SECTION 1 : More Inductive Propositions
*)

(*
 * PROBLEM 2 [5 points, ~15 tactics]
 *
 * Prove that you can "append" executions of Imp programs using ";;".
 *
 * Hint: There is more than one way to do this. You can proceed by induction, or
 * you can use the lemma trc_seq_l_trc above plus one more lemma above. Our
 * suggested number of tactics is based on an inductive proof, but a proof using
 * existing lemmas can be (much) shorter.
 *
 * Hint: If you proceed by induction, think carefully about what to induct on.
 * And if you decide to induct on a derivation of trc, you will need the
 * "remember trick" to get a useful induction hypothesis.
 *)
Lemma reconstruct_sequence_execution :
  forall v1 c1 v2 c2 v3,
    trc step (v1, c1) (v2, Skip) ->
    trc step (v2, c2) (v3, Skip) ->
    trc step (v1, c1;;c2) (v3, Skip).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * PROBLEM 3 [5 points, ~15 tactics]
 *
 * Prove that the ";;" operator is associative, in the sense that the two
 * different ways to parenthesize have equivalent computational behavior.
 *
 * Hint: Again, you can either proceed by induction or using existing lemmas.
 * Both approaches use a similar number of tactics.
 *
 * Hint: Check out the lemma deconstruct_sequence_execution above in the starter
 * code.
 *
 * Hint: If you proceed by induction, think carefully about what to induct on.
 * If you decide to induct on a derivation of trc, use the "remember trick".
 *
 *)
Lemma sequence_assoc :
  forall v c1 c2 c3 v',
    trc step (v, (c1;;c2);;c3) (v', Skip) ->
    trc step (v, c1;;(c2;;c3)) (v', Skip).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * PROBLEM 4 [5 points, 1 comment or picture]
 *
 * Define an inductive proposition on cmds that encodes the idea:
 *
 *     this command contains no while loops
 *
 * Make your definition by "long horizontal lines". You may draw them in ascii
 * art or on paper in a separate file. You can turn in your drawing as a link
 * or by uploading the image file directly to Gradescope with your homework.
 *
 * Hint: Your definition should have one rule for each syntactic form of an Imp
 * program *except* for while. Although the cmd type used in this homework is
 * the one from Week05.v, which has been extended with Assert and Panic. For
 * this problem, you should *ignore* those syntactic forms, meaning your long
 * horizontal lines should not have cases for them.
 *
 * Hint: Here is what the rule for "if" should look like (in ascii art).
 *
 *    has_no_whiles c1        has_no_whiles c2
 *  -------------------------------------------- HNWIf
 *         has_no_whiles (If e c1 c2)
 *)
  (* YOUR DEFINITION HERE *)
  (* If you choose to submit your definition by uploading a picture, please say
     so here so we know where to look for it. *)

(*
 * PROBLEM 5 [5 points, ~0 tactics]
 *
 * Encode your inductive definition in Coq by filling in constructors to the
 * type has_no_whiles below.
 *
 * Hint: This should be a very mechanical translation from your long horizontal
 * lines. If you find a bug in your definition later, be sure to update it both
 * here and "on paper".
 *)
Inductive has_no_whiles : cmd -> Prop :=
  (* YOUR CODE HERE *)
.

(*
 * PROBLEM 6 [5 points, ~6 tactics]
 *
 * Prove this silly example program has no whiles. This is just a quick
 * back-of-the-envelope check that you have a reasonable definition. If you
 * realize you are missing something, go back and edit your definitions above.
 *
 * Hint: You might find "repeat" useful to get an even shorter proof.
 *)
Example a_program_without_whiles :
  has_no_whiles (Skip ;; If "x" ("y" <- 3) ("z" <- 4)).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * PROBLEM 7 [5 points, ~6 tactics]
 *
 * There is a subtle problem that can come up when using eexists or other
 * e-whatever tactics. If you use eexists "too early", you will get weird error
 * messages.
 *
 * The way eexists works under the hood is it puts in a placeholder, whose
 * actual value gets figured out later in the course of the proof. But the
 * "real" proof at the end of the day eventually has to actually have something
 * to put in place of the placeholder.
 *
 * This means that whatever value we want to plug in for the place holder has to
 * make sense ***in the scope where the placeholder was introduced***.
 *
 * In practice, this means that if you are going to "take anything apart" with
 * destruct or inversion, etc., you should do that *before* using eexists.
 *
 * Consider the following example, derived from Week05.v's proof of
 * factorial_inv_invariant. The starter code contains a broken proof. When the
 * proof tries to use reflexivity, Coq reports a strange error that basically
 * says "something is not in scope where the placeholder was introduced".
 *
 * Try removing the "Fail" command below and run reflexivity to see the error.
 *
 * Ponder for a bit.
 *
 * Then fix the proof by moving the eexists right before reflexivity.
 *
 * Notice that reflexivity now works and the proof is finished.
 *
 * Ponder some more.
 *
 * Be on the lookout for this mistake in your own proofs! It can be hard to
 * debug if you haven't seen it before.
 *
 * Hint: Even though the problem says the solution is several tactics, really
 * all you have to do is reorder a few lines and do some thinking.
 *)
Lemma n_not_zero_is_succ :
  forall n,
    n <> 0 ->
    exists m,
      n = S m.
Proof.
  intros.
  eexists.
  destruct n.
  - congruence.
  - Fail reflexivity.
  Restart.
  (* YOUR CODE HERE, or you can delete "Restart" and edit the above proof. *)
Admitted. (* Change to Qed when done *)

(*
 * PROBLEM 8 [10 points, ~20 tactics]
 *
 * Prove that a program without while loops terminates.
 *
 * Hint: Proceed by induction.
 *
 * Hint: Think carefully about what to induct on. There is more than one
 * reasonable choice, and all reasonable choices can be made to work.
 *
 * Hint: When you induct, make sure you get a general enough induction
 * hypothesis. The person who stated this homework problem might have
 * intentionally ordered the "forall" variables in a way that makes your life
 * difficult. You can use the "revert" tactic before inducting to get a more
 * general induction hypothesis.
 *
 * Hint: During your inductive proof, you might find a lemma from an earlier
 * problem useful. Be on the lookout for this so you don't repeat a bunch of
 * work. You shouldn't need any new lemmas.
 *)
Theorem has_no_whiles_terminates :
  forall v c,
    has_no_whiles c ->
    exists v',
      trc step (v, c) (v', Skip).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
             ____                  _     _                     ____
            / ___|    ___    ___  | |_  (_)   ___    _ __     |___ \
            \___ \   / _ \  / __| | __| | |  / _ \  | '_ \      __) |
             ___) | |  __/ | (__  | |_  | | | (_) | | | | |    / __/
            |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |_____|

                      SECTION 2 : Imp as transition systems
*)

(* Here is one of our old friends: counting up and down. *)
Definition two_counters :=
  "x" <- 0;;
  "y" <- "input";;
  while "y" loop
    "x" <- "x" + 1;;
    "y" <- "y" - 1
  done.

(* Convert the above program to a transition system automatically using the
   operational semantics. *)
Definition two_counters_sys (input : nat) :=
  cmd_to_trsys [("input", input)] two_counters.

(* Here is our "safety property":
 *     when the program terminates, x is equal to input
 *)
Definition two_counters_safe (input : nat) (s : valuation * cmd) : Prop :=
  let (v, c) := s in
  c = Skip ->
  lookup "x" v = Some input.

(* For your convenience, here are all the reachable commands of two_counters. *)
Definition tc_after_step_one :=
  Skip;;
  "y" <- "input";;
  while "y" loop
    "x" <- "x" + 1;;
    "y" <- "y" - 1
  done.
Definition tc_after_step_two :=
  "y" <- "input";;
  while "y" loop
    "x" <- "x" + 1;;
    "y" <- "y" - 1
  done.
Definition tc_after_step_three :=
  Skip;;
  while "y" loop
    "x" <- "x" + 1;;
    "y" <- "y" - 1
  done.
Definition tc_top_of_loop :=
  while "y" loop
    "x" <- "x" + 1;;
    "y" <- "y" - 1
  done.
Definition tc_body :=
  "x" <- "x" + 1;;
  "y" <- "y" - 1;;
  while "y" loop
    "x" <- "x" + 1;;
    "y" <- "y" - 1
  done.
Definition tc_body_after_step_one :=
  Skip;;
  "y" <- "y" - 1;;
  while "y" loop
    "x" <- "x" + 1;;
    "y" <- "y" - 1
  done.
Definition tc_body_after_step_two :=
  "y" <- "y" - 1;;
  while "y" loop
    "x" <- "x" + 1;;
    "y" <- "y" - 1
  done.
Definition tc_after_loop :=
  Skip.
Definition tc_reachable_cmds_inv (s : valuation * cmd) :=
  let (v, c) := s in
  c = two_counters \/
  c = tc_after_step_one \/
  c = tc_after_step_two \/
  c = tc_after_step_three \/
  c = tc_top_of_loop \/
  c = tc_body \/
  c = tc_body_after_step_one \/
  c = tc_body_after_step_two \/
  c = tc_after_loop.

(* Just as a demo, here is a proof that these are actually all the reachable
   commands. *)
Lemma tc_reachable_cmds_inv_invariant :
  forall input,
    is_invariant (two_counters_sys input) tc_reachable_cmds_inv.
Proof.
  invariant_induction_boilerplate.
  - auto.
  - (* Tactics get really slow when the goal is large. So temporarily fold up
       the goal to improve performance. *)
    fold (tc_reachable_cmds_inv s2).
    destruct s1 as [v1 c1], s2 as [v2 c2].
    intuition; subst; invert_steps;
    (* now it's ok to unfold the goal again. *)
    unfold tc_reachable_cmds_inv;
    (* auto will find the correct disjunction and use "reflexivity" for us *)
    auto 10.
    (* (auto doesn't work in full "enumeration-style" invariants because it
       often cannot complete the whole proof. Use magic_select_case instead.)
     *)
Qed.

(*
 * PROBLEM 9 [30 points, ~50 tactics]
 *
 * Prove that two_counters_safe is an invariant of the transition system defined
 * by the operational semantics of the two_counters program.
 *
 * Do not use Hoare logic. The point of this problem is to gain a greater
 * appreciation of the power of Hoare logic, since it shields us from reasoning
 * directly on the semantics, as we do in this problem.
 *
 * Instead, strengthen the property using an "enumeration-style" invariant.
 *
 * Hint: As usual with enumeration-style invariants, most of the work is just
 * setting everything up. For your convenience, we have provided the list of
 * all reachable commands above. You will need to make a new invariant
 * constructed by listing all reachable commands, and for each one, make an
 * assertion about valuations when that program is reached.
 *
 * Hint: Repeating for emphasis: see the definitions above for all the reachable
 * commands so you don't have to write them out yourself.
 *
 * Hint: There are many ways to do the details, but we recommend following the
 * same structure as the examples from Week05.v. Your invariant should be a
 * disjunction of conjunctions whose left conjuncts are equations about the
 * syntax of the reachable programs. That way you can use the fancy tactics from
 * Week05.v, such as magic_select_case, to make your life easier. These tactics
 * have been pasted into the starter code above for your convenience. You may
 * wish to review Week05.v for more information about how they work and how to
 * use them.
 *
 * Hint: Repeating for emphasis: we recommend using magic_select_case. To use
 * it, you must structure your invariant exactly like we did in Week05.v.
 *
 * Hint: Once you get the definitions set up correctly, the proof itself is
 * relatively easy. Again, the hard/tedious part is setting up the definitions
 * correctly.
 *)
Theorem two_counters_correct :
  forall input,
    is_invariant (two_counters_sys input) (two_counters_safe input).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


(* This is the end of this section. More starter code appears below. Search for
   "S E C T I O N" (without spaces) to skip to the next section below. *)

(* BUNCH of copied stuff from week 6 *)
Definition assertion := (valuation -> Prop).
Definition assert_implies (P Q : assertion) : Prop :=
  (forall v, P v -> Q v).
Local Hint Unfold assert_implies : core.

Inductive hoare_triple : assertion -> cmd -> assertion -> Prop :=
| ht_skip :
  forall P,
    hoare_triple P Skip P
| ht_sequence :
  forall P Q R c1 c2,
    hoare_triple P c1 R ->
    hoare_triple R c2 Q ->
    hoare_triple P (Sequence c1 c2) Q
| ht_assert_true :
  forall P e,
    hoare_triple (fun v => P v /\ eval_arith e v <> 0) (Assert e) P
| ht_consequence :
  forall P P' Q Q' c,
    hoare_triple P' c Q' ->
    assert_implies P P' ->
    assert_implies Q' Q ->
    hoare_triple P c Q
| ht_assign :
  forall P x e,
    hoare_triple (fun v => P ((x, eval_arith e v) :: v)) (Assign x e) P
| ht_if :
  forall P Q e c1 c2,
    hoare_triple (fun v => P v /\ eval_arith e v <> 0) c1 Q ->
    hoare_triple (fun v => P v /\ eval_arith e v = 0) c2 Q ->
    hoare_triple P (If e c1 c2) Q
| ht_while :
  forall I e c,
    hoare_triple (fun v => I v /\ eval_arith e v <> 0) c I ->
    hoare_triple I (While e c) (fun v => I v /\ eval_arith e v = 0).
Local Hint Constructors hoare_triple : core.

Definition sound_triple (P : assertion) c (Q : assertion) : Prop :=
  forall v v' c',
    P v ->
    (v, c) -->* (v', c') ->
    c' <> Panic /\ (c' = Skip -> Q v').

Lemma ht_consequence_left :
  forall P P' Q c,
    hoare_triple P' c Q ->
    assert_implies P P' ->
    hoare_triple P c Q.
Proof.
  eauto.
Qed.

Lemma ht_consequence_right :
  forall P Q Q' c,
    hoare_triple P c Q' ->
    assert_implies Q' Q ->
    hoare_triple P c Q.
Proof.
  eauto.
Qed.

Lemma deconstruct_skip_execution :
  forall v v' c,
    (v, Skip) -->* (v', c) ->
    v' = v /\ c = Skip.
Proof.
  bash_execution.
Qed.

Local Hint Extern 4 (~(_ = _)) => discriminate : core.
Local Hint Extern 4 (False) => discriminate : core.
Local Hint Extern 4 (False) => congruence : core.

Lemma hoare_skip_ok :
  forall P,
    sound_triple P Skip P.
Proof.
  intros P c' v v' HP Hstep.
  apply deconstruct_skip_execution in Hstep.
  intuition; subst; auto.
Qed.

Lemma deconstruct_assert_execution :
  forall v v' e c,
    (v, Assert e) -->* (v', c) ->
    v' = v /\
    (c = Assert e \/
     (c = Skip /\ eval_arith e v <> 0) \/
     (c = Panic /\ eval_arith e v = 0)).
Proof.
  bash_execution.
Qed.

Lemma hoare_assertion_ok :
  forall P e,
    sound_triple (fun v => P v /\ eval_arith e v <> 0) (Assert e) P.
Proof.
  intros P e v v' c' [HP Heval] Hstep.
  apply deconstruct_assert_execution in Hstep.
  intuition; subst; auto.
Qed.

Lemma deconstruct_assignment_execution :
  forall v v' x e c,
    (v, x <- e) -->* (v', c) ->
    (v' = v /\ c = (x <- e)) \/
    (v' = (x, eval_arith e v) :: v /\ c = Skip).
Proof.
  bash_execution.
Qed.

Lemma hoare_assignment_ok :
  forall P x e,
    sound_triple (fun v => P ((x, eval_arith e v) :: v)) (x <- e) P.
Proof.
  intros P x e v v' c' Hv Hstep.
  apply deconstruct_assignment_execution in Hstep.
  intuition; subst; auto.
  congruence.
Qed.

Lemma hoare_sequence_ok :
  forall P Q R c1 c2,
    sound_triple P c1 R ->
    sound_triple R c2 Q ->
    sound_triple P (c1;; c2) Q.
Proof.
  intros P Q R c1 c2 IHc1 IHc2 v v' c' HP Hstep.
  apply deconstruct_sequence_execution in Hstep.
  break_up_hyps_or; subst.
  - split; congruence.
  - eapply IHc2; eauto.
    eapply IHc1; eauto.
  - apply IHc1 in H; auto.
    intuition.
Qed.

Lemma hoare_consequence_ok :
  forall (P P' Q Q' : assertion) c,
    assert_implies P P' ->
    assert_implies Q' Q ->
    sound_triple P' c Q' ->
    sound_triple P c Q.
Proof.
  intros P P' Q Q' c HPP' HQQ' IH v v' c' HP Hstep.
  apply IH in Hstep; intuition.
Qed.

Lemma deconstruct_conditional_execution :
  forall v v' e c1 c2 c',
    (v, If e c1 c2) -->* (v', c') ->
    (v' = v /\ c' = If e c1 c2) \/
    (eval_arith e v <> 0 /\ (v, c1) -->* (v', c')) \/
    (eval_arith e v = 0 /\ (v, c2) -->* (v', c')).
Proof.
  intros v v' e c1 c2 c' Hstep.
  invert_one_trc; auto.
  invert_one_step; auto.
Qed.

Lemma hoare_conditional_ok :
  forall P Q e c1 c2,
    sound_triple (fun v => P v /\ eval_arith e v <> 0) c1 Q ->
    sound_triple (fun v => P v /\ eval_arith e v = 0) c2 Q ->
    sound_triple P (If e c1 c2) Q.
Proof.
  intros P Q e c1 c2 IHc1 IHc2 v v' c' HP Hstep.
  apply deconstruct_conditional_execution in Hstep.
  break_up_hyps_or; subst.
  - split; congruence.
  - eapply IHc1; eauto.
  - eapply IHc2; eauto.
Qed.

Inductive trc_backward {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| trcb_refl :
    forall x,
      trc_backward R x x
| trcb_back :
    forall x y z,
      trc_backward R x y ->
      R y z ->
      trc_backward R x z.

Lemma trc_back :
  forall {A} (R : A -> A -> Prop) x y,
    trc R x y ->
    forall z,
      R y z ->
      trc R x z.
Proof.
  (* On HW3 *)
Admitted.
Local Hint Resolve trc_back : core.

Lemma trcb_front :
  forall {A} (R : A -> A -> Prop) y z,
    trc_backward R y z ->
    forall x,
      R x y ->
      trc_backward R x z.
Proof.
  (* Very similar to previous lemma. *)
Admitted.

Lemma trc_implies_trc_backward :
  forall A (R : A -> A -> Prop) x y,
    trc R x y ->
    trc_backward R x y.
Proof.
  intros A R x y Htrc.
  induction Htrc.
  - constructor.
  - eapply trcb_front; eauto.
Qed.

Lemma trc_backward_implies_trc :
  forall A (R : A -> A -> Prop) x y,
    trc_backward R x y ->
    trc R x y.
Proof.
  intros A R x y Htrcb.
  induction Htrcb; eauto.
Qed.

Lemma trc_reverse_ind :
  forall A (R : A -> A -> Prop) (P : A -> A -> Prop),
    (forall x, P x x) ->
    (forall x y z, trc R x y -> R y z -> P x y -> P x z) ->
    forall x y,
      trc R x y ->
      P x y.
Proof.
  intros A R P Hbase Hind x y H.
  apply trc_implies_trc_backward in H.
  induction H.
  - apply Hbase.
  - apply Hind with (y := y); auto.
    apply trc_backward_implies_trc.
    auto.
Qed.

Definition loop_runs_to (e : arith) (c : cmd) (v1 v2 : valuation) :=
  trc step (v1, c) (v2, Skip) /\ eval_arith e v1 <> 0.
Local Hint Unfold loop_runs_to : core.

Notation "v '-[' e ',' s ']>*' v'" :=
  (trc (loop_runs_to e s) v v') (at level 75).

Lemma deconstruct_while_execution :
  forall v v' e c c',
  (v, while e loop c done) -->* (v', c') ->
  exists v1,
    v -[ e, c ]>* v1 /\
    ((c' = Skip /\ v' = v1 /\ eval_arith e v' = 0) \/
     (c' = While e c /\ v' = v1) \/
     (c' = Panic /\ eval_arith e v1 <> 0 /\ (v1, c) -->* (v', Panic)) \/
     (eval_arith e v1 <> 0 /\
      exists c1', (v1, c) -->* (v', c1') /\ c' = (c1' ;; while e loop c done))).
Proof.
  intros v v' e c c' Htrc.
  prepare_induct_trc_step Htrc.
  revert e c.
  induction Htrc using trc_reverse_ind; intros e c v v' c' ? ?; subst.
  - invc Heqs'. eauto 10.
  - destruct y as [v2 c2].
    specialize (IHHtrc _ _ _ _ _ eq_refl eq_refl).
    break_up_hyps_or; subst; try invert_one_step; eauto 10.
Qed.

Lemma runs_to_preserves_invariant :
  forall (I : assertion) e c,
    (forall v v', I v ->
      eval_arith e v <> 0 ->
      (v, c) -->* (v', Skip) ->
      I v') ->
    forall v v',
      I v ->
      v -[ e, c ]>* v' ->
      I v'.
Proof.
  intros I e c HI v v' IH Hstep.
  assert (forall v v', I v -> loop_runs_to e c v v' -> I v') as HI2.
  {
    unfold loop_runs_to. intuition eauto.
  }
  induction Hstep using trc_reverse_ind; eauto.
Qed.

Lemma sound_triple_preserves_invariant :
  forall (I : assertion) e c,
    sound_triple (fun v => I v /\ eval_arith e v <> 0) c I ->
    forall v v',
      I v ->
      v -[ e, c ]>* v' ->
      I v'.
Proof.
  intros I e c Hsound v v' HI Hstep.
  eapply runs_to_preserves_invariant; eauto.
  intros. eapply Hsound; eauto.
Qed.

Lemma hoare_while_loop_ok :
  forall (I : assertion) e c,
    sound_triple (fun v => I v /\ eval_arith e v <> 0) c I ->
    sound_triple I (While e c) (fun v => I v /\ eval_arith e v = 0).
Proof.
  intros I e c IH v v' c' HI Hstep.
  apply deconstruct_while_execution in Hstep.

  break_up_hyps_or; subst; split; intros; try congruence; try split; auto.
  - eapply sound_triple_preserves_invariant; eauto.
  - eapply IH; eauto.
    split; auto.
    eapply sound_triple_preserves_invariant; eauto.
Qed.

Theorem hoare_ok :
  forall P s Q,
    hoare_triple P s Q ->
    sound_triple P s Q.
Proof.
  intros P s Q HHT.
  induction HHT.
  - apply hoare_skip_ok.
  - eapply hoare_sequence_ok; eauto.
  - apply hoare_assertion_ok.
  - eapply hoare_consequence_ok; eauto.
  - apply hoare_assignment_ok.
  - apply hoare_conditional_ok; auto.
  - apply hoare_while_loop_ok; auto.
Qed.

Corollary hoare_triples_are_safe :
  forall P c Q v v' c',
    hoare_triple P c Q ->
    (v, c) -->* (v', c') ->
    P v ->
    c' <> Panic.
Proof.
  intros P c Q v v' c' HT HP Hstep.
  eapply hoare_ok in HT.
  eapply HT; eauto.
Qed.

Lemma cmds_not_stuck :
  forall v c,
    c = Skip \/
    c = Panic \/
    exists v' c',
      (v, c) --> (v', c').
Proof.
  induction c; auto; right; right.
  - eauto.
  - clear IHc2. break_up_hyps_or; subst; eauto.
  - destruct (eval_arith e v) eqn:?; eauto.
  - destruct (eval_arith e v) eqn:?; eauto.
  - destruct (eval_arith p v) eqn:?; eauto.
Qed.

Lemma hoare_triples_not_stuck :
  forall P c Q v v' c',
    hoare_triple P c Q ->
    (v, c) -->* (v', c') ->
    P v ->
    c' = Skip \/
    exists v'' c'',
      (v', c') --> (v'', c'').
Proof.
  intros P c Q v v' c' HT Hstep HP.
  pose proof (cmds_not_stuck v' c').
  eapply hoare_triples_are_safe in HP; eauto.
  intuition.
Qed.

Lemma ht_sequence_reverse :
  forall (P Q R : assertion) c1 c2,
    hoare_triple R c2 Q ->
    hoare_triple P c1 R ->
    hoare_triple P (c1 ;; c2) Q.
Proof.
  intros.
  eapply ht_sequence; eauto.
Qed.

Ltac auto_triple :=
  intros;
  repeat match goal with
  | [ |- hoare_triple _ (_ ;; _) _ ] => eapply ht_sequence_reverse
  | [ |- hoare_triple _ (_ <- _) _ ] =>
    apply ht_assign || (eapply ht_consequence_left; [apply ht_assign|])
  | [ |- hoare_triple _ (If _ _ _) _ ] =>  apply ht_if
  | [ |- hoare_triple _ Skip _ ] =>
    apply ht_skip || (eapply ht_consequence_left; [apply ht_skip|])
  | [ |- hoare_triple _ (Assert _) _ ] =>
    apply ht_assert_true ||
    (eapply ht_consequence_left; [apply ht_assert_true|])
  | [ |- hoare_triple _ ?x _ ] => unfold x
  end.

Ltac fancy_ht_while e :=
  (let a := (apply ht_while with (I := e)) in
   (a ||
   (eapply ht_consequence_right; [a|]) ||
   (eapply ht_consequence_left; [a|]) ||
   (eapply ht_consequence; [a| |])));
  auto_triple.

Ltac cleanup_vars :=
  repeat match goal with
  | [ H : context [ match lookup ?x ?v with _ => _ end ] |- _ ] =>
    let E := fresh "E" in
    remember (match lookup x v with Some _ => _ | None => _ end) eqn:E; clear E
  end.

Ltac bash_assert_implies :=
  unfold assert_implies; intros; simpl in *; break_up_hyps; subst;
  find_rewrites; simpl in *;
  cleanup_vars; subst; auto; try lia.
(* end of week 5 stuff *)

(*
             ____                  _     _                     _____
            / ___|    ___    ___  | |_  (_)   ___    _ __     |___ /
            \___ \   / _ \  / __| | __| | |  / _ \  | '_ \      |_ \
             ___) | |  __/ | (__  | |_  | | | (_) | | | | |    ___) |
            |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |____/

                          SECTION 3 : Using Hoare Logic
*)

(* An Imp program to compute the sum of integers from 0 to n. *)
Definition sum :=
  "output" <- 0;;
  while "input" loop
    "output" <- "output" + "input";;
    "input" <- "input" - 1
  done.

(* A Coq implementation of the same. *)
Fixpoint sum_upto (n : nat) :=
  match n with
  | 0 => 0
  | S m => n + sum_upto m
  end.

(*
 * PROBLEM 10 [10 points, ~9 tactics]
 *
 * Prove the following Hoare triple about sum_triple.
 *
 * Hint: Use the automation tactics auto_triple, fancy_ht_while, and
 * bash_assert_implies. Then clean up the resulting subgoals manually.
 *
 * Hint: The hard part is getting the loop invariant correct. It should be
 * similar to your solution to Problem 5 [CHECK] on HW3.
 *)
Theorem sum_triple :
  forall input,
    hoare_triple
     (fun v => eval_arith "input" v = input)
     sum
     (fun v => eval_arith "output" v = sum_upto input).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


(*
 * PROBLEM 11 [5 points, ~3 sentences]
 *
 * Consider the following program, a version of which we saw in the Week 4
 * slides. It does not terminate. Answer the following 2 questions,
 * which are meant to be food for thought for the next problem (problem 12):
 *
 * 1. Additionally, the Hoare triple
 *            {True} doesnt_terminate {x <> 4}
 *    is true, and is in fact a _sound_ Hoare triple.
 *    Explain why this Hoare triple is sound, in your own words.
 *    (Hint: it may help to look at the definition of sound_triple.)
 *
 * 2. What implications does this have for Hoare logic, more generally?
 *    I.e., what is the relationship between termination of the programs
 *    a Hoare triple is true? (1 sentence is fine)
 *)
Definition doesnt_terminate :=
  "x" <- 5;;
  while 1 loop
    assert (("x" - 4) + (4 - "x"));; (* x <> 4 *)
    "x" <- "x" + 1
  done.

(*
 * PROBLEM 12 [5 points, ~4 tactics]
 *
 * Now prove that the Hoare triple holds!
 *)
Theorem doesnt_terminate_ht :
  hoare_triple
    (fun _ => True)
    doesnt_terminate
    (fun v => eval_arith "x" v <> 4).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


(*
            ____                  _     _                     _  _
           / ___|    ___    ___  | |_  (_)   ___    _ __     | || |
           \___ \   / _ \  / __| | __| | |  / _ \  | '_ \    | || |_
            ___) | |  __/ | (__  | |_  | | | (_) | | | | |   |__   _|
           |____/   \___|  \___|  \__| |_|  \___/  |_| |_|      |_|

                      SECTION 4 : Metatheory of Hoare Logic
*)

(*
Let's add a new feature to our language. We will have to add syntax, operational
semantics, and a Hoare proof rule, and we will have to update many theorems and
lemmas to handle the new case. This is great practice for seeing how all the
pieces fit together!

The feature we will add is a nondeterministic branching operator, which we will
call "Amb" for "ambiguous".  It's kind of like an if statement, except there is
no branch condition. When the Amb statement is executed, it nondeterministically
chooses whether to execute the "then" or the "else" branch.
*)
Module NondeterministicImp.

Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| If (e : arith) (then_ else_ : cmd)
| While (e : arith) (body : cmd)
| Assert (p: arith)
| Panic

(* The syntax of Amb: like an If statement with no branch condition. *)
| Amb (c1 : cmd) (c2 : cmd).

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
    step (v, While e body) (v, Skip)
| StepAssertionTrue :
  forall v e,
    eval_arith e v <> 0 ->
    step (v, Assert e) (v, Skip)
| StepAssertionFalse :
  forall v e,
    eval_arith e v = 0 ->
    step (v, Assert e) (v, Panic)
| StepSeqPanic :
  forall v c2,
    step (v, Sequence Panic c2) (v, Panic)
(*
The operational semantics of Amb: there are two rules, both of which are
applicable to any Amb. It can step to the left statement or the right.
*)
| StepAmbLeft :
    forall v c1 c2,
      step (v, Amb c1 c2) (v, c1)
| StepAmbRight :
    forall v c1 c2,
      step (v, Amb c1 c2) (v, c2).

Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";;" := Sequence (at level 76). (* ;; instead of ; because it interferes
                                          with record syntax *)
Notation "'when' e 'then' then_ 'else' else_ 'done'" :=
  (If e%arith then_ else_) (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" :=
  (While e%arith body) (at level 75).
Notation "e '-->' e'" := (step e e') (at level 75).
Notation "e '-->*' e'" := (trc step e e') (at level 75).

(*
 * PROBLEM 13 [5 points, ~5 LOC]
 *
 * Define the Hoare rule for the Amb operator.
 *
 * Hint: Since the operational semantics allows Amb to go to either branch, the
 * proof rule should require the user to verify both branches.
 *)
Inductive hoare_triple : assertion -> cmd -> assertion -> Prop :=
| ht_skip :
  forall P,
    hoare_triple P Skip P
| ht_sequence :
  forall P Q R c1 c2,
    hoare_triple P c1 R ->
    hoare_triple R c2 Q ->
    hoare_triple P (Sequence c1 c2) Q
| ht_assert_true :
  forall P e,
    hoare_triple (fun v => P v /\ eval_arith e v <> 0) (Assert e) P
| ht_consequence :
  forall P P' Q Q' c,
    hoare_triple P' c Q' ->
    assert_implies P P' ->
    assert_implies Q' Q ->
    hoare_triple P c Q
| ht_assign :
  forall P x e,
    hoare_triple (fun v => P ((x, eval_arith e v) :: v)) (Assign x e) P
| ht_if :
  forall P Q e c1 c2,
    hoare_triple (fun v => P v /\ eval_arith e v <> 0) c1 Q ->
    hoare_triple (fun v => P v /\ eval_arith e v = 0) c2 Q ->
    hoare_triple P (If e c1 c2) Q
| ht_while :
  forall I e c,
    hoare_triple (fun v => I v /\ eval_arith e v <> 0) c I ->
    hoare_triple I (While e c) (fun v => I v /\ eval_arith e v = 0)

(* YOUR CODE HERE *)
.

(* Copy-pasted automation. *)
Lemma ht_sequence_reverse :
  forall (P Q R : assertion) c1 c2,
    hoare_triple R c2 Q ->
    hoare_triple P c1 R ->
    hoare_triple P (c1 ;; c2) Q.
Proof.
  intros.
  eapply ht_sequence; eauto.
Qed.
Lemma ht_consequence_left :
  forall P P' Q c,
    hoare_triple P' c Q ->
    assert_implies P P' ->
    hoare_triple P c Q.
Proof.
  intros.
  eapply ht_consequence; eauto.
Qed.

Lemma ht_consequence_right :
  forall P Q Q' c,
    hoare_triple P c Q' ->
    assert_implies Q' Q ->
    hoare_triple P c Q.
Proof.
  intros.
  eapply ht_consequence; eauto.
Qed.

Ltac invert_one_step :=
  match goal with
  | [ H : step _ _ |- _ ] => invc H
  end.
Ltac invert_steps :=
  repeat invert_one_step.
Ltac invert_one_trc :=
  match goal with
  | [ H : trc step _ _ |- _ ] => invc H
  end.
Ltac bash_execution :=
  intros;
  repeat (invert_one_trc; invert_steps);
  auto.
Ltac auto_triple :=
  intros;
  repeat match goal with
  | [ |- hoare_triple _ (_ ;; _) _ ] => eapply ht_sequence_reverse
  | [ |- hoare_triple _ (_ <- _) _ ] =>
    apply ht_assign || (eapply ht_consequence_left; [apply ht_assign|])
  | [ |- hoare_triple _ (If _ _ _) _ ] =>  apply ht_if
  | [ |- hoare_triple _ Skip _ ] =>
    apply ht_skip || (eapply ht_consequence_left; [apply ht_skip|])
  | [ |- hoare_triple _ (Assert _) _ ] =>
    apply ht_assert_true ||
    (eapply ht_consequence_left; [apply ht_assert_true|])
  | [ |- hoare_triple _ ?x _ ] => unfold x
  end.

Ltac fancy_ht_while e :=
  (let a := (apply ht_while with (I := e)) in
   (a ||
   (eapply ht_consequence_right; [a|]) ||
   (eapply ht_consequence_left; [a|]) ||
   (eapply ht_consequence; [a| |])));
  auto_triple.

Ltac cleanup_vars :=
  repeat match goal with
  | [ H : context [ match lookup ?x ?v with _ => _ end ] |- _ ] =>
    let E := fresh "E" in
    remember (match lookup x v with Some _ => _ | None => _ end) eqn:E; clear E
  end.

Ltac bash_assert_implies :=
  unfold assert_implies; intros; simpl in *; break_up_hyps; subst;
  find_rewrites; simpl in *;
  cleanup_vars; subst; auto; try lia.

Definition sound_triple (P : assertion) (c : cmd) (Q : assertion) : Prop :=
  forall v v' c',
    P v ->
    (v, c) -->* (v', c') ->
    c' <> Panic /\ (c' = Skip -> Q v').


(*
 * PROBLEM 14 [5 points, ~15 tactics]
 *
 * Prove the main theorem holds for this new language. You don't need to reprove
 * the old cases; just do the Amb case in the induction by filling out the
 * provided proof template below.
 *
 * Hint: First, state and prove a deconstruction lemma for executions starting
 * from Amb. This lemma should not require induction. Then use your lemma to
 * complete the case of the soundness proof, also without using induction.
 *)
Theorem hoare_ok :
  forall P c Q,
    hoare_triple P c Q ->
    sound_triple P c Q.
Proof.
  induction 1; intros v v' c' Hv Hstep.
  (* no need to prove these first 7 cases *)
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  (* Add a bullet point and complete the new case of the proof corresponding to
     the Hoare rule you added. *)
  (* YOUR CODE HERE *)
Admitted. (* Leave this line alone, since we didn't re-do the whole proof. *)

(* Here is a program using Amb to compute *a* factorial. *)
Definition ambfact :=
  "n" <- 0;;
  "acc" <- 1;;
  "continue" <- 1;;
  while "continue" loop
    "n" <- "n" + 1;;
    "acc" <- "acc" * "n";;
    Amb (
      "continue" <- 1
    ) (
      "continue" <- 0
    )
  done;;
  "output" <- "acc".

Fixpoint fact (n : nat) :=
  match n with
  | O => 1
  | S n => S n * fact n
  end.

(*
 * PROBLEM 15 [5 points, ~10 tactics]
 *
 * Prove this Hoare triple about ambfact, which says that if/when ambfact
 * terminates, the variable "output" contains the factorial of *something*.
 *
 * Hint: We have copy pasted the automation tactics again above, so they will
 * mostly work with our new language. However, we have not updated them to take
 * into account your new Hoare rule for Amb, since it was your job to write that
 * rule! You will either need to apply the rule manually (recommended) or update
 * the tactics yourself.
 *
 * Hint: As usual, the hard part is getting the loop invariant right.
 *)
Theorem ambfact_is_nodeterministic_fact :
  hoare_triple
    (fun _ => True)
    ambfact
    (fun v =>
      exists n,
        eval_arith "output" v = fact n).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


(*
Here is an implementation of the "parallel counter" from the HW3 Challenge
Problems using Amb. In case you didn't do those problems, the idea with this
program is similar to the two_counters program, except with three variables
instead of two. So we have "a" starting out at some number n, and "b" and "c"
starting out at 0. Then we loop while "a" or "b" are nonzero and "decrement a
and increment b" as well as "decrement b and increment c". The added twist is
that no ordering is imposed on these actions, which we encode using Amb.
*)
Definition amb_counter :=
  "a" <- "input";;
  "b" <- 0;;
  "c" <- 0;;
  while "a" + "b" loop
    Amb (
      If "a" (
        "a" <- "a" - 1;;
        "b" <- "b" + 1
      ) (
        Skip
      )
    ) (
      If "b" (
        "b" <- "b" - 1;;
        "c" <- "c" + 1
      ) (
        Skip
      )
    )
  done;;
  "output" <- "c".

(*
 * PROBLEM 16 [5 points, ~7 tactics]
 *
 * Prove this Hoare triple about amb_counter.
 *
 * Hint: As usual, the hard part is getting the loop invariant right. It should
 * be similar to your solution to Challenge Problem 25 from HW3, but it also
 * shouldn't be too bad to come up with it even if you didn't do that problem,
 * since it is also pretty similar to the invariant for two_counters.
 *)
Theorem amb_counter_triple :
  forall input,
    hoare_triple
      (fun v => eval_arith "input" v = input)
      amb_counter
      (fun v => eval_arith "output" v = input).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

End NondeterministicImp.

(*
             ____                  _     _                     ____
            / ___|    ___    ___  | |_  (_)   ___    _ __     | ___|
            \___ \   / _ \  / __| | __| | |  / _ \  | '_ \    |___ \
             ___) | |  __/ | (__  | |_  | | | (_) | | | | |    ___) |
            |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |____/

                  SECTION 5 : Intro to untyped lambda calculus
 *)


Module UTLC.
Inductive expr : Type :=
| Var : var -> expr
| Abs : var -> expr -> expr
| App : expr -> expr -> expr.

Declare Scope utlc_scope.
Coercion Var : var >-> expr.
Notation "'\' x ',' y" := (Abs x y) (left associativity, at level 75).
Infix "@" := App (left associativity, at level 68).
Delimit Scope utlc_scope with expr.
Bind Scope utlc_scope with expr.

Fixpoint subst (from : var) (to : expr) (e : expr) : expr :=
  match e with
  | Var x => if var_eq from x then to else e
  | Abs x e1 => Abs x (if var_eq from x then e1 else subst from to e1)
  | App e1 e2 => App (subst from to e1) (subst from to e2)
  end.

Inductive value : expr -> Prop :=
| value_abs :
  forall x e,
    value (\x, e).
Local Hint Constructors value : core.

Inductive step : expr -> expr -> Prop :=
| step_beta :
  forall x e v,
    value v ->
    step (App (\x, e) v) (subst x v e)
| step_app_left :
  forall e1 e1' e2,
    step e1 e1' ->
    step (App e1 e2) (App e1' e2)
| step_app_right :
  forall v1 e2 e2',
    step e2 e2' ->
    value v1 ->
    step (App v1 e2) (App v1 e2').
Local Hint Constructors step : core.

Notation "e '-->' e'" := (step e e') (at level 75).
Notation "e '-->*' e'" := (trc step e e') (at level 75).

(* Here are two lambda calculus programs. *)
Definition T := \"x", \"y", "x".
Definition F := \"x", \"y", "y".

(*
 * Reminder: We won't see lambda calculus until Week 7, but
 * you should be able to do these problems after lecture on
 * Tuesday, February 14.
 *)

(*
 * PROBLEM 17 [5 points, ~15 tactics]
 *
 * Prove the following fact about T and F.
 *
 * Hint: Our solution does not use automation. You can get a shorter proof if
 * you decide to use automation.
 *)
Lemma T_T :
  T @ T @ F -->* T.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

Definition Omega :=
  (\"x", "x" @ "x") @
  (\"x", "x" @ "x").

Definition diverges e :=
  forall e',
    e -->* e' ->
    exists e'',
      e' --> e''.

(*
 * PROBLEM 18 [10 points, ~20 tactics]
 *
 * Prove that Omega diverges.
 *
 * ***This problem is a challenge problem.*** It appears here instead of in the
 * challenge section because of technical limitations in our homework
 * infrastructure.
 *
 * Hint: Proceed by induction.
 *
 * Hint: Induct on the derivation of -->*.
 *)
Theorem omega_diverges :
  diverges Omega.
Proof.
  unfold diverges.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

End UTLC.







(* Feedback question *)
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


(* --- End of Core Points --- *)

(*
 * This is the end of the core points available for Homework 4. See below for
 * challenge points.
 *
 * To submit your homework, please follow the instructions at the end of the
 * README.md file in this directory.
 *
 * Please also see the README.md file to read about how we will grade this
 * homework assignment.
 *)

(*
             ____                  _     _                      __
            / ___|    ___    ___  | |_  (_)   ___    _ __      / /_
            \___ \   / _ \  / __| | __| | |  / _ \  | '_ \    | '_ \
             ___) | |  __/ | (__  | |_  | | | (_) | | | | |   | (_) |
            |____/   \___|  \___|  \__| |_|  \___/  |_| |_|    \___/

                         SECTION 6 : Challenge Problems
*)

(*

***Note that there is one challenge problem available in the previous section.

*)

(*
 * PROBLEM 20 [2 points, ~4 tactics]
 *
 * Prove that "+" on arith expressions behaves like "or" when thinking of
 * non-zero numbers as truthy.
 *
 * Hint: No need for induction.
 *)
Lemma imp_plus_is_or :
  forall e1 e2 v,
    eval_arith (e1 + e2)%arith v <> 0 <->
    eval_arith e1 v <> 0 \/ eval_arith e2 v <> 0.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * PROBLEM 21 [5 points, ~2 LOC]
 *
 * Define a function that takes an arithmetic expression and returns another
 * arithmetic expression that represents the "not" of the argument.
 *
 * In other words, the returned expression should evaluate to non-zero if and
 * only if the argument evaluates to zero.
 *
 * Hint: Remember that subtraction returns 0 whenever the "real" answer would be
 * negative.
 *
 * Hint: If e is the argument, "1 - e" is kinda vaguely right, but it doesn't
 * work if e is anything besides 0 or 1. So, find a way to convert e into a
 * number that is either 0 or 1, then use the "1 - ..." idea.
 *)
Definition imp_not (e : arith) : arith :=
  0. (* REPLACE WITH YOUR CODE *)

(*
 * PROBLEM 22 [3 points, ~5 tactics]
 *
 * Prove your answer to the previous problem correct.
 *
 * Hint: No need for induction.
 *
 * Hint: The hard part is getting the answer to the previous problem right.
 *)
Lemma imp_not_is_not :
  forall e v,
    eval_arith (imp_not e) v <> 0 <->
    eval_arith e v = 0.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
Consider this inductive definition of what it means for one expression to be a
subexpression of another expression.
*)
Inductive subexpr : arith -> arith -> Prop :=
| subexpr_refl :
  forall e,
    subexpr e e
| subexpr_inl_plus :
  forall e1 e1' e2,
   subexpr e1' e1 ->
   subexpr e1' (Plus e1 e2)
| subexpr_inl_minus :
  forall e1 e1' e2,
    subexpr e1' e1 ->
    subexpr e1' (Minus e1 e2)
| subexpr_inl_times :
  forall e1 e1' e2,
    subexpr e1' e1 ->
    subexpr e1' (Times e1 e2)
| subexpr_inr_plus :
  forall e1 e2' e2,
    subexpr e2' e2 ->
    subexpr e2' (Plus e1 e2)
| subexpr_inr_minus :
  forall e1 e2' e2,
    subexpr e2' e2 ->
    subexpr e2' (Minus e1 e2)
| subexpr_inr_times :
  forall e1 e2' e2,
    subexpr e2' e2 ->
    subexpr e2' (Times e1 e2).
Local Hint Constructors subexpr : core.

(*
Here's a quick example showing "x" is a subexpression of some larger expression.
*)
Example subexpr_example :
  subexpr "x" (1 * "x" + "z" - ("y" + 4) * "y")%arith.
Proof.
  eauto.
Qed.

(*
 * PROBLEM 23 [3 points, ~5 tactics]
 *
 * Prove that subexpr is transitive.
 *
 * Hint: Proceed by induction.
 *
 * Hint: If you get stuck or are in a longer proof, you might want to try
 * inducting on something else. The staff were not able to guess the right thing
 * to induct on with our first try...
 *)
Theorem subexpr_transitive:
  forall e1 e2 e3,
    subexpr e1 e2 ->
    subexpr e2 e3 ->
    subexpr e1 e3.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(* We define a function that computes the depth of an AST. *)
Fixpoint ast_depth (e : arith) : nat :=
  match e with
  | Const _ => 1
  | Var _   => 1
  | Plus l r
  | Minus l r
  | Times l r => S (Nat.max (ast_depth l) (ast_depth r))
  end.

(*                           Depth
                  "-"          4
              /        \
            +          *       3
           / \        / \
          *  "z"     +   "y"   2
         / \        / \
        1  "x"   " y"  4       1
*)
Compute (ast_depth ((1 * "x" + "z")%arith - (("y" + 4) * "y")%arith)).

(*
 * PROBLEM 24 [2 points, ~6 tactics]
 *
 * Prove that if e1 is a subexpression of e2, then the depth of e1 is less than
 * or equal to the depth of e2.
 *
 * Hint: Inducting on different things will make the proof easier / harder!
 *)
Theorem subexpr_depth_leq:
  forall e1 e2,
    subexpr e1 e2 ->
    ast_depth e1 <= ast_depth e2.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * PROBLEM 25 [5 points, ~20 tactics]
 *
 * Prove that subexpr is anti-symmetric, i.e., if e1 is a subexpression of e2,
 * and e2 is also a subexpression of e1, then e1 = e2.
 *
 * Hint: This one is surprisingly tricky. As far as the staff knows, the only
 * way to prove it is to use the notion of ast_depth somewhere...
 *)
Theorem subexpr_anti_symmetry :
  forall e1 e2,
  subexpr e1 e2 ->
  subexpr e2 e1 ->
  e1 = e2.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)
