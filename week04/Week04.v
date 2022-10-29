(* include libraries and notations *)
Require Import Arith Lia List String.
Import ListNotations.
Open Scope string.

(* enable type inference *)
Set Implicit Arguments.

(* the type of an "equality decider" *)
Definition eq_dec (A : Type) :=
  forall (x : A),
    forall (y : A),
      {x = y} + {x <> y}.

(* We'll continue to use strings for variable names. *)
Notation var := string.
Definition var_eq : eq_dec var := string_dec.

(* We'll also continue to associate variables with nats in valuations. *)
Definition valuation := list (var * nat).

Fixpoint lookup (x : var) (v : valuation) : option nat :=
  match v with
  | [] => None
  | (y, n) :: v' =>
    if var_eq x y
    then Some n
    else lookup x v'
  end.

(* And we'll continue to use our arithmetic expression language.
   Here's the arith syntax: *)
Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

(* And its semantics via an interpreter: *)
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

(* Finally, we'll also copy over our arith notations. *)
Declare Scope arith_scope.
Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Infix "+" := Plus : arith_scope.
Infix "-" := Minus : arith_scope.
Infix "*" := Times : arith_scope.
Delimit Scope arith_scope with arith.
Bind Scope arith_scope with arith.

(*
If you could use a refresher on any of these definitions, please check out
the code from Week02 where they're discussed in detail:
    https://gitlab.cs.washington.edu/cse-505-21sp/cse-505-21sp/-/blob/main/week02/Week02.v
*)

(* Copied from Week03.v *)
Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| trc_refl :
    forall x,
      trc R x x
| trc_front :
    forall x y z,
      R x y ->
      trc R y z ->
      trc R x z.

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
(* End of copied stuff *)

Module Imp.

(*
CREDITS: This formalization also follows the development from Chlipala's
excellent FRAP textbook: http://adam.chlipala.net/frap/
*)

(*
Now let's move on to formalizing an imperative programming language with
unbounded loops. Since programs in our language are not guaranteed to terminate,
we won't be able to model its semantics using an interpreter because every
function in Coq must always terminate on all inputs (crucial for soundness!).
Instead we'll see how to *relationally* specify the meaning of programs in our
language using "operational semantics".

First we need to give the syntax of our language:
*)
Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| If (e : arith) (then_ else_ : cmd)
| While (e : arith) (body : cmd).

(*
This is very similar our "cmd" language from Week02, but we added an "If"
command and swapped the bounded "Repeat" loops out for an unbounded form of
"While" loops.

We will also define notations to make it easier for humans to read and write
"cmd" programs, similar to our notations for arithmetic expressions.
*)
Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";;" := Sequence (at level 76). (* ;; instead of ; because it interferes
                                         with record syntax *)
Notation "'when' e 'then' then_ 'else' else_ 'done'" :=
  (If e%arith then_ else_) (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" :=
  (While e%arith body) (at level 75).

(*
So far, we've only specified the *syntax* of our imperative language. Now let's
move on to its *semantics*. We'll specify a step relation for how "cmd"s
execute. Looks a lot like a transition relation doesn't it?
*)
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


(* Here's our old friend the factorial program. *)
Definition factorial : cmd :=
  "n" <- "input";;
  "acc" <- 1;;
  while "n" loop
    "acc" <- "acc" * "n";;
    "n" <- "n" - 1
  done;;
  "output" <- "acc".

(*
We can use the step relation to reason about this version of factorial just like we
did in week 3, except that now the steps are *much* finer grained. In week 3, we
had one step per iteration of the main loop, and no other kinds of steps. But
now, we have separate steps for roughly every line of code. As a general rule,
finer grained steps make proofs more annoying :)

Let's start with a "unit test", proving that factorial returns 24 when given 4.
(There's a problem like this on HW3. Be sure to read the better proofs below.
*)
Example factorial_4 :
  forall v1,
    lookup "input" v1 = Some 4 ->
    exists v2,
      trc step (v1, factorial) (v2, Skip) /\
      lookup "output" v2 = Some 24.
(*
Reading this theorem statement, it says if we start in any valuation v1 where
the input is 4, then there exists a final valuation v2 such that factorial
terminates (i.e., steps to Skip) in valuation v2 and such that the output is 24.

Sounds pretty straightforward. What do we need to prove it? At the end of the
day, we need to give a "witness" for v2, and then show that (v1, factorial)
steps to (v2, Skip) and that v2 maps "output" to 24. What is v2? If you think
about it, it's actually pretty complicated, because it consists of a trace of
every single assignment statement ever executed by factorial on this run. So if
we were to try to write it down explicitly using "exists blah.", it would be
super annoying. Luckily, eexists will allow us to implicitly "compute" v2 by
doing the rest of the proof. Check it out!
*)
Proof.
  intros v1 H.
  eexists. (* Put in a placeholder for v2 for now. *)
  split.
  - (* The interesting part of the proof is proving that factorial terminates in
       (v2, Skip). We need to build up a derivation tree for trc, where each
       single step is also justified by a derivation tree of step.

       The first step is to execute the very first assignment statement in the
       program, "n" <- "input". Since this statement is "inside" several, Seq
       nodes, we have several applications of StepSeqLStep to get down there. *)
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepAssign.
    reflexivity.
    (* Now we are left with a Skip out front of our Seq. Get rid of it. *)
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepSeqLDone.
    (* Time for the next assignment statement... *)
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepAssign.
    reflexivity.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLDone.
    (* Now we're at the top of the loop. *)
    cbn. rewrite H.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepWhileTrue. (* Try to enter the loop. *)
    cbn. lia. (* Prove that we actually do enter the loop. *)
    (* Now execute the body of the loop. *)
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepAssign.
    reflexivity.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepSeqLDone.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepAssign.
    reflexivity.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLDone.
    (* We're back at the top of the loop. Time for the next iteration. *)
    cbn.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepWhileTrue.
    cbn. lia.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepAssign.
    reflexivity.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepSeqLDone.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepAssign.
    reflexivity.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLDone.
    (* next iteration *)
    cbn.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepWhileTrue.
    cbn. lia.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepAssign.
    reflexivity.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepSeqLDone.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepAssign.
    reflexivity.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLDone.
    (* next iteration *)
    cbn.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepWhileTrue.
    cbn. lia.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepAssign.
    reflexivity.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepSeqLDone.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLStep.
    apply StepAssign.
    reflexivity.
    eapply trc_front.
    apply StepSeqLStep.
    apply StepSeqLDone.
    cbn.
    (* Finally n is 0. Try to exit the loop. *)
    eapply trc_front.
    apply StepSeqLStep.
    apply StepWhileFalse.
    cbn. lia. (* Prove we actually do exit the loop. *)
    (* Just a few more steps left after the loop. *)
    eapply trc_front.
    apply StepSeqLDone.
    eapply trc_front.
    apply StepAssign.
    reflexivity.
    cbn.
    (* Finally, we end the proof of trc using trc_refl. If you look carefully at
       the goal here, you can "see" the actual v2 that gets plugged in for our
       placeholder. Yikes! *)
    apply trc_refl.
  - (* All that's left is to show *)
    cbn.
    reflexivity.
Qed. (* Nailed it, only 130 ish tactics. Lots of copy paste! *)

(*
Okay, that was supposed to be a "unit test", but it was a huge pain! This is
partially because proving "specific" theorems is more tedious than proving
"general" theorems. But we can also improve the situation using some automated
tactics.
*)

(* like econstructor, but avoid StepWhileTrue b/c infinite tactic loops *)
Ltac step_easy :=
  repeat (
    apply StepSeqLDone ||
    eapply StepSeqLStep ||
    (apply StepWhileFalse; cbn; reflexivity) ||
    (apply StepAssign; reflexivity)
  ); cbn.


Example factorial_4_again :
  forall v1,
    lookup "input" v1 = Some 4 ->
    exists v2,
      trc step (v1, factorial) (v2, Skip) /\
      lookup "output" v2 = Some 24.
Proof.
  intros v1 H.
  eexists.
  split.
  - econstructor.
    step_easy.
    cbn. rewrite H.
    econstructor.
    step_easy.
    econstructor.
    step_easy.
    cbn.
    econstructor.
    step_easy.
    econstructor.
    step_easy.
    apply StepWhileTrue.
    cbn. lia.
    econstructor.
    step_easy.
    econstructor.
    step_easy.
    cbn.
    econstructor.
    step_easy.
    cbn.
    econstructor.
    step_easy.
    econstructor.
    step_easy.
    apply StepWhileTrue.
    cbn. lia.
    econstructor.
    step_easy.
    econstructor.
    step_easy.
    cbn.
    econstructor.
    step_easy.
    cbn.
    econstructor.
    step_easy.
    econstructor.
    step_easy.
    apply StepWhileTrue.
    cbn. lia.
    econstructor.
    step_easy.
    econstructor.
    step_easy.
    cbn.
    econstructor.
    step_easy.
    cbn.
    econstructor.
    step_easy.
    econstructor.
    step_easy.
    apply StepWhileTrue.
    cbn. lia.
    econstructor.
    step_easy.
    econstructor.
    step_easy.
    cbn.
    econstructor.
    step_easy.
    cbn.
    econstructor.
    step_easy.
    econstructor.
    step_easy.
    econstructor.
    step_easy.
    econstructor.
    step_easy.
    cbn.
    econstructor.
  - reflexivity. (* ok that only took half as many tactics *)
  Restart.
  (* We can do even better with more tactics. *)
  Ltac trc_easy :=
    eapply trc_front; [solve [step_easy]|]; cbn.

  Ltac trc_enter_loop :=
    eapply trc_front; [step_easy; apply StepWhileTrue; cbn; try lia|]; cbn.

  intros v1 H.
  eexists.
  split.
  - trc_easy. rewrite H.
    repeat trc_easy. (* Executes as many assignments/skips as possible. *)
    trc_enter_loop.
    repeat trc_easy.
    trc_enter_loop.
    repeat trc_easy.
    trc_enter_loop.
    repeat trc_easy.
    trc_enter_loop.
    repeat trc_easy.
    (* exited the loop *)
    apply trc_refl.
  - reflexivity.
Qed.

(*
We can also use the transition relation to reason about executions of the
program on *all* possible inputs, by constructing a transition system. We need
to answer the three questions: state space, initial states, and transition
relation. The key idea is:

    The code "left to execute" is part of the state.

The other piece of state will be the valuation. As the program executes, the
code "left to execute" evolves. If the program terminates, then eventually the
code left to execute will become Skip. Otherwise, it will just continue evolving
over time. If you like to think low level, you can think of the code left to
execute as tracking the "program counter", since it tells you what to do next.

All of this leads us to realizing our state space is (valuation * cmd). The
definition of step above already gives us our transition relation on this state
space, so we just need the initial states.

Given a particular starting valuation and a particular program we want to
execute, we can make a "singleton set" of initial states just one pair,
consisting of that valuation and program.
*)
Definition cmd_init (v : valuation) (c : cmd) (s : valuation * cmd) : Prop :=
  s = (v, c).

(*
Then we can "compute" the entire transition system from a starting valuation and
program by using cmd_init as the initial states, and using step as the
transition relation.

One interesting aspect of this definition is that cmd_init is parameterized on
the valuation and command, but step is not. In other words, every transition
system returned by cmd_to_trsys has the *same* transition relation! But they
will have different initial states. If you think about the pictures we drew for
transition systems, this might tickle your sixth sense for inductiveness. There
are many transitions that are not reachable from the initial states (since the
transition relation captures the execution of all possible programs from all
possible valuations!!), so we will need a quite strong invariant to make
anything inductive (in order to rule out most programs and valuations, since
they will not be reachable from our initial state). More on that later.
*)
Definition cmd_to_trsys (v : valuation) (c : cmd) : trsys (valuation * cmd) :=
  {| Init := cmd_init v c
   ; Step := step
   |}.

(*

Let's switch to a simpler example. We will come back to factorial below.
*)

Definition counter :=
  "x" <- 5;;
  while 1 loop
    "x" <- "x" + 1
  done.

Definition counter_sys : trsys (valuation * cmd) :=
  cmd_to_trsys [] counter.

(*
Let's prove x is always at least 5. Here's our first attempt at stating this
property.
*)
Definition counter_ge_5_attempt (s : valuation * cmd) :=
  let (v, c) := s in
  exists x,
    lookup "x" v = Some x /\
    x >= 5.

Theorem counter_ge_5_attempt_invariant :
  is_invariant counter_sys counter_ge_5_attempt.
Proof.
  invariant_induction_boilerplate.
  (* Uh oh, this just isn't true initially! x is not mapped to anything yet. *)
Abort.

(*
Let's try again. We can say "either we haven't started yet, or x is >= 5".
*)
Definition counter_ge_5 (s : valuation * cmd) :=
  let (v, c) := s in
  c = counter \/
  exists x,
    lookup "x" v = Some x /\
    x >= 5.

Theorem counter_ge_5_invariant :
  is_invariant counter_sys counter_ge_5.
Proof.
  invariant_induction_boilerplate.
  - auto.
  - destruct s1 as [v1 c1], s2 as [v2 c2].
    destruct IH as [IH|IH].
    + (* Here we are about to take the first step. No problem! *)
      subst.
      inversion Hstep; subst; clear Hstep.
      inversion H0; subst; clear H0.
      (* We just set x to 5, so it's easy to show the right disjunct. *)
      cbn. eauto.
    + (* In the second case, we know that x is >= 5, and now we take a step.
         But since our invariant says nothing about c1, we're stuck. In
         principle, c1 could be literally any program that could do anything to
         x. But we know actually c1 should be a program that arises during
         execution of the counter program. What are those programs? *)
Abort.

Definition counter_programs (s : valuation * cmd) :=
  let (v, c) := s in
  c = counter \/
  c = (Skip;;
       while 1 loop
         "x" <- "x" + 1
       done) \/
  c = (while 1 loop
         "x" <- "x" + 1
       done) \/
  c = ("x" <- "x" + 1;;
       while 1 loop
         "x" <- "x" + 1
       done) \/
  c = Skip.

Theorem counter_programs_invariant :
  is_invariant counter_sys counter_programs.
Proof.
  invariant_induction_boilerplate.
  - auto.
  - destruct s1 as [v1 c1], s2 as [v2 c2].
    (* intuition is a great tactic for busting up a bunch of disjunctions *)
    intuition; subst; inversion Hstep; subst; clear Hstep; auto.
    + inversion H0; subst; clear H0. auto.
    + inversion H0; subst; clear H0.
    + inversion H0; subst; clear H0. auto.
Qed.

(*
Building on this idea, we can also make our invariant talk about the valuations,
not just the programs. This will let us prove x >= 5.
*)

(* First, here is the only fact we ever need about the valuation. *)
Definition counter_valuation_x_ge_5 (v : valuation) :=
  exists x,
    lookup "x" v = Some x /\
    x >= 5.

(*
Then we can just paste this into every branch except the very first one,
where x is not yet initialized.
*)
Definition counter_programs_x_ge_5 (s : valuation * cmd) :=
  let (v, c) := s in
  c = counter \/
  (c = (Skip;;
        while 1 loop
          "x" <- "x" + 1
        done) /\ counter_valuation_x_ge_5 v) \/
  (c = (while 1 loop
          "x" <- "x" + 1
        done) /\ counter_valuation_x_ge_5 v) \/
  (c = ("x" <- "x" + 1;;
        while 1 loop
          "x" <- "x" + 1
        done) /\ counter_valuation_x_ge_5 v) \/
  (c = Skip /\ counter_valuation_x_ge_5 v).

Lemma counter_programs_x_ge_5_invariant :
  is_invariant counter_sys counter_programs_x_ge_5.
Proof.
  invariant_induction_boilerplate.
  - auto.
  - destruct s1 as [v1 c1], s2 as [v2 c2].
    unfold counter_valuation_x_ge_5 in *.
    intuition; subst; inversion Hstep; subst; clear Hstep; auto.
    + inversion H0; subst; clear H0. cbn. eauto 10.
    + inversion H0; subst; clear H0.
    + destruct H1 as [x [Hlook Hx]]. cbn. eauto 10.
    + destruct H1 as [x [Hlook Hx]]. cbn. eauto 10.
    + inversion H0; subst; clear H0.
      destruct H1 as [x [Hlook Hx]]. cbn. rewrite Hlook. right. left.
      split; auto. eexists. split; auto. lia.
Qed.

(* Finally, our theorem follows. *)
Theorem counter_ge_5_invariant :
  is_invariant counter_sys counter_ge_5.
Proof.
  apply invariant_implies with (P := counter_programs_x_ge_5).
  - apply counter_programs_x_ge_5_invariant.
  - unfold counter_programs_x_ge_5, counter_ge_5.
    intros [v c] Hinv.
    intuition.
Qed.

(*
It's worth reflecting on what just happened. Last week, when we manually modeled
the counter system as a transition system, the invariant x >= 0 was inductive.
This week, it wasn't even an invariant!! (Since it wasn't true in the initial
state.) Even after fixing that problem so that the property was an invariant,
it still wasn't inductive, this time because it said nothing about the program
syntax. The moral of the story is that when using a finer-grained step relation
with many more states, your invariant has to say more to "get rid" of all that
extra generality.
*)

(* Ok back to factorial. *)
Definition factorial_sys (input : nat) : trsys (valuation * cmd) :=
  cmd_to_trsys [("input", input)] factorial.

Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => fact n' * S n'
  end.

(*
Let's prove that when the program terminates, it computes the right answer.
*)
Definition factorial_safe (input : nat) (s : valuation * cmd) : Prop :=
  let (v, c) := s in
  c = Skip ->
  lookup "output" v = Some (fact input).

Theorem factorial_safe_invariant :
  forall input,
    is_invariant (factorial_sys input) (factorial_safe input).
Proof.
  (* Laughably not inductive. factorial_safe says nothing unless c = Skip.
     We're not even going to try to prove it by induction because it would be
     hopeless *)
Abort.

(*
Just like with the counter system, our invariant now needs to constrain the
"reachable programs". There are many of them, so we give them all shorter names.
*)

Definition factorial_after_step_one :=
  Skip;;
  "acc" <- 1;;
  while "n" loop
    "acc" <- "acc" * "n";;
    "n" <- "n" - 1
  done;;
  "output" <- "acc".

Definition factorial_after_step_two :=
  "acc" <- 1;;
  while "n" loop
    "acc" <- "acc" * "n";;
    "n" <- "n" - 1
  done;;
  "output" <- "acc".

Definition factorial_after_step_three :=
  Skip;;
  while "n" loop
    "acc" <- "acc" * "n";;
    "n" <- "n" - 1
  done;;
  "output" <- "acc".

Definition factorial_top_of_loop :=
  while "n" loop
    "acc" <- "acc" * "n";;
    "n" <- "n" - 1
  done;;
  "output" <- "acc".

Definition factorial_body_start :=
  "acc" <- "acc" * "n";;
  "n" <- "n" - 1;;
  while "n" loop
    "acc" <- "acc" * "n";;
    "n" <- "n" - 1
  done;;
  "output" <- "acc".

Definition factorial_body_after_step_one :=
  Skip;;
  "n" <- "n" - 1;;
  while "n" loop
    "acc" <- "acc" * "n";;
    "n" <- "n" - 1
  done;;
  "output" <- "acc".

Definition factorial_body_after_step_two :=
  "n" <- "n" - 1;;
  while "n" loop
    "acc" <- "acc" * "n";;
    "n" <- "n" - 1
  done;;
  "output" <- "acc".

Definition factorial_after_loop :=
  Skip;;
  "output" <- "acc".

Definition factorial_last_step :=
  "output" <- "acc".

(*
For each reachable program, we also need to make an assertion about the
valuation. We also give all the assertions shorter names.
*)

(* Here's the main loop invariant. *)
Definition factorial_loop_invariant input v :=
  exists n acc,
    lookup "n" v = Some n /\
    lookup "acc" v = Some acc /\
    fact n * acc = fact input.

(*
After we evaluate the loop exit condition, if we plan to enter the loop, we
learn that n is nonzero.
*)
Definition factorial_body_invariant input v :=
  exists n acc,
    lookup "n" v = Some (S n) /\
    lookup "acc" v = Some acc /\
    fact (S n) * acc = fact input.

(*
After executing the first statement in the loop body, we have this intermediate
assertion.
*)
Definition factorial_body_invariant_after_step input v :=
  exists n acc,
    lookup "n" v = Some (S n) /\
    lookup "acc" v = Some acc /\
    fact n * acc = fact input.

(*
Now the global invariant for the whole transition system. It says that the
command must be one of the reachable programs above. For each program, we also
constrain the valuation with the corresponding assertion.
*)

Definition factorial_inv (input : nat) (s : valuation * cmd) : Prop :=
  let (v, c) := s in
  (c = factorial /\ lookup "input" v = Some input) \/
  (c = factorial_after_step_one /\ lookup "n" v = Some input) \/
  (c = factorial_after_step_two /\ lookup "n" v = Some input) \/
  (c = factorial_after_step_three /\ factorial_loop_invariant input v) \/
  (c = factorial_top_of_loop /\ factorial_loop_invariant input v) \/
  (c = factorial_body_start /\ factorial_body_invariant input v) \/
  (c = factorial_body_after_step_one /\ factorial_body_invariant_after_step input v) \/
  (c = factorial_body_after_step_two /\ factorial_body_invariant_after_step input v) \/
  (c = factorial_after_loop /\ lookup "acc" v = Some (fact input)) \/
  (c = factorial_last_step /\ lookup "acc" v = Some (fact input)) \/
  (c = Skip /\ lookup "output" v = Some (fact input)).

(*
At this point, we can see how this invariant corresponds to labeling each
statement with an "invariant assertion" that is true every time control flow
reaches that point. This technique is called "the method of invariant
assertions" and is one of the earliest approaches to program verification.
*)

(*
A very common shorthand tactic for doing inversion, substituting by all the
equalities, and deleting the original hypothesis.
*)
Ltac invc H := inversion H; subst; clear H.

(*
Now let's prove our invariant is an invariant by induction. In this first
version of the proof, we will use relatively little automation.
*)
Lemma factorial_inv_invariant :
  forall input,
    is_invariant (factorial_sys input) (factorial_inv input).
Proof.
  invariant_induction_boilerplate.
  - auto.
  - unfold factorial_loop_invariant, factorial_body_invariant.
    unfold factorial_body_invariant_after_step.
    destruct s1 as [v1 c1], s2 as [v2 c2].
    intuition idtac; subst.
    + invc Hstep. invc H0. invc H2. invc H0.
      cbn [eval_arith].
      rewrite H1.
      auto.
    + invc Hstep. invc H0. invc H2. invc H0. auto.
    + invc Hstep. invc H0. invc H2.
      right. right. right. left. split; [reflexivity|].
      exists input, 1.
      cbn. split; auto. split; auto. lia.
    + destruct H1 as [n [acc [? []]]].
      invc Hstep. invc H3. invc H4.
      eauto 20.
    + destruct H1 as [n [acc [? []]]].
      invc Hstep. invc H3.
      -- right. right. right. right. right. left. split; [reflexivity|].
         cbn in *. rewrite H in *.
         destruct n; [congruence|]. (* note: destruct before exists *)
         eauto.
      -- right. right. right. right. right. right. right. right. left. split; [reflexivity|].
         cbn in *. rewrite H in *. subst n.
         cbn in *. rewrite H0, <- H1. f_equal. lia.
    + destruct H1 as [n [acc [? []]]].
      invc Hstep. invc H3. invc H4. invc H3.
      right. right. right. right. right. right. left. split; [reflexivity|].
      cbn. rewrite H, H0. eexists. eexists. split; eauto. split; eauto.
      rewrite <- H1. cbn. lia.
    + destruct H1 as [n [acc [? []]]].
      invc Hstep. invc H3. invc H4. invc H3.
      eauto 15.
    + destruct H1 as [n [acc [? []]]].
      invc Hstep. invc H3. invc H4.
      right. right. right. left. split; [reflexivity|].
      cbn. rewrite H. cbn. rewrite Nat.sub_0_r. eauto.
    + invc Hstep. invc H1. invc H0.
      auto 20.
    + invc Hstep.
      right. right. right. right. right. right. right. right. right. right.
      split; auto.
      cbn. rewrite H1. auto.
    + invc Hstep.
Qed.

(* Call invc on a hypothesis that something steps. *)
Ltac invert_one_step :=
  match goal with
  | [ H : step _ _ |- _ ] => invc H
  end.

(* Call invert_one_step over and over until nothing is left to do. *)
Ltac invert_steps :=
  repeat invert_one_step.

(*
This tactic is specific to the shape of the invariant above, which is a big
disjunction of conjunctions. The tactic tries to guess which disjunct is
correct by looking for a disjunct whose first *conjunct* is provable by
reflexivity.
*)
Ltac magic_select_case :=
  repeat match goal with
  | [ |- _ \/ _ ] => (left; split; [reflexivity|]) || right
  | _ => try split; [reflexivity|]
  end.

(* Destruct all hypotheses that are "exists" or "/\". *)
Ltac break_up_hyps :=
  repeat match goal with
  | [ H : exists _, _ |- _ ] => destruct H
  | [ H : _ /\ _ |- _ ] => destruct H
  end.

(*
Rewrite left-to-right everywhere by all (unquantified) hypotheses as many
times as possible.
*)
Ltac find_rewrites :=
  repeat match goal with
  | [ H : _ = _ |- _ ] => rewrite H in *
  end.

(* Here's a more automated version. *)
Lemma factorial_inv_invariant_again :
  forall input,
    is_invariant (factorial_sys input) (factorial_inv input).
Proof.
  invariant_induction_boilerplate.
  - auto.
  - destruct s1 as [v1 c1], s2 as [v2 c2].
    (* when the goal is huge, tactic performance suffers, so fold it up. *)
    fold (factorial_inv input (v2, c2)).
    (* Here's a huge tactic block.
       - intuition breaks up disjunctions and conjunctions in the context, so
         we get one subgoal for each reachable program
       - invert_steps determines the possible next steps for each subgoal
         - for most subgoals, there is exactly one next step
         - when we are at the top of the loop, there are two:
           - one for entering the loop body
           - one for exiting the loop
         - when we are at the very end (Skip), there are zero next steps
       - we then unfold a bunch of stuff
       - magic_select_case finds the disjunct in the goal corresponding to the
         correct next step
       - then we clean up the context and try a huge eauto
         (20 is the search depth)
     *)
    intuition; subst; invert_steps;
    unfold factorial_inv;
    unfold factorial_loop_invariant, factorial_body_invariant in *;
    unfold factorial_body_invariant_after_step in *;
    magic_select_case;
    break_up_hyps;
    cbn in *;
    find_rewrites;
    eauto 20.
    (* What remains is 5 "interesting" subgoals. *)
    + (* The program reaches the top of the loop for the very first time. We
         need to establish the loop invariant. *)
      eexists. eexists.
      split; eauto. split; eauto. lia.
    + (* The program evaluates the loop condition and finds it true, so prepares
         to enter the loop body. We "remember" the fact that n is nonzero. *)
      destruct x; [congruence|]. (* note: destruct before exists *)
      eauto.
    + (* The program evaluates the loop condition and finds it false, so exits
         the loop. We need to use the loop invariant to establish the assertion
         after the loop. *)
      subst.
      cbn in *. rewrite <- H1. f_equal. lia.
    + (* In the body of the loop, the program assigns to acc. We need to
         establish the intermediate assertion. *)
      eexists. eexists. split; eauto. split; eauto.
      rewrite <- H1. cbn. lia.
    + (* The program finishes the second statement in the loop body. We need to
         re-establish the loop invariant. *)
      eexists. eexists. split; eauto. split; eauto.
      cbn. rewrite <- H1. f_equal. f_equal. lia.
Qed.

(*
As usual, once we have an inductive invariant, proving our original "safety"
claim is a straightforward application of invariant_implies.
*)
Theorem factorial_safe_invariant :
  forall input,
    is_invariant (factorial_sys input) (factorial_safe input).
Proof.
  intros input.
  apply invariant_implies with (P := factorial_inv input).
  - apply factorial_inv_invariant.
  - unfold factorial_inv, factorial_safe.
    intros [v c] Hinv Hfinal.
    subst.
    intuition; discriminate.
Qed.


Lemma deconstruct_sequence_execution :
  forall v v' c1 c2 c',
    trc step (v, c1;; c2) (v', c') ->
    exists v1' c1',
      trc step (v, c1) (v1', c1') /\
      (c' = (c1';; c2) \/
        (c1' = Skip /\ trc step (v1', c2) (v', c'))).
Proof.
  intros v v' c1 c2 c' Hstep.
  induction Hstep.
  - (* wait... what is x??? *)
  Restart.
  intros v v' c1 c2 c' Hstep.
  remember (v, c1;;c2) as s.
  remember (v', c') as s'.
  revert v c1 c2 v' c' Heqs Heqs'.
  induction Hstep; intros v c1 c2 v' c' ? ?; subst.
  - invc Heqs'. eexists. eexists. split. constructor. auto.
  - invc H.
    + specialize (IHHstep v'0 c1' c2 v' c' eq_refl eq_refl).
      destruct IHHstep as [v1' [c1'0 [Hstep' Hc']]].
      eexists. eexists.
      split. eapply trc_front; eauto.
      intuition.
    + eexists. eexists. split. apply trc_refl.
      auto.
Qed.

Lemma trc_seq_l_trc :
  forall v1 c1 v2 c2 c3,
    trc step (v1, c1) (v2, c2) ->
    trc step (v1, c1;;c3) (v2, c2;;c3).
Proof.
  intros v1 c1 v2 c2 c3 Hstep.
  remember (v1, c1) as s1.
  remember (v2, c2) as s2.
  revert v1 c1 v2 c2 c3 Heqs1 Heqs2.
  induction Hstep; intros v1 c1 v2 c2 c3 ? ?; subst.
  - invc Heqs2. econstructor.
  - destruct y as [v1' c1'].
    specialize (IHHstep v1' c1' v2 c2 c3 eq_refl eq_refl).
    eapply trc_front. apply StepSeqLStep. eauto. eauto.
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
  induction Htrcb.
  - constructor.
  - eapply trc_back; eauto.
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
  - eapply Hind; eauto.
    apply trc_backward_implies_trc.
    auto.
Qed.

Definition loop_runs_to (e : arith) (c : cmd) (v1 v2 : valuation) :=
  eval_arith e v1 <> 0 /\
  trc step (v1, c) (v2, Skip).

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

Lemma deconstruct_while_execution :
  forall v v' e c c',
    trc step (v, while e loop c done) (v', c') ->
    exists v1,
      trc (loop_runs_to e c) v v1 /\
      ((c' = Skip /\ v' = v1 /\ eval_arith e v' = 0) \/
       (c' = (while e loop c done) /\ v' = v1) \/
       (eval_arith e v1 <> 0 /\ exists c1', trc step (v1, c) (v', c1') /\ c' = (c1' ;; while e loop c done))).
Proof.
  intros v v' e c c' Htrc.
  prepare_induct_trc_step Htrc.
  revert e c.
  induction Htrc using trc_reverse_ind; intros v e c v' c' ? ?; subst.
  - invc Heqs'. (* eexists. split.
    + apply trc_refl.
    + auto.  *)
    eauto 10 using trc_refl.
  - destruct y as [v2 c2].
    specialize (IHHtrc v e c v2 c2 eq_refl eq_refl).
    destruct IHHtrc as [v1 [Htrc1 IH]].
    destruct IH as [[? [? He]]|[[? ?]|[He [c1' [Hc ?]]]]]; subst.
    + invc H.
    + invc H.
      * eexists. split; eauto.
        right. right. split; auto.
        eexists. split; eauto. constructor.
      * eauto 10.
    + invc H.
      * eexists. split; eauto.
        right. right. split; auto.
        eexists. split; [|reflexivity].
        eapply trc_back; eauto.
      * exists v'. split.
        -- eapply trc_back; eauto. split; auto.
        -- auto.
Qed.


Fixpoint strength_reduction (e : arith) : arith :=
  match e with
  | Const _ => e
  | Var _ => e
  | Plus e1 e2 => Plus (strength_reduction e1) (strength_reduction e2)
  | Minus e1 e2 => Minus (strength_reduction e1) (strength_reduction e2)
  | Times (Const 2) e2 =>
    let e2' := strength_reduction e2 in
    Plus e2' e2'
  | Times e1 e2 => Times (strength_reduction e1) (strength_reduction e2)
  end.

Fixpoint cmd_xform_arith (f : arith -> arith) (c : cmd) : cmd :=
  match c with
  | Skip => Skip
  | Assign x e => Assign x (f e)
  | Sequence c1 c2 => Sequence (cmd_xform_arith f c1) (cmd_xform_arith f c2)
  | If e c1 c2 => If (f e) (cmd_xform_arith f c1) (cmd_xform_arith f c2)
  | While e c => While (f e) (cmd_xform_arith f c)
  end.

Lemma cmd_xform_arith_equiv_step :
  forall f,
    (forall e v, eval_arith (f e) v = eval_arith e v) ->
    forall v c v' c',
      step (v, c) (v', c') ->
      step (v, cmd_xform_arith f c) (v', cmd_xform_arith f c').
Proof.
  intros f Hf v c v' c' Hstep.
  induct_step Hstep; invc Heqs; invc Heqs'; simpl; constructor;
   try rewrite Hf; auto.
Qed.

Theorem cmd_xform_arith_equiv :
  forall f,
    (forall e v, eval_arith e v = eval_arith (f e) v) ->
    forall v c v' c',
      trc step (v, c) (v', c') ->
      trc step (v, cmd_xform_arith f c) (v', cmd_xform_arith f c').
Proof.
  intros f Hf v c v' c' Htrc.
  induct_trc_step Htrc.
  - invc Heqs'. constructor.
  - destruct y as [v1 c1].
    eapply cmd_xform_arith_equiv_step in H; eauto.
    econstructor; eauto.
Qed.

End Imp.
