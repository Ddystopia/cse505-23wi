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
This week we will develop a more structured way to do proofs about the execution
of Imp programs, called Hoare logic, after Tony Hoare.

If we pause execution of an Imp program at any point, we an look at the current
state of memory (the valuation). Just like with enumeration-style invariants
last week, we want to state facts about the valuation at different program
points. In Coq, we can think of this as a "predicate on valuations", or in other
words, a function that takes a valuation and returns a Prop.
*)
Definition assertion := (valuation -> Prop).
(* When does one assertion imply another? *)
Definition assert_implies (P Q : assertion) : Prop :=
  (forall v, P v -> Q v).

(* We will also start using more automation this week. More on Hints later. *)
Local Hint Unfold assert_implies : core.

(*
Our first order of business is to add two new features to Imp.
- Assert e, which "fails" if e evaluates to false
- Panic, which represents a failed program
*)
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

(* Three new kinds of steps: *)

(* If the assertion is true, we step to Skip. *)
| StepAssertionTrue :
  forall v e,
    eval_arith e v <> 0 ->
    step (v, Assert e) (v, Skip)

(* If the assertion is false, we step to Panic. *)
| StepAssertionFalse :
  forall v e,
    eval_arith e v = 0 ->
    step (v, Assert e) (v, Panic)

(* If the first part of a sequence has failed, then the whole sequence has
   failed. *)
| StepSeqPanic :
  forall v c2,
    step (v, Sequence Panic c2) (v, Panic).
Local Hint Constructors step : core.
(* This hint tells auto/eauto about all the constructors of step. *)

(* Our old friend *)
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

(* We will use some fancy notation for "step" and "step star". *)
Notation "e '-->' e'" := (step e e') (at level 75).
Notation "e '-->*' e'" := (trc step e e') (at level 75).

(* Our proof system closely follows the long horizontal lines. (See slides.) *)
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
  (*
    assert_implies P (fun v => eval_arith e v <> 0) -> 
    hoare_triple P (Assert e) P
*)

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
(* Another way to reason about assignment *)
(*
| ht_assign_forward :
  forall P x e,
  hoare_triple
    P
    (Assign x e)
    (fun v => exists v', P v' /\ v = (x, eval_arith e v') :: v')
*)
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

(* Often we only want to adjust the precondition. *)
Lemma ht_consequence_left :
  forall P P' Q c,
    hoare_triple P' c Q ->
    assert_implies P P' ->
    hoare_triple P c Q.
Proof.
  eauto.
Qed.

(* Or the postcondition. *)
Lemma ht_consequence_right :
  forall P Q Q' c,
    hoare_triple P c Q' ->
    assert_implies Q' Q ->
    hoare_triple P c Q.
Proof.
  eauto.
Qed.

Definition two_counters :=
  "x" <- 0;;
  "y" <- "input";;
  while "y" loop
    "x" <- "x" + 1;;
    "y" <- "y" - 1
  done.

(* Our first Hoare triple! It says that after the program terminates,
   x = input. *)
Theorem two_counters_correct :
  hoare_triple
    (fun _ => True)
    two_counters
    (fun v => eval_arith "x" v = eval_arith "input" v).
Proof.
  unfold two_counters.
  (* Follow the structure of the program! *)
  eapply ht_sequence.
  eapply ht_sequence.
  (* We want to apply the ht_assign rule, but it requires a particular shape of
     precondition. *)
  Fail apply ht_assign.
  (* So we can use ht_consequence_left first to prove an implication later. *)
  eapply ht_consequence_left; [| shelve].
  (* "shelve" puts a goal "on the shelf". It still has to be solved later before
     Qed, but it allows us to work on all the hoare_triple goals first. *)
  apply ht_assign.
  apply ht_assign.
  (* Now the interesting part: the loop invariant. The ht_while rule requires a
     specific postcondition, so we need to use ht_consequence_right first. *)
  eapply ht_consequence_right; [|shelve]. (* Again, shelve implication goal. *)
  (* We're ready for ht_while. *)
  apply ht_while with (I := fun v => eval_arith ("x" + "y") v = eval_arith "input" v).
  (* Next we prove the body preserves the invariant. *)
  eapply ht_sequence.
  (* Another round of ht_consequence_left before an assignment. *)
  eapply ht_consequence_left; [|shelve].
  apply ht_assign.
  apply ht_assign.
  (* We've finished applying the Hoare rules. It's time to deal with all the
     implication side conditions. *)
  Unshelve. (* Take all shelved goals off the shelf. *)
  - unfold assert_implies.
    intros.
    simpl.
    auto.
  - unfold assert_implies.
    intros.
    simpl in *.
    lia.
  - unfold assert_implies.
    intros.
    simpl in *.
    lia.
  (* Or we could do all three at once
  all: unfold assert_implies; intros; simpl in *; auto; lia.
  *)
Qed.

(*
We can see that the proof had a very repetitive structure. At each step we
applied the Hoare rule corresponding to the program syntax. Sometimes, the Hoare
rule required a specific shape of pre- or postcondition, so we had to use some
kind of consequence first. After applying all the rules based on the syntax, we
are left with some number of implication goals, which we can prove just like
normal Coq goals, often eventually using lia.

Let's write some automation to make these proofs easier.
*)

(* First, some standard 505 tactics. *)
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

(*
This week we are also using hints more. These hints tell auto to call
discriminate or congruence when trying to prove False or an inequality.
*)
Local Hint Extern 4 (~(_ = _)) => discriminate : core.
Local Hint Extern 4 (False) => discriminate : core.
Local Hint Extern 4 (False) => congruence : core.

(*
Because the assignment rule works backward, it's often best to solve most
Hoare triples backward. Here is a rephrasing of the ht_sequence rule that just
gives the subgoals in the opposite order.
*)
Lemma ht_sequence_reverse :
  forall (P Q R : assertion) c1 c2,
    hoare_triple R c2 Q ->
    hoare_triple P c1 R ->
    hoare_triple P (c1 ;; c2) Q.
Proof.
  intros.
  eapply ht_sequence; eauto.
Qed.

(*
Here is a tactics that just applies whatever Hoare rule makes sense based on the
syntax of the program. 505 motto in action!

The tactic tries to be a little bit smart about when to apply consequence. So it
often tries to apply the Hoare rule *without* applying consequence and then only
if that fails, it applies consequence and *then* applies the relevant rule.

Note that this tactic does not handle while loops. That's on purpose, because
for while loops, the loop invariant is almost always different than what would
be automatically computed as the pre- or postcondition of the loop.
*)
Ltac auto_triple :=
  intros;
  repeat match goal with
  | [ |- hoare_triple _ (_ ;; _) _ ] => eapply ht_sequence_reverse
  | [ |- hoare_triple _ (_ <- _) _ ] =>
    apply ht_assign || (eapply ht_consequence_left; [apply ht_assign|])
  | [ |- hoare_triple _ (If _ _ _) _ ] => apply ht_if
  | [ |- hoare_triple _ Skip _ ] =>
    apply ht_skip || (eapply ht_consequence_left; [apply ht_skip|])
  | [ |- hoare_triple _ (Assert _) _ ] =>
    apply ht_assert_true || (eapply ht_consequence_left; [apply ht_assert_true|])
  | [ |- hoare_triple _ ?x _ ] => unfold x
  end.

(*
Here is a tactic for handling while loops. You pass it a loop invariant of the
form (fun v => ...). It tries to use the least amount of consequence it can get
away with before applying the ht_while rule. Then it calls auto_triple for you
to try to prove the body of the loop.
*)
Ltac fancy_ht_while e :=
  (let a := (apply ht_while with (I := e)) in
   (a ||
   (eapply ht_consequence_right; [a|]) ||
   (eapply ht_consequence_left; [a|]) ||
   (eapply ht_consequence; [a| |])));
  auto_triple.

Ltac find_rewrites :=
  repeat match goal with
  | [ H : _ = _ |- _ ] => rewrite H in *
  end.

(*
This is a bit of a weird tactic to cleanup goals based on the fact that our
interpreter likes to make lots of calls to lookup. Usually our goals are true
if you just treat the entire "match lookup..." expression as a variable.
*)
Ltac cleanup_vars :=
  repeat match goal with
  | [ H : context [ match lookup ?x ?v with _ => _ end ] |- _ ] =>
    let E := fresh "E" in
    remember (match lookup x v with Some _ => _ | None => _ end) eqn:E; clear E
  end.

(* A tactic for implication subgoals at the end of Hoare triple proofs. *)
Ltac bash_assert_implies :=
  unfold assert_implies; intros; simpl in *; break_up_hyps; find_rewrites; simpl in *;
  cleanup_vars; auto; try lia.

(* Let's do the same proof again but with more automation. *)
Theorem two_counters_correct_again :
  hoare_triple
    (fun _ => True)
    two_counters
    (fun v => eval_arith "x" v = eval_arith "input" v).
Proof.
  auto_triple. (* Handles the assignments up to the while loop. *)
  (* Now we have to state our loop invariant. *)
  fancy_ht_while (fun v => eval_arith ("x" + "y") v = eval_arith "input" v).
  (* fancy_ht_while calls auto_triple for us on the body of the loop. All that's
     left is to handle implication subgoals. *)
  all: bash_assert_implies.
Qed.

(*
Let's do another example. Proving factorial agrees with a Coq implementation.
*)
Definition factorial : cmd :=
  "n" <- "input";;
  "acc" <- 1;;
  while "n" loop
    "acc" <- "acc" * "n";;
    "n" <- "n" - 1
  done;;
  "output" <- "acc".

Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => fact n' * S n'
  end.

(*
This time our specification uses a so-called "logical variable", which is a Coq
variable, like "n" below, that is used to connect the precondition to the
postcondition. (This is actually a shortcoming of our two_counters spec above,
since the program could have modified "input" in a way that made our spec not
mean what we thought it meant.)
*)
Theorem factorial_correct :
  forall n,
    hoare_triple
      (fun v => eval_arith "input" v = n) (* if the program is given input n *)
      factorial
      (fun v => eval_arith "output" v = fact n). (* it computes output fact n *)
Proof.
  auto_triple. (* handles everything but the loop *)
  fancy_ht_while (fun v => (* here's our loop invariant *)
    fact n = fact (eval_arith "n" v) * eval_arith "acc" v).
  (* All that's left is implications. *)
  all: bash_assert_implies.
  (* One implication remains even after the automation. We need to show that
     fact "unrolls" correctly. *)
  destruct y; [congruence|]. (* Since y <> 0, we can just handle the S case. *)
  simpl. (* Now that its argument is S, fact unrolls. *)
  (* Just some arithmetic remains. *)
  rewrite Nat.sub_0_r. lia.
Qed.

(* One more example! How about a nonterminating one? *)

Definition counter :=
  "x" <- 5;;
  while 1 loop
    assert "x" - 4;;  (* Check out this assert! *)
    "x" <- "x" + 1
  done.

(*
Since the program doesn't terminate, we can't just use a postcondition to state
our specification. Instead, we used an assert, that "x" - 4 is nonzero. Since
subtraction returns zero whenever x <= 4, this says x > 4, or in other words,
x >= 5, which is what we wanted to say.
*)

(*
Let's prove a quick lemma double checking that our assertion encodes our
intuitive specification.
*)
Lemma counter_assertion_says_what_we_think :
  forall v,
    eval_arith ("x" - 4) v <> 0 <-> eval_arith "x" v >= 5.
Proof.
  intros.
  simpl.
  lia.
Qed.

(*
 Now we'll just show the most basic Hoare triple, but that's enough to guarantee
 the assertion never fails!
 *)
Theorem counter_correct :
  hoare_triple
    (fun _ => True)
    counter
    (fun _ => True).
Proof.
  (* The proof follows the same recipe as before. The only manual step is coming
     up with the loop invariant. In this case, it's pretty easy: it's the same
     as the assert itself. *)
  auto_triple.
  fancy_ht_while (fun v => eval_arith ("x" - 4) v <> 0).
  all: bash_assert_implies.
Qed.

(* Here's another version that also proves the program doesn't terminate. *)
Theorem counter_correct_nonterminating :
  hoare_triple
    (fun _ => True)
    counter
    (fun _ => False).
Proof.
  auto_triple.
  fancy_ht_while (fun v => eval_arith ("x" - 4) v <> 0).
  all: bash_assert_implies.
Qed.

(* Couple of other small examples, making sure we didn't mess up assertions. *)
Example asserts_can_panic :
  forall v,
    (v, assert 0) -->* (v, Panic).
Proof.
  eauto.
Qed.

Example asserts_can_panic_in_big_programs :
  forall v,
    (v, Skip ;; While 1 Panic ;; Skip) -->* (v, Panic).
Proof.
  eauto 10.
Qed.

(*
What does it mean for a Hoare triple to be correct?
Here is our definition.
*)
Definition sound_triple (P : assertion) c (Q : assertion) : Prop :=
  forall v v' c',
    P v ->
    (v, c) -->* (v', c') ->
    c' <> Panic /\ (c' = Skip -> Q v').
(*
In words: from any valuation satisfying the precondition,
    1) execution is guaranteed never to panic
    2) if execution terminates, then the postcondition holds
*)

(* We are going to prove this theorem! *)
Theorem hoare_ok :
  forall P c Q,
    hoare_triple P c Q ->
    sound_triple P c Q.
Proof.
  (* We will proceed by induction on the derivation of the Hoare triple.
     Then, in each case, we will have to prove that particular rule is sound.
     The most interesting cases are the inductive ones, as usual.
     Our general strategy will be to "deconstruct" the given execution.
  *)
Abort.

(* Skip can't step anywhere. *)
Lemma deconstruct_skip_execution :
  forall v v' c,
    (v, Skip) -->* (v', c) ->
    v' = v /\ c = Skip.
Proof.
  (* bash_execution is an automated tactic to do repeated inversion on steps.
     Be careful because it can sometimes run forever if the program is unknown.
   *)
  bash_execution.
Qed.

(* The Hoare rule for Skip is sound. *)
Lemma hoare_skip_ok :
  forall P,
    sound_triple P Skip P.
Proof.
  intros P v v' c' HP Hstep.
  (* Deconstruct the given execution. *)
  apply deconstruct_skip_execution in Hstep.
  (* Now we know we haven't stepped anywhere, so the result follows. *)
  intuition. subst. auto.
Qed.

(* Panic also can't step anywhere. *)
Lemma deconstruct_panicked_execution :
  forall v v' c,
    (v, Panic) -->* (v', c) ->
    v' = v /\
    c = Panic.
Proof.
  bash_execution.
Qed.

(* Assert e can step-star in three ways:
   - to itself
   - to Skip, if e is non-zero
   - to Panic, if e is zero
   In all three cases, the valuation is unchanged.
*)
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

(* The Hoare rule for Assert is sound. *)
Lemma hoare_assertion_ok :
  forall P e,
    sound_triple (fun v => P v /\ eval_arith e v <> 0) (Assert e) P.
Proof.
  intros P e v v' c' [HP Heval] Hstep.
  (* Follow the pattern: first deconstruct the execution. *)
  apply deconstruct_assert_execution in Hstep.
  (* Then we need to handle all three possibilities. The possibility of Panic
     is ruled out because our Hoare rule says that e is nonzero. *)
  intuition; subst; auto.
Qed.

(* Assignment (x <- e) can step in two ways
   - to itself, leaving the valuation unchanged
   - to Skip, updating the valuation so that x maps to the evaluation of e
*)
Lemma deconstruct_assignment_execution :
  forall v v' x e c,
    (v, x <- e) -->* (v', c) ->
    (v' = v /\ c = (x <- e)) \/
    (v' = (x, eval_arith e v) :: v /\ c = Skip).
Proof.
  bash_execution.
Qed.

(* The Hoare rule for assignment is sound. *)
Lemma hoare_assignment_ok :
  forall P x e,
    sound_triple (fun v => P ((x, eval_arith e v) :: v)) (x <- e) P.
Proof.
  intros P x e v v' c' Hv Hstep.
  (* Follow the pattern: first deconstruct the execution. *)
  apply deconstruct_assignment_execution in Hstep.
  (* Now handle the two possibilities. *)
  intuition; subst; auto.
  (* One leftover goal, asking if P is true when (x <- e) doesn't step. But
     that's easy, because we only have to prove the postcondition if we reach
     Skip, and we haven't yet. *)
  congruence.
Qed.

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

(* The first real challenge is the Sequence construct. How can c1 ;; c2 step?
   - could be part way through executing c1
   - could be done with c1 and part way through executing c2
   - c1 could have Panicked
*)
Lemma deconstruct_sequence_execution :
  forall v v' c1 c2 c',
    (v, c1;; c2) -->* (v', c') ->
    exists v1' c1',
      (v, c1) -->* (v1', c1') /\
      ((c' = (c1';; c2) /\ v' = v1') \/
       (c1' = Skip /\ (v1', c2) -->* (v', c')) \/
       (c' = Panic /\ c1' = Panic /\ v1' = v')).
Proof.
  intros v v' c1 c2 c' Hstep.
  (* We want to proceed by induction on the derivation of trc. *)
  induction Hstep.
  - (* wait... what is x??? *)
  (* Unfortunately, Coq's induction tactic is not smart enough to do the right
     thing here. The general rule is that when you do induction on a derivation,
     all the "subexpressions of the type" you're inducting on must be variables.
     We can transform our goal into this form using the "remember" tactic to
     introduce new variables to stand for complex subexpressions. *)
  Restart.
  intros v v' c1 c2 c' Hstep.
  (* We want to induct on Hstep, but it's type contains complex subexpressions
     involving pairs and sequences.

     Here comes the "remember trick". *)
  remember (v, c1;;c2) as s.
  remember (v', c') as s'.
  (* Now before calling induction, we want to move *everything* else back into
     the goal. This let's us undo the problem of "intros too much". The "revert"
     tactic is the opposite of "intros": it moves something back into the goal.
     Be careful of the dependency order in the arguments to revert. *)
  revert v c1 c2 v' c' Heqs Heqs'.
  (* Finally, we can do induction. *)
  induction Hstep; intros v c1 c2 v' c' ? ?; subst.
  - invc Heqs'. 
    exists v', c1.
    split.
    + apply trc_refl.
    + left. split; reflexivity.
  (*eauto 10.*)
  - invc H.
    + (* c1 stepped *)
      specialize (IHHstep v'0 c1' c2 v' c' eq_refl eq_refl).
      break_up_hyps.
      eauto.
    + (* c1 was Skip and we got rid of it. *)
      eauto 10.
    + (* c1 was Panic and we propagated the error *)
      apply deconstruct_panicked_execution in Hstep.
      break_up_hyps; subst; eauto 10.
  Restart.
  intros v v' c1 c2 c' Hstep.
  prepare_induct_trc_step Hstep.
  revert c1 c2.
  induction Hstep; intros; subst.
  - invc Heqs'. eauto 10.
  - invc H; eauto 10.
    + specialize (IHHstep _ _ _ _ _ eq_refl eq_refl).
      break_up_hyps.
      eauto.
    + apply deconstruct_panicked_execution in Hstep.
      break_up_hyps; subst; eauto 10.
Qed.

(* The Hoare rule for sequence is sound. *)
Lemma hoare_sequence_ok :
  forall P Q R c1 c2,
    sound_triple P c1 R ->
    sound_triple R c2 Q ->
    sound_triple P (c1;; c2) Q.
Proof.
  intros P Q R c1 c2 IHc1 IHc2 v v' c' HP Hstep.
  (* Take apart the execution, then handle each case. *)
  apply deconstruct_sequence_execution in Hstep.
  break_up_hyps_or; subst.
  - split; congruence. (* Still in c1; nothing to show. *)
  - eapply IHc2; eauto. (* c1 terminated in Skip, use both IHs. *)
    eapply IHc1; eauto.
  - apply IHc1 in H; auto. (* Show that c1 can't Panic. *)
    intuition.
Qed.

(* The Hoare rule for consequence is sound. *)
Lemma hoare_consequence_ok :
  forall (P P' Q Q' : assertion) c,
    assert_implies P P' ->
    assert_implies Q' Q ->
    sound_triple P' c Q' ->
    sound_triple P c Q.
Proof.
  intros P P' Q Q' c HPP' HQQ' IH v v' c' HP Hstep.
  (* No execution to deconstruct here, just use the IH and implication. *)
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

(*
Here's an alternative definition of trc that adds steps "on the right". We are
going to prove it equivalent to trc and then use it to get a "rightward"
induction principle for trc.
*)
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

(* Here is a "custom induction principle" for trc. *)
Lemma trc_reverse_ind :
  forall A (R : A -> A -> Prop) (P : A -> A -> Prop),
    (forall x, P x x) ->
    (forall x y z, trc R x y -> R y z -> P x y -> P x z) ->
    forall x y,
      trc R x y ->
      P x y.
Proof.
  (* - convert to trc_backward
     - induct on that
     - in inductive case, convert back to trc to use our hypothesis
  *)
  intros A R P Hbase Hind x y H.
  apply trc_implies_trc_backward in H.
  induction H.
  - apply Hbase.
  - apply Hind with (y := y); auto.
    apply trc_backward_implies_trc.
    auto.
Qed.

(*
The key idea for the soundness proof of ht_while. It says that one iteration of
the loop body of "While e c" starts in v1 and terminates in v2. Since the loop
body is going to execute, that also means e is truthy.
*)
Definition loop_runs_to (e : arith) (c : cmd) (v1 v2 : valuation) :=
  trc step (v1, c) (v2, Skip) /\ eval_arith e v1 <> 0.
Local Hint Unfold loop_runs_to : core.

(* Some fancy notation for trc (loop_runs_to...) *)
Notation "v '-[' e ',' s ']>*' v'" := (trc (loop_runs_to e s) v v') (at level 75).

(* Taking apart the execution of a while loop. If we get to (v', c'), then we
   know that there is a "most recent" top-of-loop valuation v1 such that
   - v takes some number of complete loop iterations to v1, and
   - one of these four things is true:
     - we exit the loop at v1, so v' = v1 and c' = Skip
     - we're still at the top of the loop, so v' = v1 and c' = While e c
     - we started executing the loop body from v1 (so e is truthy in v1), but c
       Panicked at some point, so c' = Panic
     - we started executing the loop body from v1 (so e is truthy in v1), but
       we're not done yet *)
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
  (* We prove this by "rightward induction" on trc. The lemma is not inductive
     under the normal induction principle; it would require a different phrasing
     to be inductive. *)
  induction Htrc using trc_reverse_ind; intros e c v v' c' ? ?; subst.
  - invc Heqs'. eauto 10.
  - destruct y as [v2 c2].
    specialize (IHHtrc _ _ _ _ _ eq_refl eq_refl).
    break_up_hyps_or; subst; try invert_one_step; eauto 10.
Qed.

(*
This lemma says that if you know one iteration of the loop preserves the
invariant, then any number of loop iterations preserves the invariant.
*)
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

(*
This lemma is just a rephrasing of the previous lemma in terms of sound_triple.
*)
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

(* Finally, the Hoare rule for while is sound. *)
Lemma hoare_while_loop_ok :
  forall (I : assertion) e c,
    sound_triple (fun v => I v /\ eval_arith e v <> 0) c I ->
    sound_triple I (While e c) (fun v => I v /\ eval_arith e v = 0).
Proof.
  intros I e c IH v v' c' HI Hstep.
  (* step 1: deconstruct the execution *)
  apply deconstruct_while_execution in Hstep.
  (* step 2: handle each case, using the IH as needed *)
  break_up_hyps_or; subst; split; intros; try congruence; try split; auto.
  - eapply sound_triple_preserves_invariant; eauto.
  - eapply IH; eauto.
    split; auto.
    eapply sound_triple_preserves_invariant; eauto.
Qed.

(*
Our crowning achievement for this week. Any Hoare triple proved with our rules
is actually true about the operational semantics!
*)
Theorem hoare_ok :
  forall P c Q,
    hoare_triple P c Q ->
    sound_triple P c Q.
Proof.
  intros P c Q HHT.
  induction HHT.
  - apply hoare_skip_ok.
  - eapply hoare_sequence_ok; eauto.
  - apply hoare_assertion_ok.
  - eapply hoare_consequence_ok; eauto.
  - apply hoare_assignment_ok.
  - apply hoare_conditional_ok; auto.
  - apply hoare_while_loop_ok; auto.
Qed.

(* One of the things soundness gives us is:
       well-specified programs don't panic
 *)
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

(* In our semantics, the only programs that can't step are Skip and Panic. *)
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

(*
Since well-specified programs don't panic, they either terminate in Skip, or
they run forever.
*)
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

(* Another easy consequence of soundness: the counter never panics. *)
Corollary counter_never_panics :
  forall v v' c',
    (v, counter) -->* (v', c') ->
    c' <> Panic.
Proof.
  intros v v' c' Hstep.
  eapply hoare_triples_are_safe.
  apply counter_correct.
  eassumption.
  simpl. auto.
Qed.