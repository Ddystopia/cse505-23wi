(* include libraries and notations *)
Require Import Arith Lia List String.
Import ListNotations.
Open Scope string.

Set Implicit Arguments.

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

(*
If you could use a refresher on any of these definitions, please check out
the code from Week04 where they're discussed in detail:
    https://gitlab.cs.washington.edu/cse505-23wi/cse505-23wi/-/blob/main/week04/Week04.v
*)

(* Copied from Week04.v *)
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

(* Syntax of Imp. *)
Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| If (e : arith) (then_ else_ : cmd) (* new this week (but nothing fundamental) *)
| While (e : arith) (body : cmd). (* new this week (and fundamentally different!) *)

Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";;" := Sequence (at level 76). (* ;; instead of ; because it interferes
                                         with record syntax *)
Notation "'when' e 'then' then_ 'else' else_ 'done'" :=
  (If e%arith then_ else_) (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" :=
  (While e%arith body) (at level 75).

(* Translate our long horizontal lines to an inductive definition. *)
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
      (* --------------------------- *)
      step (v, While e body) (v, Sequence body (While e body))
| StepWhileFalse :
    forall v e body,
      eval_arith e v = 0 ->
      step (v, While e body) (v, Skip).

Definition counter :=
  "x" <- 5;;
  while 1 loop
    "x" <- "x" + 1
  done.

Example counter_steps_10_times :
  exists v,
    trc step ([], counter) (v, while 1 loop
                                  "x" <- "x" + 1
                               done) /\
    lookup "x" v = Some 15.
Proof.
Admitted.

(* Here's our old friend the factorial program. *)
Definition factorial : cmd :=
  "n" <- "input";;
  "acc" <- 1;;
  while "n" loop
    "acc" <- "acc" * "n";;
    "n" <- "n" - 1
  done;;
  "output" <- "acc".

Example factorial_4 :
  forall v1,
    lookup "input" v1 = Some 4 ->
    exists v2,
      trc step (v1, factorial) (v2, Skip) /\
      lookup "output" v2 = Some 24.
Proof.
  intros v1 Hv1.
  eexists.
  split. 
  - unfold factorial.
    Print trc.
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
Restart.





  intros v1 H.
  eexists.
  split.
  - eapply trc_front.
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

Definition cmd_init (v : valuation) (c : cmd) (s : valuation * cmd) : Prop :=
  s = (v, c).

Definition cmd_to_trsys (v : valuation) (c : cmd) : trsys (valuation * cmd) :=
  {| Init := cmd_init v c
   ; Step := step
   |}.


Definition counter_sys : trsys (valuation * cmd) :=
  cmd_to_trsys [] counter.

Definition counter_ge_5_attempt (s : valuation * cmd) :=
  let (v, c) := s in
  exists x,
    lookup "x" v = Some x /\
    x >= 5.

Theorem counter_ge_5_attempt_invariant :
  is_invariant counter_sys counter_ge_5_attempt.
Proof.
  invariant_induction_boilerplate.
  (* Uh oh, this just isn't true initially! 
     x is not mapped to anything yet. *)
  - 

Abort.

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
  - left. reflexivity. (* auto. *)
  - destruct s1 as [v1 c1], s2 as [v2 c2].
     destruct IH as [IH|IH].
    + unfold counter in *.
      subst c1.
      inversion Hstep; subst. clear Hstep.
      inversion H0; subst. clear H0.
      simpl. 
      (* right.
      eexists.
      split.
      reflexivity.
      lia. *)
      eauto.
    +
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
       done).



Theorem counter_programs_invariant :
  is_invariant counter_sys counter_programs.
Proof.
  invariant_induction_boilerplate.
  - auto.
  - destruct s1 as [v1 c1], s2 as [v2 c2].
    intuition; subst; inversion Hstep; subst; clear Hstep; auto.
    + inversion H0; subst; clear H0. auto.
    + inversion H0; subst; clear H0.
    + inversion H0; subst; clear H0. auto.
Qed.

Definition counter_valuation_x_ge_5 (v : valuation) :=
  exists x,
    lookup "x" v = Some x /\
    x >= 5.

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
        done) /\ counter_valuation_x_ge_5 v).

Lemma counter_programs_x_ge_5_invariant :
  is_invariant counter_sys counter_programs_x_ge_5.
Proof.
  invariant_induction_boilerplate.
  - auto.
  - destruct s1 as [v1 c1], s2 as [v2 c2].
    unfold counter_valuation_x_ge_5 in *.
    intuition; subst; inversion Hstep; subst; clear Hstep; auto.
    + inversion H0; subst; clear H0. cbn.  eauto 10.
    (* right. left. split. reflexivity. eauto. *)
    + inversion H0; subst; clear H0.
    + destruct H1 as [x [Hlook Hx]]. cbn in *. discriminate.
    + inversion H0; subst; clear H0.
      destruct H1 as [x [Hlook Hx]]. cbn. rewrite Hlook. right. left.
      split; auto. eexists. split; auto. lia.
Qed.

Theorem counter_ge_5_invariant :
  is_invariant counter_sys counter_ge_5.
Proof.
  unfold counter_ge_5.
  apply invariant_implies with (P := counter_programs_x_ge_5).
  - apply counter_programs_x_ge_5_invariant.
  - unfold counter_programs_x_ge_5, counter_ge_5.
    intros [v c] Hinv.
    intuition.
Qed.

Definition factorial_sys (input : nat) : trsys (valuation * cmd) :=
  cmd_to_trsys [("input", input)] factorial.

Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => fact n' * S n'
  end.

Definition factorial_safe (input : nat) (s : valuation * cmd) : Prop :=
  let (v, c) := s in
  c = Skip ->
  lookup "output" v = Some (fact input).

Theorem factorial_safe_invariant :
  forall input,
    is_invariant (factorial_sys input) (factorial_safe input).
Proof.
Abort.

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

Definition factorial_loop_invariant input v :=
  exists n acc,
    lookup "n" v = Some n /\
    lookup "acc" v = Some acc /\
    fact n * acc = fact input.

Definition factorial_body_invariant input v :=
  exists n acc,
    lookup "n" v = Some (S n) /\
    lookup "acc" v = Some acc /\
    fact (S n) * acc = fact input.

Definition factorial_body_invariant_after_step input v :=
  exists n acc,
    lookup "n" v = Some (S n) /\
    lookup "acc" v = Some acc /\
    fact n * acc = fact input.

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

Ltac invc H := inversion H; subst; clear H.

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

Ltac invert_one_step :=
  match goal with
  | [ H : step _ _ |- _ ] => invc H
  end.

Ltac invert_steps :=
  repeat invert_one_step.

Ltac magic_select_case :=
  repeat match goal with
  | [ |- _ \/ _ ] => (left; split; [reflexivity|]) || right
  | _ => try split; [reflexivity|]
  end.

Ltac break_up_hyps :=
  repeat match goal with
  | [ H : exists _, _ |- _ ] => destruct H
  | [ H : _ /\ _ |- _ ] => destruct H
  end.

Ltac find_rewrites :=
  repeat match goal with
  | [ H : _ = _ |- _ ] => rewrite H in *
  end.

Lemma factorial_inv_invariant_again :
  forall input,
    is_invariant (factorial_sys input) (factorial_inv input).
Proof.
  invariant_induction_boilerplate.
  - auto.
  - destruct s1 as [v1 c1], s2 as [v2 c2].
    fold (factorial_inv input (v2, c2)).
    intuition; subst; invert_steps;
    unfold factorial_inv;
    unfold factorial_loop_invariant, factorial_body_invariant in *;
    unfold factorial_body_invariant_after_step in *;
    magic_select_case;
    break_up_hyps;
    cbn in *;
    find_rewrites;
    eauto 20.
    + eexists. eexists.
      split; eauto. split; eauto. lia.
    + destruct x; [congruence|]. (* note: destruct before exists *)
      eauto.
    + subst.
      cbn in *. rewrite <- H1. f_equal. lia.
    + eexists. eexists. split; eauto. split; eauto.
      rewrite <- H1. cbn. lia.
    + eexists. eexists. split; eauto. split; eauto.
      cbn. rewrite <- H1. f_equal. f_equal. lia.
Qed.

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

Lemma decompose_sequence_execution :
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

Lemma decompose_while_execution :
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
