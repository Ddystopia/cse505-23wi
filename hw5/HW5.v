(*

  _   _    ___    __  __   _____  __        __   ___    ____    _  __    ____
 | | | |  / _ \  |  \/  | | ____| \ \      / /  / _ \  |  _ \  | |/ /   | ___|
 | |_| | | | | | | |\/| | |  _|    \ \ /\ / /  | | | | | |_) | | ' /    |___ \
 |  _  | | |_| | | |  | | | |___    \ V  V /   | |_| | |  _ <  | . \     ___) |
 |_| |_|  \___/  |_|  |_| |_____|    \_/\_/     \___/  |_| \_\ |_|\_\   |____/


Welcome back! This homework covers (untyped) lambda calculus and simply typed
lambda calculus. System F will be covered in homework 6.

There are 27 problems worth a total of 120 core points and
30 challenge points.

*)


Require Import Arith Lia List String.
Require Import ListSet.
Open Scope string.
Import ListNotations.

Set Implicit Arguments.

(*
 * PROBLEM 1 [0 points, ~0 tactics]
 *
 * Fake problem to make Gradescope numbers match problem numbers.
 *)
(* Nothing to do here. *)

(* Generic copied stuff *)
Definition eq_dec (A : Type) :=
  forall (x : A),
    forall (y : A),
      {x = y} + {x <> y}.

Notation var := string.
Definition var_eq : eq_dec var := string_dec.

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
  forall A (R : A -> A -> Prop) x y z,
    trc R x y ->
    trc R y z ->
    trc R x z.
Proof.
  intros A R x y z Hxy Hyz.
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

Ltac invc H := inversion H; subst; clear H.
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
Ltac easy_specialize :=
  repeat match goal with
  | [ H : (?x = ?x -> _) |- _ ] => specialize (H eq_refl)
  end.
(* End of generic copied stuff *)

(*
               ____                  _     _                     _
              / ___|    ___    ___  | |_  (_)   ___    _ __     / |
              \___ \   / _ \  / __| | __| | |  / _ \  | '_ \    | |
               ___) | |  __/ | (__  | |_  | | | (_) | | | | |   | |
              |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |_|

                       SECTION 1 : Untyped Lambda Calculus
*)
Module UTLC.

(* Copied stuff from Week07.v *)
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

Definition Id := \"x", "x".

Definition T := \"x", \"y", "x".
Definition F := \"x", \"y", "y".

Definition not b :=
  b @ F @ T.

Definition and b1 b2 :=
  b1 @ b2 @ F.

Definition or b1 b2 :=
  b1 @ T @ b2.

Definition church_bool (b : bool) : expr :=
  if b then T else F.

Definition evals_to (e v : expr) : Prop :=
  e -->* v /\ value v.

Ltac step_utlc :=
  repeat match goal with
  | [ |- (_ @ _) @ _ --> _ ] => apply step_app_left
  | [ |- (\_, _) @ (_ @ _) --> _ ] => apply step_app_right; [|solve [auto]]
  | [ |- (\_, _) @ (\_, _) --> _ ] => apply step_beta; [solve [auto]]
  | [ |- (\_, _) @ ?x --> _ ] => unfold x
  | [ |- ?x @ _ --> _ ] => unfold x
  end.

Ltac eval_utlc :=
  repeat (cbn; match goal with
  | [ |- _ -->* _ ] =>
    apply trc_refl || (eapply trc_front; [solve[step_utlc]|])
  end).

Lemma step_star_app_left :
  forall e1 e1' e2,
    e1 -->* e1' ->
    e1 @ e2 -->* e1' @ e2.
Proof.
  intros e1 e1' e2 Hstep.
  induction Hstep; eauto.
Qed.

Lemma step_star_app_right :
  forall v1 e2 e2',
    e2 -->* e2' ->
    value v1 ->
    v1 @ e2 -->* v1 @ e2'.
Proof.
  intros v1 e2 e2' Hstep HV.
  induction Hstep; eauto.
Qed.

Fixpoint is_free_var (e : expr) (y : var) : Prop :=
  match e with
  | Var x => x = y
  | Abs x e => x <> y /\ is_free_var e y
  | App e1 e2 => is_free_var e1 y \/ is_free_var e2 y
  end.

Definition closed (e : expr) : Prop :=
  forall x,
    ~ is_free_var e x.

Lemma closed_app_invert :
  forall e1 e2,
    closed (e1 @ e2) ->
    closed e1 /\ closed e2.
Proof.
  firstorder.
Qed.

Definition Zero := (\"s", \"z", "z").
Definition Succ := (\"n", \"s", \"z", "s" @ (("n" @ "s") @ "z")).
Definition One := Succ @ Zero.
Definition Add := \"n1", \"n2", "n2" @ Succ @ "n1".
Definition Mult := \"n1", \"n2", "n2" @ (Add @ "n1") @ Zero.
Definition IsZero := \"n", "n" @ (\"_", F) @ T.
Definition Pair := \"fst", \"snd", \"f", "f" @ "fst" @ "snd".
Definition Fst := \"pi", "pi" @ (\"x", \"y", "x").
Definition Snd := \"pi", "pi" @ (\"x", \"y", "y").
Definition PairZero := Pair @ Zero @ Zero.
Definition PairSucc := \"pi", Pair @ (Succ @ (Fst @ "pi")) @ (Fst @ "pi").
Definition Pred := \"n", Snd @ ("n" @ PairSucc @ PairZero).
Definition Fix :=
  (\"f",
    (\"x", "f" @ (\"y", "x" @ "x" @ "y")) @
    (\"x", "f" @ (\"y", "x" @ "x" @ "y"))).

Fixpoint take_one_step (e : expr) : expr :=
  match e with
  | Var _ => e
  | Abs _ _ => e
  | App (Abs x e) ((Abs _ _) as v) => subst x v e
  | App (Abs x e) e2 => App (Abs x e) (take_one_step e2)
  | App e1 e2 => App (take_one_step e1) e2
  end.

Lemma take_one_step_step :
  forall e,
    closed e ->
    step e (take_one_step e) \/ (value e /\ take_one_step e = e).
Proof.
  induction e; simpl; intros; auto.
  - specialize (H s). simpl in *. congruence.
  - apply closed_app_invert in H. break_up_hyps.
    destruct e1.
    + specialize (H s). congruence.
    + destruct e2.
      * specialize (H0 s0). congruence.
      * auto.
      * apply IHe2 in H0. clear IHe1.
        intuition. invc H0.
    + apply IHe1 in H. clear IHe2.
      intuition. invc H.
Qed.

Fixpoint run_for_n_steps (n : nat) (e : expr) : expr :=
  match n with
  | 0 => e
  | S m => run_for_n_steps m (take_one_step e)
  end.

Lemma free_vars_subst :
  forall from to e x,
    closed to ->
    is_free_var (subst from to e) x <->
    is_free_var e x /\ x <> from.
Proof.
  intros from to e x Hto.
  induction e; simpl.
  - destruct (var_eq _ _); simpl.
    + subst. split; intros.
      * apply Hto in H. intuition.
      * intuition. congruence.
    + intuition. congruence.
  - destruct (var_eq _ _).
    + intuition. congruence.
    + rewrite IHe. intuition.
  - rewrite IHe1, IHe2. intuition.
Qed.

Theorem closed_subst :
  forall from to e,
    closed (\from, e) ->
    closed to ->
    closed (subst from to e).
Proof.
  unfold closed.
  simpl.
  intros from to e He Hto x.
  rewrite free_vars_subst by assumption.
  firstorder.
Qed.

Lemma step_closed :
  forall e e',
    e --> e' ->
    closed e ->
    closed e'.
Proof.
  intros e e' Hstep Hclosed.
  induction Hstep; try firstorder.
  apply closed_app_invert in Hclosed.
  break_up_hyps.
  eauto using closed_subst.
Qed.

Lemma run_for_n_steps_step_star :
  forall n e,
    closed e ->
    e -->* run_for_n_steps n e.
Proof.
  induction n; simpl; intros.
  - auto.
  - pose proof (take_one_step_step H).
    intuition.
    + eauto using step_closed.
    + rewrite H2. auto.
Qed.

Fixpoint numeral_body (n : nat) : expr :=
  match n with
  | O => "z"
  | S m => "s" @ ((\"s", \"z", numeral_body m) @ "s" @ "z")
  end.

Definition numeral (n : nat) : expr :=
  \"s", \"z", numeral_body n.
(* End of copied stuff from Week07.v *)

(*
 * PROBLEM 2 [5 points, ~15 tactics]
 *
 * Prove that "or" returns T when given T as its first argument, regardless of
 * its second argument.
 *
 * Hint: No need for induction.
 *
 * Hint: Use the three provided lemmas above in this file whose *conclusion* is
 * a trc of some kind.
 *)
Lemma or_T_left_T :
  forall e1 e2 v2,
    e1 -->* T ->
    e2 -->* v2 ->
    value v2 ->
    or e1 e2 -->* T.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * PROBLEM 3 [5 points, ~5 tactics]
 *
 * Show that a similar result does *not* hold about the second argument to "or".
 * In particular, give a counterexample of an expression e1 that causes "or"
 * to return F even though "or" is called with T as its second argument.
 *
 * Hint: Remind yourself how "or" is defined.
 *
 * Hint: Devise an e1 that has "the wrong type", i.e., is not a Church boolean.
 *
 * This is an interesting phenomenon of a program "going wrong" in some sense
 * because of a type error, but without evaluation getting stuck.
 *
 *)
Example or_T_right_wrong_answer :
  exists e1 v1 e2,
    e1 -->* v1 /\
    value v1 /\
    e2 -->* T /\
    or e1 e2 -->* F.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * PROBLEM 4 [5 points, ~20 tactics]
 *
 * Prove that if the first argument to "or" is any Church boolean, then when or
 * is passed T as its second argument, it returns T.
 *
 * Hint: The proof is broadly similar to the proof of or_T_left_T.
 *
 * Hint: At some point you will need to destruct b. Choose where carefully.
 *)
Lemma or_T_right_fixed :
  forall e1 e2 b,
    e1 -->* church_bool b ->
    e2 -->* T ->
    or e1 e2 -->* T.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


(*
 * PROBLEM 5 [10 points, ~20 tactics]
 *
 * In lecture during Week 8, we discussed a "wishful" version of the
 * substitution lemma that was an if and only if.
 *
 * Show that this one direction of the lemma is true.
 *
 * Hint: Proceed by induction. (On what?)
 *)
Lemma free_vars_subst_1 :
  forall from to e x,
    is_free_var (subst from to e) x ->
    (is_free_var e x /\ x <> from) \/ (is_free_var to x /\ is_free_var e from).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * PROBLEM 6 [5 points, ~9 tactics]
 *
 * Show that the other direction is false on our definition.
 *
 * Hint: Week07.v contains a partial proof of both directions that shows the
 * inductive proof only fails in the case for lambda ASTs. So your example must
 * use a lambda somewhere in e.
 *
 * Your example is an example of what we call "variable capture".
 *)
Example free_vars_subst_2_nope :
  exists from to e x,
    ((is_free_var e x /\ x <> from) \/
     (is_free_var to x /\ is_free_var e from)) /\
    ~ is_free_var (subst from to e) x.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


(*
 * PROBLEM 7 [15 points, ~15 tactics]
 *
 * Prove that if e is closed, then calling subst on e is a no-op.
 *
 * Hint: Note that here we are talking about *e* being closed, not "to".
 *
 * Hint: The property is not inductive on its own. You will need a stronger
 * helper lemma. If you are not sure what lemma to prove, try getting stuck in a
 * direct proof by induction of the theorem.
 *)
Theorem subst_closed :
  forall from to e,
    closed e ->
    subst from to e = e.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


(* Here is a better version of If than the one from Week07.v. This one thunks
   the branches for you, just like we did in the slides. *)
Definition If (e1 e2 e3 : expr) : expr :=
  (e1 @ (\"_", e2) @ (\"_", e3)) @ (\"x", "x").

Definition Let (x : var) (e1 e2 : expr) : expr :=
  (\x, e2) @ e1.

(*
 * PROBLEM 8 [5 points, ~1 tactics]
 *
 * Use "Fix" to write an implementation of the sum-of-the-first-n-numbers
 * function with Church numerals.
 *
 * (You are required to use "Fix" to do recursion in your solution. Do not
 * implement your function by "calling the number". The point is to practice
 * using "Fix".)
 *)
Definition SumUpto : expr :=
  "blah". (* Replace with your code. *)

Definition Two := Succ @ One.
Definition Three := Succ @ Two.
Definition Four := Succ @ Three.
Definition Five := Succ @ Four.

(*
 * PROBLEM 9 [5 points, ~4 tactics]
 *
 * Prove the following "unit test" about your SumUpto implementation.
 *
 * Hint: We recommend using run_for_n_steps_step_star, similar to the proof at
 * the bottom of Week07.v about factorial. Don't use eval_utlc; it's too slow.
 *)
Example SumUpto5 :
  SumUpto @ Five -->* numeral 15.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


(* Here are a few challenge problems about UTLC. For more core points, skip to
   the next section. *)

(* Here is a definition of when a variable is bound by some lambda in e. *)
Fixpoint is_bound_var (e : expr) (y : var) : Prop :=
  match e with
  | Var x => False
  | \x, e => x = y \/ is_bound_var e y
  | e1 @ e2 => is_bound_var e1 y \/ is_bound_var e2 y
  end.

(*
 * CHALLENGE 10 [3 points, ~4 tactics]
 *
 * Prove that some variable names can be simultaneously free and bound by giving
 * an example.
 *)
Example can_be_both_bound_and_free :
  exists e x,
    is_free_var e x /\ is_bound_var e x.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(* Here is a predicate for when it is safe to plug to into e somewhere. *)
Definition safe_to_subst (e to : expr) : Prop :=
  forall y,
    ~ (is_free_var to y /\ is_bound_var e y).

(*
 * CHALLENGE 11 [7 points, ~25 tactics]
 *
 * Prove that if the arguments to subst are "safe_to_subst",  then subst
 * satisfies the full version of our free_vars_subst lemma.
 *
 * Hint: Pretty similar to free_vars_subst from Week07.v.
 *)
Lemma free_vars_subst_no_capture :
  forall e to,
    safe_to_subst e to ->
    forall from x,
        is_free_var (subst from to e) x
      <->
        (is_free_var e x /\ x <> from) \/
        (is_free_var to x /\ is_free_var e from).
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)

(*
 * CHALLENGE 12 [5 points, ~15 tactics]
 *
 * safe_to_subst gives us a condition under which our substitution function
 * avoids capture without having to do any extra work.
 *
 * Unfortunately, this condition is not always preserved by execution.
 *
 * Give an example of a program that is safe to subst, but steps to a program
 * that is not safe.
 *)
Example safe_to_subst_not_inductive :
  exists e1 e2 e3 e4,
    e1 @ e2 --> e3 @ e4 /\
    safe_to_subst e1 e2 /\
    ~ safe_to_subst e3 e4.
Proof.
  (* YOUR CODE HERE *)
Admitted. (* Change to Qed when done *)


End UTLC.

(*
             ____                  _     _                     ____
            / ___|    ___    ___  | |_  (_)   ___    _ __     |___ \
            \___ \   / _ \  / __| | __| | |  / _ \  | '_ \      __) |
             ___) | |  __/ | (__  | |_  | | | (_) | | | | |    / __/
            |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |_____|

                    SECTION 2 : Simply-typed Lambda Calculus
*)

Module STLC.

(* Bunch of copied stuff from Week08.v *)
Inductive type :=
| Bool
| Fun : type -> type -> type.
Notation "t1 ==> t2" := (Fun t1 t2) (at level 69, right associativity).

Definition gamma := list (var * type).

Inductive expr : Type :=
| T   : expr
| F   : expr
| Var : var -> expr
| Ite : expr -> expr -> expr -> expr
| Abs : var -> expr -> expr
| App : expr -> expr -> expr.

Declare Scope stlc_scope.
Coercion Var : var >-> expr.
Notation "'\' x ',' y" := (Abs x y) (left associativity, at level 75).
Notation "'If' c 'Then' e1 'Else' e2" :=
  (Ite c e1 e2) (no associativity, at level 69).
Infix "@" := App (left associativity, at level 68).
Delimit Scope stlc_scope with expr.
Bind Scope stlc_scope with expr.

Fixpoint subst (from : var) (to : expr) (e : expr) : expr :=
  match e with
  | T => T
  | F => F
  | Var x => if var_eq from x then to else e
  | Abs x e1 => Abs x (if var_eq from x then e1 else subst from to e1)
  | App e1 e2 => App (subst from to e1) (subst from to e2)
  | If c Then e1 Else e2 =>
    If (subst from to c) Then (subst from to e1) Else (subst from to e2)
  end.

Inductive value : expr -> Prop :=
| value_abs : forall x e, value (\x, e)
| value_T   : value T
| value_F   : value F.
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
    step (App v1 e2) (App v1 e2')
| step_ite_cond :
  forall c c' e1 e2,
    step c c' ->
    step (If c Then e1 Else e2) (If c' Then e1 Else e2)
| step_true :
  forall e1 e2,
    step (If T Then e1 Else e2) e1
| step_false :
  forall e1 e2,
    step (If F Then e1 Else e2) e2.
Local Hint Constructors step : core.

Notation "e '-->' e'" := (step e e') (at level 75).
Notation "e '-->*' e'" := (trc step e e') (at level 75).

Fixpoint lookup {A} (x : var) (ctx : list (var * A)) : option A :=
  match ctx with
  | [] => None
  | (y, n) :: ctx' =>
    if var_eq x y
    then Some n
    else lookup x ctx'
  end.

Reserved Notation "G |- x : t" (at level 76, x at next level, no associativity).

Inductive hasty : gamma -> expr -> type -> Prop :=
| HtTrue :  forall G, G |- T : Bool
| HtFalse : forall G, G |- F : Bool
| HtVar :   forall G x t, lookup x G = Some t -> G |- x : t
| HtIte :   forall G c e1 e2 t,
                    (G |- c : Bool) -> (G |- e1 : t) -> (G |- e2 : t) ->
                    (G |- If c Then e1 Else e2 : t)
| HtApp :   forall G e1 e2 t1 t2,
                    (G |- e1 : (t1 ==> t2)) -> (G |- e2 : t1) ->
                    (G |- e1 @ e2 : t2)
| HtAbs :   forall G x e t1 t2,
                    ((x, t1) :: G |- e : t2) ->
                    (G |- \x, e : (t1 ==> t2))
where "G |- x : t" := (hasty G x t).
Local Hint Constructors hasty : core.

Fixpoint is_free_var (e : expr) (y : var) : Prop :=
  match e with
  | T | F => False
  | Var x => x = y
  | Abs x e => x <> y /\ is_free_var e y
  | App e1 e2 => is_free_var e1 y \/ is_free_var e2 y
  | If c Then e1 Else e2 =>
    is_free_var c y \/ is_free_var e1 y \/ is_free_var e2 y
  end.

Lemma lookup_app :
  forall A x (G1 G2 : list (var * A)),
    lookup x (G1 ++ G2)%list =
    match lookup x G1 with
    | Some t => Some t
    | None => lookup x G2
    end.
Proof.
  induction G1; simpl; intros; auto.
  destruct a, var_eq; auto.
Qed.

Definition expr_init (e : expr) (e' : expr) :=
  e' = e.
Local Hint Unfold expr_init : core.

Definition expr_to_trsys (e : expr) := {|
  Init := expr_init e;
  Step := step
|}.

Definition closed_expr_of_type (t : type) : expr -> Prop :=
  fun e =>
    [] |- e : t.

(* We proved this in Week08.v. Let's just assume it here. *)
Lemma preservation_star :
  forall e t,
    [] |- e : t ->
    is_invariant (expr_to_trsys e) (closed_expr_of_type t).
Admitted.
(* End of copied stuff from Week08.v *)

(*
 * PROBLEM 13 [3 points, ~4 tactics]
 *
 * Give an example program of STLC that has the following type:
 *
 *     (Bool ==> Bool) ==> (Bool ==> Bool ==> Bool)
 *
 * Note that "==>" is right-associative.
 *
 * Try to make your example at least sort of interesting :)
 *)
Lemma program_with_stlc :
  exists G t,
    G |- t : ((Bool ==> Bool) ==> (Bool ==> Bool ==> Bool)).
Proof.
  (* YOUR CODE HERE *)
Admitted.

Definition closed (e : expr) : Prop :=
  forall x,
    ~ is_free_var e x.

(*
 * PROBLEM 14 [10 points, ~20 tactics]
 *
 * Prove that an expression that is well typed in an empty context is closed.
 *
 * Hint: If the theorem is not inductive, you will need to prove a lemma that is
 * inductive and implies the theorem.
 *)
Theorem well_typed_empty_closed :
  forall e t,
    [] |- e : t ->
    closed e.
Proof.
  (* YOUR CODE HERE *)
Admitted.


(*
 * PROBLEM 15 [10 points, ~20 tactics]
 *
 * Prove the following lemma that says that, from the perspective of type
 * checking e, the only thing that matters about the context is what happens
 * when you look up a free variable of e.
 *
 * Hint: Proceed by induction. (On what?)
 *
 * Hint: You shouldn't need to use any other lemmas.
 *
 * Hint: The Abs case is tricky, because G1 "changes". You need to make sure
 * your induction hypothesis allows G2 to change as well. Follow the rule of
 * thumb that you should revert *everything* you're not inducting on before you
 * do the induction. In particular, be sure you've reverted G2 before inducting.
 *)
Lemma context_extentionality :
  forall G1 G2 e t,
    (forall x,
      is_free_var e x ->
      lookup x G1 = lookup x G2) ->
    G1 |- e : t ->
    G2 |- e : t.
Proof.
  (* YOUR CODE HERE *)
Admitted.

(* Extentionality is a very powerful lemma. *)

(*
 * PROBLEM 16 [2 points, ~8 tactics]
 *
 * Prove the "weakening_empty" lemma follows from extentionality.
 *
 * Hint: No need for induction. Just use the extentionality lemma.
 *
 * Hint: Use well_typed_empty_closed as well.
 *)
Lemma weakening_empty_again :
  forall G e t,
    [] |- e : t ->
    G |- e : t.
Proof.
  (* YOUR CODE HERE *)
Admitted.

(*
 * PROBLEM 17 [3 points, ~15 tactics]
 *
 * Prove the "strengthening" lemma follows from extentionality.
 *
 * Hint: No need for induction. Just use the extentionality lemma.
 *
 * Hint: Use the provided lookup_app lemma as well.
 *)
Lemma strengthening_again :
  forall G x t1 t2 e t,
    (G ++ [(x, t2)])%list |- e : t ->
    lookup x G = Some t1 ->
    G |- e : t.
Proof.
  (* YOUR CODE HERE *)
Admitted.


(*
 * PROBLEM 18 [4 points, ~15 tactics]
 *
 * Give an example of an expression which is not well typed in any context at
 * any type, but which executes just fine to the value T.
 *
 * Hint: "Hide" a type error somewhere that execution will never reach it.
 *)
Example ill_typed_but_safe :
  exists e,
    (forall G t, ~ (G |- e : t)) /\
    e -->* T.
Proof.
  (* YOUR CODE HERE *)
Admitted.

(* The rest of the problems in this section are challenge problems. Skip to the
   next section for more core points. *)

(* These challenge problems investigate termination. It turns out that all well-
   typed programs in STLC terminate, but this fact is hard to prove. These
   exercises ask you to identify where a direct proof by induction fails. *)

(* An expression terminates if it step stars to a value. *)
Definition terminates (e : expr) :=
  exists v,
    e -->* v /\
    value v.
Local Hint Unfold terminates : core.

(* You might find this lemma useful below. *)
Lemma step_star_ite_cond :
  forall c c' e1 e2,
    c -->* c' ->
    If c Then e1 Else e2 -->* If c' Then e1 Else e2.
Proof.
  intros c c' e1 e2 Hstep.
  induction Hstep; eauto.
Qed.

(* There are three challenge problems below. We recommend doing them in a
   strange order:
   - the third one "termination_attempt"
     - this one is provable using the first two problems
   - the first one "termination_ite"
     - this one is provable
   - the second one "termination_app"
     - this one is not provable directly, you will investigate why
*)

(*
 * CHALLENGE 19 [5 points, ~30 tactics]
 *
 * Prove this lemma derived from the inductive case of termination_attempt for
 * Ite expressions.
 *
 * Reminder: we recommend doing this problem *after* you do termination_attempt.
 *
 * Hint: No induction needed.
 *
 * Hint use preservation_star and step_star_ite_cond, among other lemmas.
 *)
Lemma termination_ite :
  forall c e1 e2 t,
    [] |- c : Bool ->
    [] |- e1 : t ->
    [] |- e2 : t ->
    terminates c ->
    terminates e1 ->
    terminates e2 ->
    terminates (If c Then e1 Else e2).
Proof.
  (* YOUR CODE HERE *)
Admitted.

(*
 * CHALLENGE 20 [5 points, ~2 sentences]
 *
 * Attempt to prove this lemma derived from the inductive case of
 * termination_attempt for App expressions. No need to turn in your partial
 * proof.
 *
 * Reminder: we recommend doing this problem *after* you do termination_attempt
 * and termination_ite.
 *
 * This lemma is *not* provable directly (as far as we know).
 *
 * Write a sentence or two explaining where a direct proof gets stuck. Be
 * specific, but also brief. Answer the question:
 *
 *    why are the hypotheses to this lemma not enough to imply its conclusion?
 *
 * Optionally (for zero points), also think about what additional hypothesis you
 * would need to know in order to finish the proof.
 *)
Lemma termination_app :
  forall e1 e2 tA tB,
    [] |- e1 : tA ==> tB ->
    [] |- e2 : tA ->
    terminates e1 ->
    terminates e2 ->
    terminates (e1 @ e2).
Proof.
  (* YOUR COMMENT HERE *)
Admitted.

(*
 * CHALLENGE 21 [5 points, ~6 tactics]
 *
 * Assuming the previous two lemmas, prove this theorem that says all STLC
 * expressions that are well typed in the empty context terminate.
 *
 * We have set up the induction for you. You have 6 cases to prove, one per kind
 * of AST node for expressions. Most cases are pretty easy.
 *
 * In the If-Then-Else case, use the termination_ite lemma.
 *
 * In the App case, use the termination_app lemma.
 *
 * Of course, since the termination_app lemma is not actually provable, we
 * haven't actually proved termination. But this shows you how close we are!
 * It's *just* function application that's the problem.
 *)
Theorem termination_attempt :
  forall e t,
    [] |- e : t ->
    terminates e.
Proof.
  intros e t HT.
  remember [] as G.
  revert HeqG.
  induction HT; intros; subst; easy_specialize.
  (* YOUR CODE HERE *)
Admitted.
End STLC.

(*
             ____                  _     _                     _____
            / ___|    ___    ___  | |_  (_)   ___    _ __     |___ /
            \___ \   / _ \  / __| | __| | |  / _ \  | '_ \      |_ \
             ___) | |  __/ | (__  | |_  | | | (_) | | | | |    ___) |
            |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |____/

                           SECTION 3 : Extending STLC
*)

(*
This section contains a copy of the Week 7 proof of type safety for STLC. We
will extend it with pairs. To get you started, we have included commented out
code to add the syntax of types and expressions related to pair. Begin by
uncommenting the lines marked "UNCOMMENT".
*)
Module STLC_pairs.

Inductive type :=
| Bool
| Fun : type -> type -> type
(* UNCOMMENT *)
(*
| Pair : type -> type -> type
*)
.
Notation "t1 ==> t2" := (Fun t1 t2) (at level 69, right associativity).

Definition gamma := list (var * type).

Inductive expr : Type :=
| T   : expr
| F   : expr
| Var : var -> expr
| Ite : expr -> expr -> expr -> expr
| Abs : var -> expr -> expr
| App : expr -> expr -> expr
(* UNCOMMENT *)
(*
| MkPair : expr -> expr -> expr
| Fst : expr -> expr
| Snd : expr -> expr
*)
.

Declare Scope stlc_scope.
Coercion Var : var >-> expr.
Notation "'\' x ',' y" := (Abs x y) (left associativity, at level 75).
Notation "'If' c 'Then' e1 'Else' e2" :=
  (Ite c e1 e2) (no associativity, at level 69).
Infix "@" := App (left associativity, at level 68).
Delimit Scope stlc_scope with expr.
Bind Scope stlc_scope with expr.

(*
 * PROBLEM 22 [3 points, ~4 LOC]
 *
 * Extend the substitution function with cases for the new expressions.
 *
 * Reminder: don't forget to uncomment the lines marked "UNCOMMENT" above.
 *
 * Hint: Since the new expressions don't bind or use any variables, these cases
 * are similar to App and If.
 *
 *)
Fixpoint subst (from : var) (to : expr) (e : expr) : expr :=
  match e with
  | T => T
  | F => F
  | Var x => if var_eq from x then to else e
  | Abs x e1 => Abs x (if var_eq from x then e1 else subst from to e1)
  | App e1 e2 => App (subst from to e1) (subst from to e2)
  | If c Then e1 Else e2 =>
    If (subst from to c) Then (subst from to e1) Else (subst from to e2)
  (* YOUR CODE HERE *)
  end.

(* Uncomment the constructor below, which says that a pair is a value if both
   its components are values. *)
Inductive value : expr -> Prop :=
| value_abs : forall x e, value (\x, e)
| value_T   : value T
| value_F   : value F
(* UNCOMMENT *)
(*
| value_pair :
  forall v1 v2,
    value v1 ->
    value v2 ->
    value (MkPair v1 v2)
*)
.
Local Hint Constructors value : core.

(*
 * PROBLEM 23 [10 points, ~30 LOC]
 *
 * Add 6 new rules for executing the new expressions, according to the following
 * long horizontal lines.
 *
 *             e1 --> e1'
 * -----------------------------------
 *    MkPair e1 e2 --> MkPair e1' e2
 *
 *
 *     value v1          e2 --> e2'
 * -----------------------------------
 *    MkPair v1 e2 --> MkPair v1 e2'
 *
 *
 *              e --> e'
 * ----------------------------------
 *          Fst e --> Fst e'
 *
 *
 *   value v1             value v2
 * ----------------------------------
 *   Fst (MkPair v1 v2) --> v1
 *
 *
 *              e --> e'
 * ----------------------------------
 *          Snd e --> Snd e'
 *
 *
 *   value v1             value v2
 * ----------------------------------
 *   Snd (MkPair v1 v2) --> v2
 *
 *)
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
    step (App v1 e2) (App v1 e2')
| step_ite_cond :
  forall c c' e1 e2,
    step c c' ->
    step (If c Then e1 Else e2) (If c' Then e1 Else e2)
| step_true :
  forall e1 e2,
    step (If T Then e1 Else e2) e1
| step_false :
  forall e1 e2,
    step (If F Then e1 Else e2) e2
(* YOUR CODE HERE *)
.
Local Hint Constructors step : core.

Notation "e '-->' e'" := (step e e') (at level 75).
Notation "e '-->*' e'" := (trc step e e') (at level 75).

Fixpoint lookup (x : var) (ctx : gamma) : option type :=
  match ctx with
  | [] => None
  | (y, n) :: ctx' =>
    if var_eq x y
    then Some n
    else lookup x ctx'
  end.

Reserved Notation "G |- x : t" (at level 76, x at next level, no associativity).

(*
 * PROBLEM 24 [5 points, ~15 LOC]
 *
 * Add 3 new typing rules for the new expressions, according to these long
 * horizontal lines.
 *
 *      G |- e1 : t1                G |- e2 : t2
 * --------------------------------------------------
 *         G |- MkPair e1 e2 : Pair t1 t2
 *
 *
 *       G |- e : Pair t1 t2
 * -------------------------------
 *       G |- Fst e : t1
 *
 *
 *       G |- e : Pair t1 t2
 * -------------------------------
 *       G |- Snd e : t2
 *
 *)
Inductive hasty : gamma -> expr -> type -> Prop :=
| HtTrue :  forall G, G |- T : Bool
| HtFalse : forall G, G |- F : Bool
| HtVar :   forall G x t, lookup x G = Some t -> G |- x : t
| HtIte :   forall G c e1 e2 t,
                    (G |- c : Bool) -> (G |- e1 : t) -> (G |- e2 : t) ->
                    (G |- If c Then e1 Else e2 : t)
| HtApp :   forall G e1 e2 t1 t2,
                    (G |- e1 : (t1 ==> t2)) -> (G |- e2 : t1) ->
                    (G |- e1 @ e2 : t2)
| HtAbs :   forall G x e t1 t2,
                    ((x, t1) :: G |- e : t2) ->
                    (G |- \x, e : (t1 ==> t2))
(* YOUR CODE HERE *)
where "G |- x : t" := (hasty G x t).
Local Hint Constructors hasty : core.

Definition expr_init (e : expr) (e' : expr) :=
  e' = e.

Definition expr_to_trsys (e : expr) := {|
  Init := expr_init e;
  Step := step
|}.

Definition unstuck e :=
  value e \/ exists e', e --> e'.

Lemma lookup_app :
  forall x G1 G2,
    lookup x (G1 ++ G2)%list =
    match lookup x G1 with
    | Some t => Some t
    | None => lookup x G2
    end.
Proof.
  induction G1; simpl; intros; auto.
  destruct a, var_eq; auto.
Qed.


(*
 * PROBLEM 25 [5 points, ~20 tactics]
 *
 * Fix the proof of progress by adding new cases as needed.
 *
 * Reminder: don't forget to uncomment the value constructor for pairs marked
 * "UNCOMMENT" above, or this lemma will not be provable.
 *
 * Hint: the new cases are pretty similar to the old cases.
 *)
Lemma progress :
  forall e t,
    [] |- e : t ->
    unstuck e.
Proof.
  intros.
  remember [] as G.
  revert HeqG.
  induction H; intros; subst; unfold unstuck; eauto; easy_specialize.
  - simpl in *. discriminate.
  - clear IHhasty2 IHhasty3.
    unfold unstuck in *.
    intuition.
    + invc H2; invc H; eauto.
    + destruct H2; eauto.
  - destruct IHhasty1.
    + invc H1; invc H.
      destruct IHhasty2.
      * eauto.
      * destruct H. eauto.
    + destruct H1. eauto.
  (* YOUR CODE HERE *)
Admitted.

Lemma weakening_middle :
  forall G1 G2 G3 e t,
    (forall x t1,
      lookup x G3 = Some t1 ->
      lookup x G2 = None) ->
    (G1 ++ G3)%list |- e : t ->
    (G1 ++ G2 ++ G3)%list |- e : t.
Proof.
  intros G1 G2 G3 e t Disjoint He.
  remember (G1 ++ G3)%list as G.
  revert G1 G2 G3 HeqG Disjoint.
  induction He; intros; subst; eauto.
  - econstructor.
    rewrite lookup_app in *.
    destruct (lookup x G1); auto.
    rewrite lookup_app.
    erewrite Disjoint; eauto.
  - econstructor.
    specialize (IHHe (_ :: _) G2 _ eq_refl Disjoint).
    auto.
Qed.

Lemma weakening_append :
  forall G1 G2 e t,
    (forall x t1,
      lookup x G2 = Some t1 ->
      lookup x G1 = None) ->
    G2 |- e : t ->
    (G1 ++ G2)%list |- e : t.
Proof.
  intros G1 G2 e t Disjoint He.
  apply weakening_middle with (G1 := []); auto.
Qed.

Lemma weakening_empty :
  forall G e t,
    [] |- e : t ->
    G |- e : t.
Proof.
  intros G e t He.
  apply weakening_append with (G1 := G) in He.
  - rewrite app_nil_r in He. auto.
  - simpl. discriminate.
Qed.

Lemma strengthening :
  forall G x t1 t2 e t,
    (G ++ [(x, t2)])%list |- e : t ->
    lookup x G = Some t1 ->
    G |- e : t.
Proof.
  intros G x t1 t2 e t He HG.
  remember (G ++ [(x, t2)])%list as G'.
  revert G t1 HeqG' HG.
  induction He; intros; subst; eauto.
  - rewrite lookup_app in H.
    destruct (lookup x0 G0) eqn:?.
    + invc H. auto.
    + simpl in *. destruct var_eq; congruence.
  - constructor.
    apply IHHe with (t1 := if var_eq x x0 then t1 else t3); auto.
    simpl.
    destruct var_eq; auto.
Qed.

Lemma substitution :
  forall G  e t x t1 v,
    (G ++ [(x, t1)])%list |- e : t ->
    lookup x G = None ->
    [] |- v : t1->
    G |- subst x v e : t.
Proof.
  intros G e t x t1 v He Hlook Hv.
  remember (G ++ [(x, t1)])%list as G'.
  revert G x t1 v Hlook Hv HeqG'.
  induction He; simpl; intros; subst; eauto.
  - rewrite lookup_app in H.
    destruct var_eq.
    + subst. rewrite Hlook in H.
      simpl in *. destruct var_eq; try congruence.
      invc H.
      auto using weakening_empty.
    + destruct (lookup x G0) eqn:L.
      * invc H. auto.
      * simpl in *. destruct var_eq; congruence.
  - constructor.
    destruct var_eq.
    + subst. eapply strengthening; eauto.
      simpl.
      destruct var_eq; try congruence.
      reflexivity.
    + eapply IHHe; eauto.
      simpl.
      destruct var_eq; congruence.
Qed.

Lemma substitution_one :
  forall x t1 e t v,
    [(x, t1)] |- e : t ->
    [] |- v : t1->
    [] |- subst x v e : t.
Proof.
  eauto using substitution.
Qed.

(*
 * PROBLEM 26 [5 points, ~5 tactics]
 *
 * Fix the proof of preservation by adding new cases as needed.
 *
 * Hint: The new cases are pretty easy.
 *)
Lemma preservation :
  forall e e' t,
    [] |- e : t ->
    e --> e' ->
    [] |- e' : t.
Proof.
  intros e e' t HT Step.
  revert t HT.
  induction Step; intros t HT; invc HT; eauto.
  - invc H3. eauto using substitution_one.
  (* YOUR CODE HERE *)
Admitted.

Definition closed_expr_of_type (t : type) : expr -> Prop :=
  fun e =>
    [] |- e : t.

Lemma preservation_star :
  forall e t,
    [] |- e : t ->
    is_invariant (expr_to_trsys e) (closed_expr_of_type t).
Proof.
  invariant_induction_boilerplate;
  eauto using preservation.
Qed.

(* That's all there is to it! *)
Theorem type_safety :
  forall e t,
    [] |- e : t ->
    is_invariant (expr_to_trsys e) unstuck.
Proof.
  intros e t HHT.
  apply invariant_implies with (P := closed_expr_of_type t).
  - apply preservation_star. auto.
  - intros. eapply progress; eauto.
Qed.
End STLC_pairs.

(* Feedback question *)
(*
 * PROBLEM 27 [5 points, ~3 sentences]
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
 * This is the end of Homework 5.
 *
 * To submit your homework, please follow the instructions at the end of the
 * README.md file in this directory.
 *
 * Please also see the README.md file to read about how we will grade this
 * homework assignment.
 *)
