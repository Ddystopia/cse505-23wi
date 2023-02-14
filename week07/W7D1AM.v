Require Import Arith Lia List String.
Import ListNotations.
Open Scope string.

(* enable type inference *)
Set Implicit Arguments.

Set Nested Proofs Allowed.

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
Print Id.

Example eval_identity :
  Id @ (\"y", "z") --> (\"y", "z").
Proof.
  unfold Id.
  Print step.

Compute 
  subst "x" (\"y", "z") (Var "x").  

  apply step_beta.
Print value.
  apply value_abs.
  Restart.

constructor.
constructor.
Restart.

repeat constructor.

Qed.

Definition T := \"x", \"y", "x".
Definition F := \"x", \"y", "y".

Example higher_order_function :
  (\"x", "x" @ F) @ Id -->* F.
Proof.
  Print trc.
  repeat econstructor.

Restart.
  econstructor.
  econstructor.
  econstructor.
  cbn.
  econstructor.
  Restart.
  repeat econstructor.
Qed.

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

Example higher_order_function_again :
  (\"x", "x" @ F) @ Id -->* F.
Proof.
  eval_utlc.
Qed.

Example id_id :
  Id @ Id -->* Id.
Proof.
  eval_utlc.
Qed.

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

Theorem church_not :
  forall e b,
    evals_to e (church_bool b) ->
    evals_to (not e) (church_bool (negb b)).
Proof.
  intros e b [Step V].
  split.
  - unfold not.
    eapply trc_transitive.
    eapply step_star_app_left.
    eapply step_star_app_left.
    eauto.
    unfold church_bool.
    destruct b; simpl; eval_utlc.
  - destruct b; simpl; constructor.
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

(* caller's job to thunk e2/e3 if needed *)
Definition If (e1 e2 e3 : expr) : expr :=
  e1 @ e2 @ e3.

Lemma subst_value :
  forall from to v,
    value v ->
    value (subst from to v).
Proof.
  intros from to v V.
  invc V.
  simpl.
  auto.
Qed.

Theorem church_if :
  forall e1 b1 e2 e3 v2 v3,
    evals_to e1 (church_bool b1) ->
    evals_to e2 v2 ->
    evals_to e3 v3 ->
    evals_to (If e1 e2 e3) (if b1 then subst "y" v3 v2 else v3).
Proof.
  intros e1 b1 e2 e3 v2 v3 [Step1 V1] [Step2 V2] [Step3 V3].
  unfold If.
  split.
  - eapply trc_transitive.
    eapply step_star_app_left.
    eapply step_star_app_left.
    eauto.
    unfold church_bool.
    eapply trc_transitive.
    eapply step_star_app_left.
    eapply step_star_app_right.
    eauto.
    destruct b1; constructor.
    destruct b1.
    + unfold T.
      eapply trc_front.
      eapply step_app_left.
      apply step_beta.
      auto.
      cbn.
      eapply trc_transitive.
      apply step_star_app_right.
      eauto.
      constructor.
      eapply trc_front.
      apply step_beta.
      auto.
      apply trc_refl.
    + unfold F.
      eapply trc_front.
      eapply step_app_left.
      apply step_beta.
      auto.
      cbn.
      eapply trc_transitive.
      apply step_star_app_right.
      eauto.
      constructor.
      eapply trc_front.
      apply step_beta.
      auto.
      cbn.
      apply trc_refl.
  - destruct b1; auto using subst_value.
Qed.

Definition Zero := (\"s", \"z", "z").
Definition One_manually  := (\"s", \"z", "s" @ "z").

Definition Succ := (\"n", \"s", \"z", "s" @ (("n" @ "s") @ "z")).
Definition One := Succ @ Zero.

Definition Two := Succ @ One.

Theorem it_is_two :
  Two @ F @ T -->*
  F @ (F @ T).
Proof.
  eval_utlc.
Qed.

Fixpoint numeral_body (n : nat) : expr :=
  match n with
  | O => "z"
  | S m => "s" @ ((\"s", \"z", numeral_body m) @ "s" @ "z")
  end.
Definition numeral (n : nat) : expr :=
  \"s", \"z", numeral_body n.

Example numeral_zero :
  Zero = numeral 0.
Proof. reflexivity. Qed.

Example numeral_one :
  Succ @ Zero -->* numeral 1.
Proof.
  unfold Succ, Zero, numeral.
  simpl.
  eval_utlc.
Qed.

Lemma numeral_succ :
  forall n e,
    evals_to e (numeral n) ->
    evals_to (Succ @ e) (numeral (S n)).
Proof.
  unfold evals_to, Succ, numeral.
  intros n e [Hstep HV].
  simpl.
  split; auto.
  eapply trc_transitive.
  eapply step_star_app_right; eauto.
  eapply trc_front.
  eauto.
  cbn.
  auto.
Qed.

Definition Add := \"n1", \"n2", "n2" @ Succ @ "n1".
Definition Mult := \"n1", \"n2", "n2" @ (Add @ "n1") @ Zero.

Example two_plus_two :
  Add @ Two @ Two -->* numeral 4.
Proof.
  unfold numeral. simpl.
  eval_utlc.
Qed.

Example two_times_two :
  Mult @ Two @ Two -->* numeral 4.
Proof.
  unfold numeral. simpl.
  eval_utlc.
Qed.

Lemma subst_numeral_body :
  forall from to n,
    from <> "s" ->
    from <> "z" ->
    subst from to (numeral_body n) = numeral_body n.
Proof.
  intros from to n Hs Hz.
  induction n; simpl.
  - destruct (var_eq _ _); congruence.
  - destruct (var_eq _ _), (var_eq _ _); congruence.
Qed.

Lemma deconstruct_app_execution :
  forall e1 e2 v,
    e1 @ e2 -->* v ->
    value v ->
    exists v1 v2,
      e1 -->* v1 /\
      e2 -->* v2 /\
      value v1 /\
      value v2 /\
      v1 @ v2 -->* v.
Proof.
  intros e1 e2 v Step V.
  remember (e1 @ e2) as e.
  revert e1 e2 Heqe V.
  induction Step; intros; subst.
  - invc V.
  - invc H.
    + eauto 10.
    + specialize (IHStep _ _ eq_refl V).
      break_up_hyps.
      eauto 10.
    + specialize (IHStep _ _ eq_refl V).
      break_up_hyps.
      eauto 10.
Qed.

Lemma numeral_body_add :
  forall n1 n2,
    subst "z" (\ "s", (\ "z", numeral_body n1))
      (subst "s" Succ (numeral_body n2))
    -->*
    \"s", \"z", numeral_body (n1 + n2).
Proof.
  induction n2; simpl.
  - rewrite <- plus_n_O. auto.
  - rewrite <- plus_n_Sm. simpl.
    eval_utlc.
    fold Succ.
    eapply trc_transitive.
    eapply step_star_app_right; [|unfold Succ; auto].
    apply IHn2.
    unfold Succ.
    eval_utlc.
Qed.

Lemma numeral_add :
  forall n1 n2 e1 e2,
    evals_to e1 (numeral n1) ->
    evals_to e2 (numeral n2) ->
    evals_to (Add @ e1 @ e2) (numeral (n1 + n2)).
Proof.
  unfold evals_to, Add.
  intros n1 n2 e1 e2 [Step1 V1] [Step2 V2].
  split.
  - eapply trc_transitive.
    eapply step_star_app_left.
    eapply step_star_app_right; eauto.
    eapply trc_transitive.
    eapply trc_front.
    eauto.
    cbn. fold Succ.
    eapply step_star_app_right; eauto.
    eapply trc_front.
    eauto.
    cbn.
    rewrite subst_numeral_body by congruence.
    unfold numeral.
    eval_utlc.
    apply numeral_body_add.
  - unfold numeral. auto.
Qed.

Definition Pair := \"fst", \"snd", \"f", "f" @ "fst" @ "snd".

Definition Fst := \"pi", "pi" @ (\"x", \"y", "x").
Definition Snd := \"pi", "pi" @ (\"x", \"y", "y").

Definition PairZero := Pair @ Zero @ Zero.
Definition PairSucc := \"pi", Pair @ (Succ @ (Fst @ "pi")) @ (Fst @ "pi").

Theorem pair_fst :
  Fst @ (Pair @ T @ F)  -->* T.
Proof.
  unfold Fst, Pair, T, F.
  eval_utlc.
Qed.

Definition Pred := \"n", Snd @ ("n" @ PairSucc @ PairZero).

Theorem pred_of_1 :
  Pred @ One -->* Zero.
Proof.
  unfold Pred, Snd, PairSucc, PairZero, One, Zero, Fst, Pair, Succ.
  eval_utlc.
Qed.

Theorem pred_of_two :
  Pred @ Two -->*
  (\"s", (\"z",
    "s" @ ((\"s", (\"z", "z")) @ "s" @ "z"))).
Proof.
  unfold Pred, Two, Snd, PairSucc, PairZero, Succ, One, Pair, Fst, Zero.
  eval_utlc.
Qed.

Definition Omega :=
  (\"x", "x" @ "x") @
  (\"x", "x" @ "x").

Theorem omega_to_self:
  Omega --> Omega.
Proof.
  unfold Omega;
  repeat econstructor.
Qed.

Definition Fix :=
  (\"f",
    (\"x", "f" @ (\"y", "x" @ "x" @ "y")) @
    (\"x", "f" @ (\"y", "x" @ "x" @ "y"))).

Definition IsZero :=
  \"n", "n" @ (\"_", F) @ T.

Lemma all_numbers_are_values:
  forall x, value (numeral x).
Proof.
  intros; unfold numeral; econstructor.
Qed.

Lemma step_right_replace :
  forall e1 e2 v, value e1 -> value v -> e2 -->* v -> (e1 @ e2) -->* (e1 @ v).
Proof.
  intros.
  generalize dependent e1.
  induction H1; intros; econstructor.
  - apply step_app_right; eassumption.
  - specialize (IHtrc H0). eauto.
Qed.

Lemma replace_subst :
  forall e1 e2 v v2,
    value e1 ->
    value v ->
    value v2 ->
    e2 -->* v2 ->
    (e1 @ v2 -->* v) ->
    (e1 @ e2 -->* v).
Proof.
  intros.
  induction H2.
  - auto.
  - econstructor.
    + apply step_app_right; eauto.
    + apply IHtrc; eauto.
Qed.

Theorem is_zero_ok :
  forall x, IsZero @ (numeral (S x)) -->* F.
Proof.
  intros.
  unfold numeral, IsZero.
  eval_utlc.
  induction x.
  - cbn. eval_utlc.
  - cbn. apply deconstruct_app_execution in IHx.
    + destruct IHx as [v1 [v2 [Hsteps [Hsubstz [Hv1 [Hv2 Happ]]]]]].
      eval_utlc.
      apply replace_subst with
              (e2 := ((\ "_", (\ "x", (\ "y", "y"))) @
                      subst "z" (\ "x", (\ "y", "x"))
                          (subst "s" (\ "_", (\ "x", (\ "y", "y"))) (numeral_body x))))
              (v2 := F); eauto.
      * econstructor.
      * econstructor.
      * apply replace_subst with (v2 := v2); eauto.
        econstructor.
      * unfold F. eval_utlc.
    + econstructor.
Qed.

Definition Fact :=
  Fix @ (\"rec", \"n",
    (If (IsZero @ "n")
      (\"_", One)
      (\"_", Mult @ "n" @ ("rec" @ (Pred @ "n")))) @ Id).

Definition Three := Succ @ Two.

Example factorial_3 :
  Fact @ Three -->* numeral 6.
Proof.
  eval_utlc.
Qed.

Fixpoint take_one_step (e : expr) : expr :=
  match e with
  | Var _ => e
  | Abs _ _ => e
  | App (Abs x e) ((Abs _ _) as v) => subst x v e
  | App (Abs x e) e2 => App (Abs x e) (take_one_step e2)
  | App e1 e2 => App (take_one_step e1) e2
  end.

Lemma closed_app_invert :
  forall e1 e2,
    closed (e1 @ e2) ->
    closed e1 /\ closed e2.
Proof.
  firstorder.
Qed.

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

Compute (run_for_n_steps 5000 (Fact @ Three)).

Theorem closed_subst :
  forall from to e,
    closed (\from, e) ->
    closed to ->
    closed (subst from to e).
Abort.

(* If subst was capture-avoiding, we would want to prove this theorem. *)
Lemma free_vars_subst :
  forall from to e x,
    is_free_var (subst from to e) x <->
    (is_free_var e x /\ x <> from) \/ (is_free_var to x /\ is_free_var e from).
Proof.
  intros from to e.
  induction e; intros x; simpl.
  - destruct (var_eq _ _); simpl.
    + subst. intuition. congruence.
    + intuition.
      * subst. auto.
      * congruence.
  - admit. (* other cases work, this one's not true *)
  - rewrite IHe1, IHe2. intuition.
Abort.

(* Here's the special case where "to" is closed. *)
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

Definition expr_init (e : expr) (e' : expr) :=
  e' = e.

Definition expr_to_trsys (e : expr) := {|
  Init := expr_init e;
  Step := step
|}.

Theorem step_star_closed :
  forall e,
    closed e ->
    is_invariant (expr_to_trsys e) closed.
Proof.
  intros e HC.
  apply invariant_induction.
  - unfold initially_holds. simpl.
    unfold expr_init. intros. subst. auto.
  - unfold closed_under_step. simpl.
    eauto using step_closed.
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

Example factorial_3_again :
  Fact @ Three -->* numeral 6.
Proof.
  (* really slow: eval_utlc. *)
  (* faster proof *)
  apply run_for_n_steps_step_star with (n := 1000).
  compute.
  intuition.
Qed.