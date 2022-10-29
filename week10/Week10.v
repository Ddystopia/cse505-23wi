Require Import Arith Lia List String.
Import ListNotations.

(* enable type inference *)
Set Implicit Arguments.

(* GENERIC HELPER TACTICS / LEMMAS *)

Create HintDb hints.

Ltac inv H :=
  inversion H; subst.

Ltac invc H :=
  inv H; clear H.

Ltac break_up_hyps :=
  repeat match goal with
  | [ H : exists _, _ |- _ ] => destruct H
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ H : (_, _) = (_, _) |- _ ] => invc H
  end.

Ltac ee :=
  econstructor; eauto.

Ltac listy :=
  repeat rewrite app_nil_l;
  repeat rewrite app_nil_r;
  repeat rewrite app_assoc;
  auto.

Ltac case_if :=
  match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
  end.

(*
  CREDITS: from StructTact 
    https://github.com/uwplse/StructTact/blob/master/theories/StructTactics.v
*)

Ltac break_if :=
  match goal with
  | [ |- context [ if ?X then _ else _ ] ] =>
      match type of X with
      | sumbool _ _ => destruct X
      | _ => destruct X eqn:?
      end
  | [ H : context [ if ?X then _ else _ ] |- _] =>
      match type of X with
      | sumbool _ _ => destruct X
      | _ => destruct X eqn:?
      end
  end.

Ltac break_match_hyp :=
  match goal with
  | [ H : context [ match ?X with _ => _ end ] |- _] =>
      match type of X with
      | sumbool _ _ => destruct X
      | _ => destruct X eqn:?
      end
  end.

Ltac break_match_goal :=
  match goal with
  | [ |- context [ match ?X with _ => _ end ] ] =>
      match type of X with
      | sumbool _ _ => destruct X
      | _ => destruct X eqn:?
      end
  end.

Ltac find_apply_hyp_hyp :=
  match goal with
    | [ H : forall _, _ -> _,
        H' : _ |- _ ] =>
      apply H in H'; [idtac]
    | [ H : _ -> _ , H' : _ |- _ ] =>
      apply H in H'; auto; [idtac]
  end.

Ltac find_apply_lem_hyp lem :=
  match goal with
    | [ H : _ |- _ ] => apply lem in H
  end.

Ltac find_eapply_lem_hyp lem :=
  match goal with
    | [ H : _ |- _ ] => eapply lem in H
  end.

Ltac find_rewrite :=
  match goal with
    | [ H : ?X _ _ _ _ = _, H' : ?X _ _ _ _ = _ |- _ ] => rewrite H in H'
    | [ H : ?X = _, H' : ?X = _ |- _ ] => rewrite H in H'
    | [ H : ?X = _, H' : context [ ?X ] |- _ ] => rewrite H in H'
    | [ H : ?X = _ |- context [ ?X ] ] => rewrite H
  end.

Ltac rewrite_match_goal :=
  match goal with
  | [ H : ?X = _ |- context [ ?X ] ] => rewrite H
  end.

Lemma length_app_lt1_inv :
  forall A (l1 l2 : list A),
    List.length (l1 ++ l2) <= 1 ->
    l1 = [] \/ l2 = [].
Proof.
  intros A l1 l2 Hlen.
  destruct l1, l2; auto.
  rewrite app_length in Hlen.
  simpl in *. lia.
Qed.

Local Hint Resolve in_or_app : hints.


Section TransitiveReflexiveClosure.

Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| trc_refl :
    forall x,
      trc R x x
| trc_front :
    forall x y z,
      R x y ->
      trc R y z ->
      trc R x z.

Lemma trc_trans :
  forall A (R : A -> A -> Prop) a b c,
    trc R a b ->
    trc R b c ->
    trc R a c.
Proof.
  intros A R a b c Hab.
  revert c; induction Hab; intros c Hbc.
  - assumption.
  - ee.
Qed.

Lemma trc_back :
  forall A (R : A -> A -> Prop) a b c,
    trc R a b ->
    R b c ->
    trc R a c.
Proof.
  (* From Homework 3. *)
Admitted.

End TransitiveReflexiveClosure.
Local Hint Constructors trc : hints.
Local Hint Resolve trc_trans : hints.
Local Hint Resolve trc_back : hints.


Section LabeledClosures.

Variable label : Type.
Local Notation trace := (list label).

Variable state : Type.

Variable step : state -> trace -> state -> Prop.

Definition can_step (s : state) : Prop :=
  exists t s', step s t s'.

Definition no_step (s : state) : Prop :=
  forall t s', ~ step s t s'.

Inductive star : state -> trace -> state -> Prop :=
| star_refl :
    forall s,
      star s [] s
| star_front :
    forall s1 t1 s2 t2 s3 t,
      step s1 t1 s2 ->
      star s2 t2 s3 ->
      t = t1 ++ t2 ->
      star s1 t s3.

Lemma star_trans :
  forall a tab b,
    star a tab b ->
    forall tbc c tac,
      star b tbc c ->
      tac = tab ++ tbc ->
      star a tac c.
Proof.
  induction 1; simpl; intros; subst.
  - assumption.
  - ee. listy.
Qed.

Lemma star_back :
  forall s1 t1 s2 t2 s3 t,
    star s1 t1 s2 ->
    step s2 t2 s3 ->
    t = t1 ++ t2 ->
    star s1 t s3.
Proof.
  (* From Homework 3. *)
Admitted. 

Inductive plus : state -> trace -> state -> Prop :=
| plus_front :
    forall s1 t1 s2 t2 s3 t,
      step s1 t1 s2 ->
      star s2 t2 s3 ->
      t = t1 ++ t2 ->
      plus s1 t s3.

Lemma plus_star :
  forall a t b,
    plus a t b ->
    star a t b.
Proof.
  intros a t b Hplus.
  inv Hplus. ee.
Qed.

Lemma step_plus_plus :
  forall a tab b tbc c tac,
    step a tab b ->
    plus b tbc c ->
    tac = tab ++ tbc ->
    plus a tac c.
Proof.
  intros a tab b tbc c tac Hstep Hplus Htac.
  invc Hplus. ee. ee.
Qed.

Lemma star_plus_plus :
  forall a tab b,
    star a tab b ->
    forall tbc c tac,
      plus b tbc c ->
      tac = tab ++ tbc ->
      plus a tac c.
Proof.
  induction 1; simpl; intros; subst.
  - assumption.
  - eapply step_plus_plus; eauto. listy.
Qed.

Lemma plus_star_plus :
  forall a tab b tbc c tac,
    plus a tab b ->
    star b tbc c ->
    tac = tab ++ tbc ->
    plus a tac c.
Proof.
  intros a tab b tbc c tac Hplus Hstar Htac.
  invc Hplus. ee.
  - eapply star_trans; eauto.
  - listy.
Qed.

Lemma star_plus_star :
  forall a tab b tbc c tac,
    star a tab b ->
    plus b tbc c ->
    tac = tab ++ tbc ->
    star a tac c.
Proof.
  intros a tab b tbc c tac Hstar Hplus Htac. 
  eapply star_trans; eauto.
  apply plus_star; auto.
Qed.

Lemma plus_star_star :
  forall a tab b tbc c tac,
    plus a tab b ->
    star b tbc c ->
    tac = tab ++ tbc ->
    star a tac c.
Proof.
  intros a tab b tbc c tac Hplus Hstar Htac. 
  eapply star_trans; eauto.
  apply plus_star; auto.
Qed.

Lemma plus_trans :
  forall a tab b tbc c tac,
    plus a tab b ->
    plus b tbc c ->
    tac = tab ++ tbc ->
    plus a tac c.
Proof.
  intros a tab b tbc c tac Hplus1 Hplus2 Htac.
  invc Hplus1. ee.
  + eapply star_plus_star; eauto.
  + listy.
Qed.

Lemma plus_back :
  forall s1 t1 s2 t2 s3 t,
    star s1 t1 s2 ->
    step s2 t2 s3 ->
    t = t1 ++ t2 ->
    plus s1 t s3.
Proof.
  (* From Homework 3. *)
Admitted. 

Inductive starn : nat -> state -> trace -> state -> Prop :=
| starn_refl :
    forall s,
      starn 0 s [] s
| starn_front :
    forall n s1 t1 s2 t2 s3 t,
      step s1 t1 s2 ->
      starn n s2 t2 s3 ->
      t = t1 ++ t2 ->
      starn (S n) s1 t s3.

Lemma star_starn :
  forall s1 t1 s2,
    star s1 t1 s2 ->
    exists n, starn n s1 t1 s2.
Proof.
  induction 1.
  - exists 0; ee.
  - destruct IHstar as [n IHstar].
    exists (S n); ee.
Qed.

Lemma starn_star :
  forall n s1 t1 s2,
    starn n s1 t1 s2 ->
    star s1 t1 s2.
Proof.
  induction 1; ee.
Qed.

Lemma starn_trans :
  forall n12 s1 t12 s2,
    starn n12 s1 t12 s2 ->
    forall n23 t23 s3 t,
      starn n23 s2 t23 s3 ->
      t = t12 ++ t23 ->
      starn (n12 + n23) s1 t s3.
Proof.
  induction 1; intros; subst; auto.
  eapply IHstarn in H2; eauto.
  ee. listy.
Qed.

Inductive Plus : state -> trace -> state -> Prop :=
| Plus_single :
    forall s1 t s2,
      step s1 t s2 ->
      Plus s1 t s2
| Plus_front :
    forall s1 t1 s2 t2 s3 t,
      step s1 t1 s2 ->
      Plus s2 t2 s3 ->
      t = t1 ++ t2 ->
      Plus s1 t s3.

Lemma plus_Plus :
  forall s1 t s2,
    plus s1 t s2 ->
    Plus s1 t s2.
Proof.
  intros s1 t s2 Hplus.
  invc Hplus. revert s1 t1 H.
  induction H0; intros; subst.
  - rewrite app_nil_r. ee.
  - eapply Plus_front; eauto.
Qed.

Lemma Plus_plus :
  forall s1 t s2,
    Plus s1 t s2 ->
    plus s1 t s2.
Proof.
  intros s1 t s2 Hplus.
  induction Hplus; subst.
  - repeat ee. rewrite app_nil_r; auto.
  - invc IHHplus. repeat ee.
Qed.

Lemma plus_single_event_inv :
  forall s1 t s2,
    plus s1 t s2 ->
    List.length t <= 1 ->
    exists s1' s2',
      star s1 [] s1' /\
      step s1' t s2' /\
      star s2' [] s2.
Proof.
  intros s1 t s2 Hp.
  apply plus_Plus in Hp.
  induction Hp; intros; subst.
  - exists s1; exists s2; repeat ee.
  - edestruct IHHp as [sA [sB [HstarA [HstepAB HstarB]]]].
      rewrite app_length in H1. lia.
    apply length_app_lt1_inv in H1. destruct H1; subst.
    + exists sA; exists sB; repeat ee.
    + rewrite app_nil_r.
      exists s1; exists s2; intuition; [ee |].
      eapply star_trans; eauto. ee. auto.
Qed.

Lemma plus_can_step :
  forall s1 t s2,
    plus s1 t s2 ->
    can_step s1.
Proof.
  intros s1 t s2 Hplus.
  invc Hplus; ee.
Qed.

End LabeledClosures.
Local Hint Constructors star : hints.
Local Hint Resolve star_trans : hints.
Local Hint Resolve star_back : hints.
Local Hint Constructors plus : hints.
Local Hint Resolve plus_back : hints.


Section LabeledTransitionSystems.

Variable label : Type.
Local Notation trace := (list label).

Variable state : Type.

Record trsys :=
  { Init : state -> Prop
  ; Step : state -> trace -> state -> Prop
  ; Final : state -> Prop
  ; FinalNoStep : forall s, Final s -> no_step Step s }.

(*
  Defining and proving invariants for labeled transition systems (LTSes)
  is almost identical to what we had for unlabeled transition systems.
  The only difference is that invariants can also talk about the trace.
*)

Inductive reachable (sys : trsys) : trace -> state -> Prop :=
| Reachable :
    forall s0 t sN,
      sys.(Init) s0 ->
      star sys.(Step) s0 t sN ->
      reachable sys t sN.
Local Hint Constructors reachable : hints.

Definition is_invariant (sys : trsys) (P : trace -> state -> Prop) :=
  forall s0,
    sys.(Init) s0 ->
    forall t sN,
      star sys.(Step) s0 t sN ->
      P t sN.

Definition initially_holds (sys : trsys) (P : trace -> state -> Prop) :=
  forall s0,
    sys.(Init) s0 ->
    P [] s0.

Definition closed_under_step (sys : trsys) (P : trace -> state -> Prop) :=
  forall t01 s1,
    P t01 s1 ->
    forall t12 s2 t,
      sys.(Step) s1 t12 s2 ->
      t = t01 ++ t12 ->
      P t s2.

Lemma closed_under_step_star (sys : trsys) (P : trace -> state -> Prop) :
  forall s1 t1N sN,
    star sys.(Step) s1 t1N sN ->
    closed_under_step sys P ->
    forall t01 t0N,
      P t01 s1 ->
      t0N = t01 ++ t1N ->
      P t0N sN.
Proof.
  unfold closed_under_step.
  induction 1; intros; subst.
  - listy.
  - listy. eapply IHstar; eauto.
Qed.

Theorem invariant_induction (sys : trsys) (P : trace -> state -> Prop) :
    initially_holds sys P ->
    closed_under_step sys P ->
    is_invariant sys P.
Proof.
  unfold is_invariant; intros.
  eapply closed_under_step_star; eauto.
Qed.

Theorem invariant_implies (sys : trsys) :
    forall (P Q : trace -> state -> Prop),
    is_invariant sys P ->
    (forall t s, P t s -> Q t s) ->
    is_invariant sys Q.
Proof.
  unfold is_invariant. eauto.
Qed.

Theorem is_invariant_iff (sys : trsys) :
    forall (P : trace -> state -> Prop),
    is_invariant sys P <->
    (forall t s, reachable sys t s -> P t s).
Proof.
  intro P; split.
  + intros Hi t s Hreach. inv Hreach; eauto.
  + unfold is_invariant; intros. eauto with hints.
Qed.

(*
  We can also special-case the above machinery for
  proving invariants about the traces a program can generate.
*)

Inductive can_gen (sys : trsys) : trace -> Prop :=
| CanGen :
    forall s0 t sN,
      sys.(Init) s0 ->
      star sys.(Step) s0 t sN ->
      can_gen sys t.
Local Hint Constructors can_gen : hints.

Definition is_trace_invariant (sys : trsys) (P : trace -> Prop) :=
  forall s0,
    sys.(Init) s0 ->
    forall t sN,
      star sys.(Step) s0 t sN ->
      P t.

(*
  In practice, trace invariants are usually proved by first
  establishing a regular invariant that talks about the state and trace,
  and then "forgetting" the state part.
*)
Lemma invariant_implies_trace_invariant (sys : trsys) :
    forall (P : trace -> state -> Prop) (PT : trace -> Prop),
    is_invariant sys P ->
    (forall t s, P t s -> PT t) ->
    is_trace_invariant sys PT.
Proof.
  unfold is_invariant, is_trace_invariant.
  eauto.
Qed.

(*
  And of course, we can weaken trace invariants
  in the same way we can weaken regular invariants.
*)
Lemma trace_invariant_implies (sys : trsys) :
    forall (PT QT : trace -> Prop),
    is_trace_invariant sys PT ->
    (forall t, PT t -> QT t) ->
    is_trace_invariant sys QT.
Proof.
  unfold is_trace_invariant. eauto.
Qed.

Theorem is_trace_invariant_iff (sys : trsys) :
    forall (PT : trace -> Prop),
    is_trace_invariant sys PT <->
    (forall t, can_gen sys t -> PT t).
Proof.
  intro PT; split.
  + intros Hti t Hgen. inv Hgen; eauto.
  + unfold is_trace_invariant; intros. eauto with hints.
Qed.

(*
  Compiler correctness is about preserving observable behavior.
  Observable behavior includes both:
    (1) the traces a program can generate
    (2) a program's termination
  To avoid coinductive reasoning, we are a bit too strict in our
  definition of "has_behavior", but we err on the side of caution.
*)

Inductive behavior : Type :=
| beh_running (t: trace)
| beh_halted (t: trace).

Inductive has_behavior (sys : trsys) : behavior -> Prop :=
| hb_running :
    forall s0 t sN,
      sys.(Init) s0 ->
      star sys.(Step) s0 t sN ->
      has_behavior sys (beh_running t)
| hb_halted :
    forall s0 t sN,
      sys.(Init) s0 ->
      star sys.(Step) s0 t sN ->
      sys.(Final) sN ->
      has_behavior sys (beh_halted t).

Definition is_behavior_invariant (sys : trsys) (PB : behavior -> Prop) :=
  forall beh,
    has_behavior sys beh ->
    PB beh.

(*
  In practice, behavior invariants PB are usually proved by first
  establishing a regular invariant P that talks about the state and trace,
  and then ensuring P implies what's needed regarding termination.
*)
Lemma invariant_implies_behavior_invariant (sys : trsys) :
    forall (P : trace -> state -> Prop) (PB : behavior -> Prop),
    is_invariant sys P ->
    (forall t s, P t s -> PB (beh_running t)) ->
    (forall t s, P t s -> sys.(Final) s -> PB (beh_halted t)) ->
    is_behavior_invariant sys PB.
Proof.
  unfold is_invariant, is_behavior_invariant.
  intros P PB Hinv Hrun Hhalt beh Hbeh.
  invc Hbeh; eauto.
Qed.

(*
  And of course, we can weaken trace invariants
  in the same way we can weaken regular invariants.
*)
Lemma behavior_invariant_implies (sys : trsys) :
    forall (PB QB : behavior -> Prop),
    is_behavior_invariant sys PB ->
    (forall b, PB b -> QB b) ->
    is_behavior_invariant sys QB.
Proof.
  unfold is_behavior_invariant. eauto.
Qed.

(*
  Finally, we will want to exploit determinacy in some of our
  compiler correctness proofs later, so let's define it here.
*)
Record is_det_sys (sys : trsys) : Prop :=
  { InitDet :
      forall s0 s0',
        sys.(Init) s0 ->
        sys.(Init) s0' ->
        s0 = s0'
  ; StepDet :
      forall s1 t12 s2 t13 s3,
        sys.(Step) s1 t12 s2 ->
        sys.(Step) s1 t13 s3 ->
        t12 = t13 /\ s2 = s3
  }.

Definition has_init_state (sys: trsys) : Prop :=
  exists a0,
    sys.(Init) a0.

End LabeledTransitionSystems.


Section Simulation.

Variable label : Type.
Local Notation trace := (list label).
Local Notation beh := (behavior label).

Variable stateA : Type.
Variable stateB : Type.

(*
  A labeled transition system (LTS) A can simulate another LTS B
  if whenever B can exhibit some behavior beh,
  then A can also exhibit the same behavior beh.

  We think of this as intuitively meaning
  "A can do anything B can do" or
  "A's behaviors are a superset of B's behaviors".
*)
Definition can_simulate (sysA : trsys label stateA) (sysB : trsys label stateB) :=
  forall beh,
    has_behavior sysB beh ->
    has_behavior sysA beh.

(*
  If A can simulate B,
  then any invariant of A behaviors
  is also an invariant of B behaviors.
*)
Lemma can_simulate_preserves_spec :
  forall (sysA : trsys label stateA) (sysB : trsys label stateB),
    can_simulate sysA sysB ->
    forall (BI : beh -> Prop),
      is_behavior_invariant sysA BI ->
      is_behavior_invariant sysB BI.
Proof.
  unfold can_simulate, is_behavior_invariant.
  eauto.
Qed.

End Simulation.


Section Simulation_PreOrder.

Lemma can_simulate_refl :
  forall label state (sys : trsys label state),
    can_simulate sys sys.
Proof.
  unfold can_simulate; eauto.
Qed.

Lemma can_simulate_trans :
  forall label
    stateA (sysA : trsys label stateA)
    stateB (sysB : trsys label stateB)
    stateC (sysC : trsys label stateC),
    can_simulate sysA sysB ->
    can_simulate sysB sysC ->
    can_simulate sysA sysC.
Proof.
  unfold can_simulate; eauto.
Qed.

End Simulation_PreOrder.
Local Hint Resolve can_simulate_refl : hints.
Local Hint Resolve can_simulate_trans : hints.


Section TRSys_Equiv.

Variable label : Type.

Variable stateA : Type.
Variable sysA : trsys label stateA.

Variable stateB : Type.
Variable sysB : trsys label stateB.

Definition trsys_equiv :=
  can_simulate sysA sysB /\
  can_simulate sysB sysA.

Lemma trsys_equiv_ok :
  trsys_equiv ->
  forall beh,
    has_behavior sysA beh <->
    has_behavior sysB beh.
Proof.
  unfold trsys_equiv, can_simulate.
  intros [HeqAB HeqBA] beh; split; eauto.
Qed.

End TRSys_Equiv.


Section TRSys_Equiv_EqRel.

Variable label : Type.

Lemma trsys_equiv_refl :
  forall state (sys : trsys label state),
    trsys_equiv sys sys.
Proof.
  unfold trsys_equiv; intros.
  intuition; eauto with hints.
Qed.

Lemma trsys_equiv_sym :
  forall label
    stateA (sysA : trsys label stateA)
    stateB (sysB : trsys label stateB),
    trsys_equiv sysA sysB ->
    trsys_equiv sysB sysA.
Proof.
  unfold trsys_equiv; intros.
  intuition; eauto with hints.
Qed.

Lemma trsys_equiv_trans :
  forall label
    stateA (sysA : trsys label stateA)
    stateB (sysB : trsys label stateB)
    stateC (sysC : trsys label stateC),
    trsys_equiv sysA sysB ->
    trsys_equiv sysB sysC ->
    trsys_equiv sysA sysC.
Proof.
  unfold trsys_equiv; intros.
  intuition; eauto with hints.
Qed.

End TRSys_Equiv_EqRel.


Section SimulationRelations.

Variable label : Type.
Local Notation trace := (list label).
Local Notation beh := (behavior label).

Variable stateA : Type.
Variable sysA : trsys label stateA.

Variable stateB : Type.
Variable sysB : trsys label stateB.

Section LockstepSimulationRelations.

Variable match_states : stateA -> stateB -> Prop.

(*
  Forward simulations show that sysB can simulate sysA.
  This is often backward from what we want if we are
  trying to prove that some transformation preserves specs!
*)

Record fwdsim_lockstep : Prop :=
  { FSLS_MatchInit :
      forall a0,
        sysA.(Init) a0 ->
        exists b0,
          sysB.(Init) b0 /\
          match_states a0 b0
  ; FSLS_MatchStep :
      forall a1 b1,
        match_states a1 b1 ->
        forall a2 t,
          sysA.(Step) a1 t a2 ->
          exists b2,
            sysB.(Step) b1 t b2 /\
            match_states a2 b2
  ; FSLS_MatchFinal :
      forall aN bN,
        match_states aN bN ->
        sysA.(Final) aN -> sysB.(Final) bN }.

Theorem fwdsim_lockstep_star :
  forall (SIM : fwdsim_lockstep) a1 t1N aN,
    star sysA.(Step) a1 t1N aN ->
    forall b1,
    match_states a1 b1 ->
    exists bN,
      star sysB.(Step) b1 t1N bN /\
      match_states aN bN.
Proof.
  intros SIM a1 t1N aN HstarA.
  induction HstarA; intros b1 Hmatch1.
  - exists b1; split; eauto. ee.
  - edestruct SIM.(FSLS_MatchStep) as [b2 [HstepB Hmatch2]]; eauto.
    edestruct IHHstarA as [bN [HstarB HmatchN]]; eauto.
    exists bN; split; eauto. ee.
Qed.

Theorem fwdsim_lockstep_can_sim :
  forall (SIM : fwdsim_lockstep),
    can_simulate sysB sysA.
Proof.
  unfold can_simulate.
  intros SIM beh HbehA.
  invc HbehA.
  + edestruct SIM.(FSLS_MatchInit) as [b0 [HinitB Hmatch0]]; eauto.
    edestruct fwdsim_lockstep_star as [bN [HstarB HmatchN]]; eauto.
    ee.
  + edestruct SIM.(FSLS_MatchInit) as [b0 [HinitB Hmatch0]]; eauto.
    edestruct fwdsim_lockstep_star as [bN [HstarB HmatchN]]; eauto.
    ee. eapply SIM.(FSLS_MatchFinal); eauto.
Qed.

(*
  Backward simulations show that sysA can simulate sysB.
  This is often what we need in order to prove that some
  transformation preserves specs.
*)

Record bwdsim_lockstep : Prop :=
  { BSLS_MatchInit :
      forall b0,
        sysB.(Init) b0 ->
        exists a0,
          sysA.(Init) a0 /\
          match_states a0 b0
  ; BSLS_MatchStep :
      forall a1 b1,
        match_states a1 b1 ->
        forall b2 t,
          sysB.(Step) b1 t b2 ->
          exists a2,
            sysA.(Step) a1 t a2 /\
            match_states a2 b2
  ; BSLS_MatchFinal :
      forall aN bN,
        match_states aN bN ->
        sysB.(Final) bN -> sysA.(Final) aN }.

Theorem bwdsim_lockstep_star :
  forall (SIM : bwdsim_lockstep) b1 t1N bN,
    star sysB.(Step) b1 t1N bN ->
    forall a1,
    match_states a1 b1 ->
    exists aN,
      star sysA.(Step) a1 t1N aN /\
      match_states aN bN.
Proof.
  intros SIM a1 t1N bN HstarB.
  induction HstarB; intros a1 Hmatch1.
  - exists a1; split; eauto. ee.
  - edestruct SIM.(BSLS_MatchStep) as [a2 [HstepA Hmatch2]]; eauto.
    edestruct IHHstarB as [aN [HstarA HmatchN]]; eauto.
    exists aN; split; eauto. ee.
Qed.

Theorem bwdsim_lockstep_can_sim :
  forall (SIM : bwdsim_lockstep),
    can_simulate sysA sysB.
Proof.
  unfold can_simulate.
  intros SIM beh HbehB.
  invc HbehB.
  + edestruct SIM.(BSLS_MatchInit) as [a0 [HinitA Hmatch0]]; eauto.
    edestruct bwdsim_lockstep_star as [aN [HstarA HmatchN]]; eauto.
    ee.
  + edestruct SIM.(BSLS_MatchInit) as [a0 [HinitA Hmatch0]]; eauto.
    edestruct bwdsim_lockstep_star as [aN [HstarA HmatchN]]; eauto.
    ee. eapply SIM.(BSLS_MatchFinal); eauto.
Qed.

Theorem lockstep_equiv :
  fwdsim_lockstep ->
  bwdsim_lockstep ->
  trsys_equiv sysA sysB.
Proof.
  unfold trsys_equiv.
  intros FSIM BSIM; split.
  - apply bwdsim_lockstep_can_sim; auto.
  - apply fwdsim_lockstep_can_sim; auto.
Qed.

(*
  In practice, it's often much easier to prove forward simulations.
  But there's a trick to get a backward simulation from a forward simulation
  when the target system is deterministic and the simulation relation
  guarantees that non-final source states are unstuck.
*)

Definition match_states_progress :=
  forall a b,
    match_states a b ->
    can_step sysA.(Step) a \/
    sysA.(Final) a.

Lemma det_trick_fwdsim_bwdsim_lockstep :
  is_det_sys sysB ->
  has_init_state sysA ->
  match_states_progress ->
  fwdsim_lockstep ->
  bwdsim_lockstep.
Proof.
  unfold has_init_state, match_states_progress.
  intros Hdet [a0 Ha0] Progress SIM.
  destruct Hdet as [InitDet StepDet].
  destruct SIM as [HinitA HstepA HfinalA].
  ee.
  - intros b0 Hinitb0.
    edestruct HinitA as [b0' [Hinitb0' Hmatch0]]; eauto.
    replace b0 with b0' in *; eauto.
  - intros a1 b1 Hmatch b2 t12 HstepB1.
    edestruct Progress as [Hcan_step | Hfinal]; eauto.
    + destruct Hcan_step as [t12' [a2 Hstepa12]].
      edestruct HstepA as [b2' [HstepB1' Hmatch']]; eauto.
      edestruct StepDet.
        apply HstepB1.
        apply HstepB1'.
      subst; eauto.
    + edestruct sysB.(FinalNoStep); eauto.
  - intros aN bN Hmatch HfinalB.
    edestruct Progress as [Hcan_step | Hfinal]; eauto.
    destruct Hcan_step as [tNZ [aZ HstepaNZ]].
    edestruct HstepA as [bZ [HstepbNZ HmatchZ]]; eauto.
    edestruct sysB.(FinalNoStep); eauto.
Qed.

(* TODO name should include "fwdsim" *)
Theorem det_lockstep_equiv :
  is_det_sys sysB ->
  has_init_state sysA ->
  match_states_progress ->
  fwdsim_lockstep ->
  trsys_equiv sysA sysB.
Proof.
  intros.
  apply lockstep_equiv; auto.
  apply det_trick_fwdsim_bwdsim_lockstep; auto.
Qed.

End LockstepSimulationRelations.

(*
  The 1-1 step matching in the "lockstep" forward and backward simulations
  above can only be used to verify optimizations or translations that maintain
  the exact number of steps used to generate the same trace and each step
  of source and target must produce the same trace events (labels).

  Below we'll show that the lockstep definitions are just special cases
  of more general simulation relations.
*)

Section AddingSimulationRelations.

(*
  First we'll consider simulations that allow "adding" steps.
*)

Variable match_states : stateA -> stateB -> Prop.

(*
  Forward simulations show that sysB can simulate sysA.
  This is often backward from what we want if we are
  trying to prove that some transformation preserves specs!
*)

Record fwdsim_add : Prop :=
  { FSA_MatchInit :
      forall a0,
        sysA.(Init) a0 ->
        exists b0,
          sysB.(Init) b0 /\
          match_states a0 b0
  ; FSA_MatchStep :
      forall a1 b1,
        match_states a1 b1 ->
        forall a2 t,
          sysA.(Step) a1 t a2 ->
          exists b2,
            plus sysB.(Step) b1 t b2 /\
            match_states a2 b2
  ; FSA_MatchFinal :
      forall aN bN,
        match_states aN bN ->
        sysA.(Final) aN -> sysB.(Final) bN }.

Theorem fwdsim_add_star :
  forall (SIM : fwdsim_add) a1 t1N aN,
    star sysA.(Step) a1 t1N aN ->
    forall b1,
    match_states a1 b1 ->
    exists bN,
      star sysB.(Step) b1 t1N bN /\
      match_states aN bN.
Proof.
  intros SIM a1 t1N aN HstarA.
  induction HstarA; intros b1 Hmatch1.
  - exists b1; split; eauto. ee.
  - edestruct SIM.(FSA_MatchStep) as [b2 [HstepB Hmatch2]]; eauto.
    edestruct IHHstarA as [bN [HstarB HmatchN]]; eauto.
    exists bN; split; eauto.
    eapply plus_star_star; eauto.
Qed.

Theorem fwdsim_add_can_sim :
  forall (SIM : fwdsim_add),
    can_simulate sysB sysA.
Proof.
  unfold can_simulate.
  intros SIM beh HbehA.
  invc HbehA.
  + edestruct SIM.(FSA_MatchInit) as [b0 [HinitB Hmatch0]]; eauto.
    edestruct fwdsim_add_star as [bN [HstarB HmatchN]]; eauto.
    ee.
  + edestruct SIM.(FSA_MatchInit) as [b0 [HinitB Hmatch0]]; eauto.
    edestruct fwdsim_add_star as [bN [HstarB HmatchN]]; eauto.
    ee. eapply SIM.(FSA_MatchFinal); eauto.
Qed.

(*
  Backward simulations show that sysA can simulate sysB.
  This is often what we need in order to prove that some
  transformation preserves specs.
*)

Record bwdsim_add : Prop :=
  { BSA_MatchInit :
      forall b0,
        sysB.(Init) b0 ->
        exists a0,
          sysA.(Init) a0 /\
          match_states a0 b0
  ; BSA_MatchStep :
      forall a1 b1,
        match_states a1 b1 ->
        forall b2 t,
          sysB.(Step) b1 t b2 ->
          exists a2,
            plus sysA.(Step) a1 t a2 /\
            match_states a2 b2
  ; BSA_MatchFinal :
      forall aN bN,
        match_states aN bN ->
        sysB.(Final) bN -> sysA.(Final) aN }.

Theorem bwdsim_add_star :
  forall (SIM : bwdsim_add) b1 t1N bN,
    star sysB.(Step) b1 t1N bN ->
    forall a1,
    match_states a1 b1 ->
    exists aN,
      star sysA.(Step) a1 t1N aN /\
      match_states aN bN.
Proof.
  intros SIM a1 t1N bN HstarB.
  induction HstarB; intros a1 Hmatch1.
  - exists a1; split; eauto. ee.
  - edestruct SIM.(BSA_MatchStep) as [a2 [HstepA Hmatch2]]; eauto.
    edestruct IHHstarB as [aN [HstarA HmatchN]]; eauto.
    exists aN; split; eauto.
    eapply plus_star_star; eauto.
Qed.

Theorem bwdsim_add_can_sim :
  forall (SIM : bwdsim_add),
    can_simulate sysA sysB.
Proof.
  unfold can_simulate.
  intros SIM beh HbehB.
  invc HbehB.
  + edestruct SIM.(BSA_MatchInit) as [a0 [HinitA Hmatch0]]; eauto.
    edestruct bwdsim_add_star as [aN [HstarA HmatchN]]; eauto.
    ee.
  + edestruct SIM.(BSA_MatchInit) as [a0 [HinitA Hmatch0]]; eauto.
    edestruct bwdsim_add_star as [aN [HstarA HmatchN]]; eauto.
    ee. eapply SIM.(BSA_MatchFinal); eauto.
Qed.

(* TODO make bwdsim_add a special case *)

Record bwdsim_add2 : Prop :=
  { BSA2_MatchInit :
      forall b0,
        sysB.(Init) b0 ->
        exists a0,
          sysA.(Init) a0 /\
          match_states a0 b0
  ; BSA2_MatchStep :
      forall a1 b1,
        match_states a1 b1 ->
        forall b2 t,
          sysB.(Step) b1 t b2 ->
          exists a2,
            plus sysA.(Step) a1 t a2 /\
            match_states a2 b2
  ; BSA2_MatchFinal :
      forall aN bN,
        match_states aN bN ->
        sysB.(Final) bN ->
        (exists aZ,
          star sysA.(Step) aN [] aZ /\
          sysA.(Final) aZ) }.

Theorem bwdsim_add2_star :
  forall (SIM : bwdsim_add2) b1 t1N bN,
    star sysB.(Step) b1 t1N bN ->
    forall a1,
    match_states a1 b1 ->
    exists aN,
      star sysA.(Step) a1 t1N aN /\
      match_states aN bN.
Proof.
  intros SIM a1 t1N bN HstarB.
  induction HstarB; intros a1 Hmatch1.
  - exists a1; split; eauto. ee.
  - edestruct SIM.(BSA2_MatchStep) as [a2 [HstepA Hmatch2]]; eauto.
    edestruct IHHstarB as [aN [HstarA HmatchN]]; eauto.
    exists aN; split; eauto.
    eapply plus_star_star; eauto.
Qed.

Theorem bwdsim_add2_can_sim :
  forall (SIM : bwdsim_add2),
    can_simulate sysA sysB.
Proof.
  unfold can_simulate.
  intros SIM beh HbehB.
  invc HbehB.
  + edestruct SIM.(BSA2_MatchInit) as [a0 [HinitA Hmatch0]]; eauto.
    edestruct bwdsim_add2_star as [aN [HstarA HmatchN]]; eauto.
    ee.
  + edestruct SIM.(BSA2_MatchInit) as [a0 [HinitA Hmatch0]]; eauto.
    edestruct bwdsim_add2_star as [aN [HstarA HmatchN]]; eauto.
    edestruct SIM.(BSA2_MatchFinal) as [aZ [HstarZ HfinalZ]]; eauto.
    assert (star sysA.(Step) a0 t aZ).
      eapply star_trans; eauto. listy.
    ee.
Qed.

End AddingSimulationRelations.

Section DroppingSimulationRelations.

(*
  Second we'll consider simulations that allow "dropping" steps.

  The most important change is that we generalize the "match_states" relation
  to take an nat index. Our simulation relations will be allowed to
  'delay stepping' if states match at an index greater than 0.
*)

Variable match_states : nat -> stateA -> stateB -> Prop.

(*
  Forward simulations show that sysB can simulate sysA.
  This is often backward from what we want if we are
  trying to prove that some transformation preserves specs!
*)

Record fwdsim_drop : Prop :=
  { FSD_MatchInit :
      forall a0,
        sysA.(Init) a0 ->
        exists n0 b0,
          sysB.(Init) b0 /\
          match_states n0 a0 b0
  ; FSD_MatchStep :
      forall n1 a1 b1,
        match_states n1 a1 b1 ->
        forall a2 t,
          sysA.(Step) a1 t a2 ->
          (exists n2 b2, sysB.(Step) b1 t b2 /\ match_states n2 a2 b2) \/
          (t = [] /\ exists n, n < n1 /\ match_states n a2 b1)
  ; FSD_MatchFinal :
      forall nN aN bN,
        match_states nN aN bN ->
        sysA.(Final) aN -> sysB.(Final) bN }.

Theorem fwdsim_drop_star :
  forall (SIM : fwdsim_drop) a1 t1N aN,
    star sysA.(Step) a1 t1N aN ->
    forall n1 b1,
    match_states n1 a1 b1 ->
    exists nN bN,
      star sysB.(Step) b1 t1N bN /\
      match_states nN aN bN.
Proof.
  intros SIM a1 t1N aN HstarA.
  induction HstarA; intros n1 b1 Hmatch1; subst.
  - exists n1; exists b1; split; eauto. ee.
  - edestruct SIM.(FSD_MatchStep) as [Hlock | Hdelay]; eauto.
    + destruct Hlock as [n2 [b2 [Hstep Hmatch]]].
      edestruct IHHstarA as [nN [bN [HstarB HmatchN]]]; eauto.
      exists nN; exists bN; split; eauto. ee.
    + destruct Hdelay as [Ht [n [Hlt Hmatch]]]. subst; simpl.
      eapply IHHstarA; eauto.
Qed.

Theorem fwdsim_drop_can_sim :
  forall (SIM : fwdsim_drop),
    can_simulate sysB sysA.
Proof.
  unfold can_simulate.
  intros SIM beh HbehA.
  invc HbehA.
  + edestruct SIM.(FSD_MatchInit) as [n0 [b0 [HinitB Hmatch0]]]; eauto.
    edestruct fwdsim_drop_star as [nN [bN [HstarB HmatchN]]]; eauto.
    ee.
  + edestruct SIM.(FSD_MatchInit) as [n0 [b0 [HinitB Hmatch0]]]; eauto.
    edestruct fwdsim_drop_star as [nN [bN [HstarB HmatchN]]]; eauto.
    ee. eapply SIM.(FSD_MatchFinal); eauto.
Qed.

(*
  Backward simulations show that sysA can simulate sysB.
  This is often what we need in order to prove that some
  transformation preserves specs.
*)

Record bwdsim_drop : Prop :=
  { BSD_MatchInit :
      forall b0,
        sysB.(Init) b0 ->
        exists n0 a0,
          sysA.(Init) a0 /\
          match_states n0 a0 b0
  ; BSD_MatchStep :
      forall n1 a1 b1,
        match_states n1 a1 b1 ->
        forall b2 t,
          sysB.(Step) b1 t b2 ->
          (exists n2 a2, sysA.(Step) a1 t a2 /\ match_states n2 a2 b2) \/
          (t = [] /\ exists n, n < n1 /\ match_states n a1 b2)
  ; BSD_MatchFinal :
      forall nN aN bN,
        match_states nN aN bN ->
        sysB.(Final) bN -> sysA.(Final) aN }.

Theorem bwdsim_drop_star :
  forall (SIM : bwdsim_drop) b1 t1N bN,
    star sysB.(Step) b1 t1N bN ->
    forall n1 a1,
    match_states n1 a1 b1 ->
    exists nN aN,
      star sysA.(Step) a1 t1N aN /\
      match_states nN aN bN.
Proof.
  intros SIM b1 t1N bN HstarB.
  induction HstarB; intros n1 a1 Hmatch1; subst.
  - exists n1; exists a1; split; eauto. ee.
  - edestruct SIM.(BSD_MatchStep) as [Hlock | Hdelay]; eauto.
    + destruct Hlock as [n2 [a2 [Hstep Hmatch]]].
      edestruct IHHstarB as [nN [aN [HstarA HmatchN]]]; eauto.
      exists nN; exists aN; split; eauto. ee.
    + destruct Hdelay as [Ht [n [Hlt Hmatch]]]. subst; simpl.
      eapply IHHstarB; eauto.
Qed.

Theorem bwdsim_drop_can_sim :
  forall (SIM : bwdsim_drop),
    can_simulate sysA sysB.
Proof.
  unfold can_simulate.
  intros SIM beh HbehB.
  invc HbehB.
  + edestruct SIM.(BSD_MatchInit) as [n0 [a0 [HinitA Hmatch0]]]; eauto.
    edestruct bwdsim_drop_star as [nN [aN [HstarA HmatchN]]]; eauto.
    ee.
  + edestruct SIM.(BSD_MatchInit) as [n0 [a0 [HinitA Hmatch0]]]; eauto.
    edestruct bwdsim_drop_star as [nN [aN [HstarA HmatchN]]]; eauto.
    ee. eapply SIM.(BSD_MatchFinal); eauto.
Qed.

End DroppingSimulationRelations.

Section ForwardBackward.

Definition single_events label state (sys : trsys label state) : Prop :=
  forall s1 t s2,
    sys.(Step) s1 t s2 ->
    List.length t <= 1.

Inductive ms_msi (MS : stateA -> stateB -> Prop) : nat -> stateA -> stateB -> Prop :=
| MSMSI_starn :
    forall tr12 sa1 sa2 n1 sb1 sb1' n2 sb2' sb2,
      sysA.(Step) sa1 tr12 sa2 ->
      starn sysB.(Step) n1 sb1 [] sb1' ->
      sysB.(Step) sb1' tr12 sb2' ->
      starn sysB.(Step) n2 sb2' [] sb2 ->
      MS sa2 sb2 ->
      ms_msi MS n1 sa1 sb1
| MSMSI_final :
    forall sa n sb sb',
      sysA.(Final) sa ->
      starn sysB.(Step) n sb [] sb' ->
      MS sa sb' ->
      ms_msi MS n sa sb.

Lemma fwdsim_add_bwdsim_drop_diagram :
  is_det_sys sysB ->
  single_events sysA ->
  forall (MS : stateA -> stateB -> Prop),
    match_states_progress MS ->
    fwdsim_add MS ->
    forall (n1 : nat) (a1 : stateA) (b1 : stateB),
      ms_msi MS n1 a1 b1 ->
      forall (b2 : stateB) (t : trace),
        Step sysB b1 t b2 ->
        (exists (n2 : nat) (a2 : stateA), Step sysA a1 t a2 /\ ms_msi MS n2 a2 b2)
        \/ (t = [] /\ (exists n : nat, n < n1 /\ ms_msi MS n a1 b2)).
Proof.
  intros Hdet Hsingle MS Progress SIM.
  destruct Hdet as [InitDet StepDet].
  destruct SIM as [_ STEP FINAL].
  intros n1 a1 b1 Hmatch1. induction Hmatch1.
  - intros b2 t12 HstepB12.
    invc H0.
    + left.
      eapply StepDet in H1. 2 : apply HstepB12. destruct H1; subst.
      edestruct Progress as [Hcan_step | Hfinal]; eauto.
      * destruct Hcan_step as [t23 [sa3 HstepA23]].
        edestruct STEP as [sb3 [HplusB23 Hmatch3]]; eauto.
        eapply plus_single_event_inv in HplusB23; eauto.
        destruct HplusB23 as [s1' [s2' [Hstar1' [Hstep12 Hstar2']]]].
        apply star_starn in Hstar1'. destruct Hstar1' as [nL Hstarn1].
        apply star_starn in Hstar2'. destruct Hstar2' as [nR Hstarn2].
        exists (n2 + nL); exists sa2; split; eauto.
        ee. eapply starn_trans; eauto.
      * exists n2; exists sa2; split; eauto.
        eapply MSMSI_final; eauto.
    + symmetry in H6. apply app_eq_nil in H6. invc H6.
      eapply StepDet in H4. 2 : apply HstepB12. destruct H4; subst.
      right; split; auto.
      exists n; split; auto.
      ee.
  - intros b2 t12 HstepB12. invc H0.
    + edestruct (sysB.(FinalNoStep) sb'); eauto.
    + eapply StepDet in H2. 2 : apply HstepB12. invc H2.
      symmetry in H4. apply app_eq_nil in H4. invc H4.
      right; split; eauto.
      exists n0; split; auto.
      eapply MSMSI_final; eauto.
Qed.

Lemma ms_msi_final_or_step :
  forall MS n a b,
    ms_msi MS n a b ->
    Final sysA a \/ can_step sysB.(Step) b.
Proof.
  intros MS n a b Hmsi.
  invc Hmsi; auto. right.
  apply starn_star in H0.
  eapply plus_back in H1; eauto.
  eapply plus_can_step; eauto.
Qed.

Lemma det_trick_fwdsim_add_bwdsim_drop :
  is_det_sys sysB ->
  has_init_state sysA ->
  single_events sysA ->
  forall (MS : stateA -> stateB -> Prop),
    match_states_progress MS ->
    fwdsim_add MS ->
    bwdsim_drop (ms_msi MS).
Proof.
  unfold has_init_state.
  intros Hdet [a0 Ha0] Hsingle MS Progress SIM.
  destruct Hdet as [InitDet StepDet].
  destruct SIM as [INIT STEP FINAL].
  ee.
  - intros b0 Hb0.
    edestruct INIT as [b0' [Hb0' Hmatch0]]; eauto.
    eapply InitDet in Hb0. 2 : apply Hb0'. subst.
    edestruct Progress; eauto.
    + destruct H as [t01 [a1 HstepA]].
      edestruct STEP as [b1 [HplusB Hmatch1]]; eauto.
      eapply plus_single_event_inv in HplusB; eauto.
      destruct HplusB as [s1' [s2' [Hstar1' [Hstep12 Hstar2']]]].
      apply star_starn in Hstar1'. destruct Hstar1' as [n1 Hstarn1].
      apply star_starn in Hstar2'. destruct Hstar2' as [n2 Hstarn2].
      exists n1; exists a0; split; eauto.
      ee.
    + exists 0; exists a0; split; auto.
      eapply MSMSI_final; eauto. ee.
  - apply fwdsim_add_bwdsim_drop_diagram; auto. ee. ee.
  - intros nN aN bN Hmatch HfinalB.
    apply ms_msi_final_or_step in Hmatch.
    intuition; auto. invc H. break_up_hyps.
    edestruct sysB.(FinalNoStep); eauto.
Qed.

Theorem det_fwdsim_add_equiv :
  is_det_sys sysB ->
  has_init_state sysA ->
  single_events sysA ->
  forall (MS : stateA -> stateB -> Prop),
    match_states_progress MS ->
    fwdsim_add MS ->
    trsys_equiv sysA sysB.
Proof.
  unfold trsys_equiv.
  intros; split.
  - eapply bwdsim_drop_can_sim; eauto.
    eapply det_trick_fwdsim_add_bwdsim_drop; eauto.
  - eapply fwdsim_add_can_sim; eauto.
Qed.

Require Import Arith Wf.

Definition match_states_progress' (MSI : nat -> stateA -> stateB -> Prop) :=
  forall n a b,
    MSI n a b ->
    can_step sysA.(Step) a \/
    sysA.(Final) a.

Inductive msi_ms (MSI : nat -> stateA -> stateB -> Prop) : stateA -> stateB -> Prop :=
| MSIMS :
    forall n a b,
      MSI n a b ->
      msi_ms MSI a b.

Lemma fwdsim_drop_bwdsim_add_diagram :
    is_det_sys sysB ->
    forall (MSI : nat -> stateA -> stateB -> Prop),
      match_states_progress' MSI ->
      fwdsim_drop MSI ->
      forall (a1 : stateA) (b1 : stateB),
        msi_ms MSI a1 b1 ->
        forall (b2 : stateB) (t : trace),
          Step sysB b1 t b2 ->
          exists a2 : stateA, plus (Step sysA) a1 t a2 /\ msi_ms MSI a2 b2.
Proof.
  intros Hdet MSI Progress SIM.
  destruct Hdet as [InitDet StepDet].
  destruct SIM as [_ STEP FINAL].
  intros a1 b1 Hmatch1. destruct Hmatch1 as [n1 a1 b1 Hmatch1].
  revert a1 b1 Hmatch1.
  induction n1 as [i IHi] using (well_founded_induction lt_wf).
  intros a1 b1 Hmatch1 b2 t12 HstepB12.
  edestruct Progress as [Hcan_step | Hfinal]; eauto.
  - destruct Hcan_step as [t12' [a2 HstepA12]].
    edestruct STEP as [HstepsB | HwaitsB]; eauto.
    + destruct HstepsB as [n2 [b2' [HstepB12' Hmatch2]]].
      eapply StepDet in HstepB12.
        2 : apply HstepB12'. destruct HstepB12; subst.
      exists a2; split; eauto; repeat ee. listy.
    + destruct HwaitsB as [Hsilent [n [Hlt Hmsi]]]; subst.
      edestruct IHi as [a2' [HplusA Hmatch2]]; eauto.
      exists a2'; split; eauto.
      apply plus_star in HplusA; ee.
  - edestruct sysB.(FinalNoStep); eauto.
Qed.

Lemma fwdsim_drop_bwdsim_add_final :
  is_det_sys sysB ->
  forall (MSI : nat -> stateA -> stateB -> Prop),
    match_states_progress' MSI ->
    fwdsim_drop MSI ->
    forall (aN : stateA) (bN : stateB),
      msi_ms MSI aN bN ->
      Final sysB bN ->
      exists aZ : stateA,
        star (Step sysA) aN [] aZ /\
        Final sysA aZ.
Proof.
  intros Hdet MSI Progress SIM.
  destruct Hdet as [InitDet StepDet].
  destruct SIM as [_ STEP FINAL].
  intros aN bN HmatchN.
  destruct HmatchN as [nN aN bN HmatchN].
  revert aN bN HmatchN.
  induction nN as [i IHi] using (well_founded_induction lt_wf).
  intros aN bN HmatchN HfinalBN.
  edestruct Progress as [Hcan_step | Hfinal]; eauto.
  2 : {
    exists aN; split; eauto. ee.
  }
  destruct Hcan_step as [tNZ [aZ HstepANZ]].
  edestruct STEP as [HstepsB | HwaitsB]; eauto.
  - destruct HstepsB as [nZ [bNZ [HstepBNZ Hmatch2]]].
    edestruct sysB.(FinalNoStep); eauto.
  - destruct HwaitsB as [Hsilent [nZ [Hlt HmatchZ]]]; subst.
    eapply IHi in HmatchZ; eauto.
    destruct HmatchZ as [aZ' [HstarZ' HfinalZ']].
    exists aZ'; split; eauto. ee.
Qed.

Lemma det_trick_fwdsim_drop_bwdsim_add :
  is_det_sys sysB ->
  has_init_state sysA ->
  single_events sysA ->
  forall (MSI : nat -> stateA -> stateB -> Prop),
    match_states_progress' MSI ->
    fwdsim_drop MSI ->
    bwdsim_add2 (msi_ms MSI).
Proof.
  unfold has_init_state.
  intros Hdet [a0 Ha0] Hsingle MSI Progress SIM.
  destruct Hdet as [InitDet StepDet].
  destruct SIM as [INIT STEP FINAL].
  ee.
  - intros b0 Hb0.
    edestruct INIT as [n [b0' [Hb0' Hmatch]]]; eauto.
    eapply InitDet in Hb0. 2 : apply Hb0'. subst.
    exists a0; split; eauto. ee.
  - eapply fwdsim_drop_bwdsim_add_diagram; eauto. ee. ee.
  - eapply fwdsim_drop_bwdsim_add_final; eauto. ee. ee.
Qed.

Theorem det_fwdsim_drop_equiv :
  is_det_sys sysB ->
  has_init_state sysA ->
  single_events sysA ->
  forall (MSI : nat -> stateA -> stateB -> Prop),
    match_states_progress' MSI ->
    fwdsim_drop MSI ->
    trsys_equiv sysA sysB.
Proof.
  unfold trsys_equiv.
  intros; split.
  - eapply bwdsim_add2_can_sim; eauto.
    eapply det_trick_fwdsim_drop_bwdsim_add; eauto.
  - eapply fwdsim_drop_can_sim; eauto.
Qed.

End ForwardBackward.


Section GeneralSimulationRelations.

(*
  The 1-1 step matching in the "lockstep" forward and backward simulations
  above can not be used to verify optimizations or translations that change
  the number of steps used to generate the same trace.

  Next we'll show that the lockstep definitions are just special cases
  of more general simulation relations.

  The most important change is that we generalize the "match_states" relation
  to take an nat index. Our simulation relations will be allowed to
  'delay matching' if states match at an index greater than 0.
*)

Variable match_states : nat -> stateA -> stateB -> Prop.

(* 
Record fwdsim : Prop :=
  { FS_MatchInit :
      forall a0,
        sysA.(Init) a0 ->
        exists i b0,
          sysB.(Init) b0 /\
          match_states i a0 b0
  ; FS_MatchStep :
      forall i a1 b1,
        match_states i a1 b1 ->
        forall a2 t,
          sysA.(Step) a1 t a2 ->
          exists i' b2,
             star sysB.(Step) b1 t b2
          /\ match_states i' a2 b2
  ; FS_MatchFinal :
      forall i aN bN,
        match_states i aN bN ->
        sysA.(Final) aN -> sysB.(Final) bN }.

Theorem fwdsim_star :
  forall (SIM : fwdsim) a1 t1N aN,
    star sysA.(Step) a1 t1N aN ->
    forall i b1,
    match_states i a1 b1 ->
    exists i' bN,
        star sysB.(Step) b1 t1N bN /\
        match_states i' aN bN.
Proof.
  intros SIM a1 t1N aN HstarA.
  induction HstarA; intros i b1 Hmatch1; subst.
  - exists i; exists b1; split; eauto. ee.
  - edestruct SIM.(FS_MatchStep) as [i2 [b2 [HstarB Hmatch2]]]; eauto.
    edestruct IHHstarA as [iN [bN [Hstar2B HmatchN]]]; eauto;
        exists iN; exists bN; split; eauto.
    eapply star_trans; eauto.
Qed.

Theorem fwdsim_can_sim :
  forall (SIM : fwdsim),
    can_simulate sysB sysA.
Proof.
  unfold can_simulate.
  intros SIM beh HbehA.
  invc HbehA.
  + edestruct SIM.(FS_MatchInit) as [n0 [b0 [HinitB Hmatch0]]]; eauto.
    edestruct fwdsim_star as [nN [bN [HstarB HmatchN]]]; eauto.
    ee.
  + edestruct SIM.(FS_MatchInit) as [n0 [b0 [HinitB Hmatch0]]]; eauto.
    edestruct fwdsim_star as [nN [bN [HstarB HmatchN]]]; eauto.
    ee. eapply SIM.(FS_MatchFinal); eauto.
Qed.
*)

Record fwdsim : Prop :=
  { FS_MatchInit :
      forall a0,
        sysA.(Init) a0 ->
        exists i b0,
          sysB.(Init) b0 /\
          match_states i a0 b0
  ; FS_MatchStep :
      forall i a1 b1,
        match_states i a1 b1 ->
        forall a2 t,
          sysA.(Step) a1 t a2 ->
          exists i' b2,
             (plus sysB.(Step) b1 t b2 \/ (star sysB.(Step) b1 t b2 /\ i' < i))
          /\ match_states i' a2 b2
  ; FS_MatchFinal :
      forall i aN bN,
        match_states i aN bN ->
        sysA.(Final) aN -> sysB.(Final) bN }.

Theorem fwdsim_star :
  forall (SIM : fwdsim) a1 t1N aN,
    star sysA.(Step) a1 t1N aN ->
    forall i b1,
    match_states i a1 b1 ->
    exists i' bN,
        star sysB.(Step) b1 t1N bN /\
        match_states i' aN bN.
Proof.
  intros SIM a1 t1N aN HstarA.
  induction HstarA; intros i b1 Hmatch1; subst.
  - exists i; exists b1; split; eauto. ee.
  - edestruct SIM.(FS_MatchStep) as [i2 [b2 [HB Hmatch2]]]; eauto.
    destruct HB as [HplusB | [Hstar1B Hlt]];
      edestruct IHHstarA as [iN [bN [Hstar2B HmatchN]]]; eauto;
        exists iN; exists bN; split; eauto.
    + eapply plus_star_star; eauto.
    + eapply star_trans; eauto.
Qed.

Theorem fwdsim_can_sim :
  forall (SIM : fwdsim),
    can_simulate sysB sysA.
Proof.
  unfold can_simulate.
  intros SIM beh HbehA.
  invc HbehA.
  + edestruct SIM.(FS_MatchInit) as [n0 [b0 [HinitB Hmatch0]]]; eauto.
    edestruct fwdsim_star as [nN [bN [HstarB HmatchN]]]; eauto.
    ee.
  + edestruct SIM.(FS_MatchInit) as [n0 [b0 [HinitB Hmatch0]]]; eauto.
    edestruct fwdsim_star as [nN [bN [HstarB HmatchN]]]; eauto.
    ee. eapply SIM.(FS_MatchFinal); eauto.
Qed.

(*
  Backward simulations show that sysA can simulate sysB.
  This is often what we need in order to prove that some
  transformation preserves specs.
*)

Record bwdsim : Prop :=
  { BS_MatchInit :
      forall b0,
        sysB.(Init) b0 ->
        exists i a0,
          sysA.(Init) a0 /\
          match_states i a0 b0
  ; BS_MatchStep :
      forall i a1 b1,
        match_states i a1 b1 ->
        forall b2 t,
          sysB.(Step) b1 t b2 ->
          exists i' a2,
             (plus sysA.(Step) a1 t a2 \/ (star sysA.(Step) a1 t a2 /\ i' < i))
          /\ match_states i' a2 b2
  ; BS_MatchFinal :
      forall i aN bN,
        match_states i aN bN ->
        sysB.(Final) bN -> sysA.(Final) aN }.

Theorem bwdsim_star :
  forall (SIM : bwdsim) b1 t1N bN,
    star sysB.(Step) b1 t1N bN ->
    forall i a1,
    match_states i a1 b1 ->
    exists i' aN,
        star sysA.(Step) a1 t1N aN /\
        match_states i' aN bN.
Proof.
  intros SIM b1 t1N bN HstarB.
  induction HstarB; intros i a1 Hmatch1; subst.
  - exists i; exists a1; split; eauto. ee.
  - edestruct SIM.(BS_MatchStep) as [i2 [a2 [HA Hmatch2]]]; eauto.
    destruct HA as [HplusA | [Hstar1A Hlt]];
      edestruct IHHstarB as [iN [aN [Hstar2A HmatchN]]]; eauto;
        exists iN; exists aN; split; eauto.
    + eapply plus_star_star; eauto.
    + eapply star_trans; eauto.
Qed.

Theorem bwdsim_can_sim :
  forall (SIM : bwdsim),
    can_simulate sysA sysB.
Proof.
  unfold can_simulate.
  intros SIM beh HbehB.
  invc HbehB.
  + edestruct SIM.(BS_MatchInit) as [n0 [a0 [HinitA Hmatch0]]]; eauto.
    edestruct bwdsim_star as [nN [aN [HstarA HmatchN]]]; eauto.
    ee.
  + edestruct SIM.(BS_MatchInit) as [n0 [a0 [HinitA Hmatch0]]]; eauto.
    edestruct bwdsim_star as [nN [aN [HstarA HmatchN]]]; eauto.
    ee. eapply SIM.(BS_MatchFinal); eauto.
Qed.

(* TODO backward proofs should just be inverting match_states relation *)

Theorem sim_equiv :
  fwdsim ->
  bwdsim ->
  trsys_equiv sysA sysB.
Proof.
  unfold trsys_equiv.
  intros FSIM BSIM; split.
  - apply bwdsim_can_sim; auto.
  - apply fwdsim_can_sim; auto.
Qed.

End GeneralSimulationRelations.

End SimulationRelations.


Section VariableValuations.

Require Import Ascii.
Open Scope string_scope.

(* we'll continue to use strings for variable names *)
Local Notation var := string.

(* the type of an "equality decider" *)
Definition eq_dec (A : Type) :=
  forall (x : A),
    forall (y : A),
      {x = y} + {x <> y}.

Definition var_eq : eq_dec var := string_dec.

Lemma if_var_eq_refl :
  forall (v : var) (a b : option nat),
  (if var_eq v v then a else b) = a.
Proof.
  intros.
  destruct (var_eq v v); auto.
  congruence.
Qed.

(* we'll also continue to associate variables with nats in valuations *)
Definition valuation := list (var * nat).

Fixpoint lookup (x : var) (v : valuation) : option nat :=
  match v with
  | [] => None
  | (y, n) :: v' =>
    if var_eq x y
    then Some n
    else lookup x v'
  end.

Definition lkup (x : var) (v : valuation) : nat :=
  match lookup x v with
    | None => 0
    | Some n => n
  end.

(* TODO would be nice to make these base 10 *)
Fixpoint string_of_nat (n : nat) :=
  match n with
  | O => "O"
  | S m => "S" ++ string_of_nat m
  end.

Fixpoint nat_of_string (s: string) : option nat :=
  match s with
  | EmptyString => None
  | String "O" EmptyString => Some O
  | String "S" s =>
      match nat_of_string s with
      | None => None
      | Some n => Some (S n)
      end
  | _ => None
  end.

Lemma nat_of_string_of_nat :
  forall n,
    nat_of_string (string_of_nat n) = Some n.
Proof.
  induction n; simpl; auto.
  rewrite IHn; auto.
Qed.

Definition TMP_PREFIX :=
  "_".

Definition tmp_var (n : nat) :=
  TMP_PREFIX ++ string_of_nat n.

Definition is_tmp (x : var) :=
  prefix TMP_PREFIX x = true.

Definition not_tmp (x : var) :=
  ~ is_tmp x.

Lemma is_tmp_tmp_var :
  forall n,
  is_tmp (tmp_var n).
Proof.
  unfold is_tmp, tmp_var; intros.
  simpl. destruct n; auto.
Qed.

Lemma tmp_var_inj :
  forall n1 n2,
  tmp_var n1 = tmp_var n2 ->
  n1 = n2.
Proof.
  unfold tmp_var, TMP_PREFIX; intros.
  inversion H. apply (f_equal nat_of_string) in H1.
  repeat rewrite nat_of_string_of_nat in H1.
  congruence.
Qed.

Definition vequiv_when (P : var -> Prop) v1 v2 : Prop :=
  forall x, P x ->
    lookup x v1 = lookup x v2.

Lemma vequiv_when_refl :
  forall P v,
    vequiv_when P v v.
Proof.
  unfold vequiv_when.
  intros; auto.
Qed.

Lemma vequiv_when_sym :
  forall P v1 v2,
    vequiv_when P v1 v2 ->
    vequiv_when P v2 v1.
Proof.
  unfold vequiv_when.
  intros; symmetry; auto.
Qed.

Lemma vequiv_when_trans :
  forall P v1 v2 v3,
    vequiv_when P v1 v2 ->
    vequiv_when P v2 v3 ->
    vequiv_when P v1 v3.
Proof.
  unfold vequiv_when.
  intros. rewrite H; auto.
Qed.

Definition vequiv_for (vars : list var) v1 v2 : Prop :=
  forall x, In x vars ->
    lookup x v1 = lookup x v2.

Lemma vequiv_when_for :
  forall P vars v1 v2,
    Forall P vars ->
    vequiv_when P v1 v2 ->
    vequiv_for vars v1 v2.
Proof.
  unfold vequiv_for.
  intros P vars v1 v2 Hall Hwhen x Hin.
  apply Hwhen. eapply Forall_forall; eauto.
Qed.

End VariableValuations.
Opaque tmp_var.


Module IMPrint.

Local Notation var := string.

(* arithmetic expressions *)
Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

(* commands *)
Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Seq (c1 c2 : cmd)
| If (e : arith) (then_ else_ : cmd)
| While (e : arith) (body : cmd)
| Out (e : arith). (* <-- NEW! Programs can "print" output to their trace. *)

(* arithmetic expression semantics via an interpreter *)
Fixpoint eval_arith (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x => lkup x v
  | Plus  e1 e2 => eval_arith e1 v + eval_arith e2 v
  | Minus e1 e2 => eval_arith e1 v - eval_arith e2 v
  | Times e1 e2 => eval_arith e1 v * eval_arith e2 v
  end.

Definition label : Set := nat.
Definition trace : Set := list label.
Definition state : Set := valuation * cmd.

Inductive step : state -> trace -> state -> Prop :=
| StepAssign :
  forall v x e v',
    v' = (x, eval_arith e v) :: v ->
    step (v, Assign x e) [] (v', Skip)
| StepSeqLStep :
  forall v c1 c2 v' c1' t,
    step (v, c1) t (v', c1') ->
    step (v, Seq c1 c2) t (v', Seq c1' c2)
| StepSeqLDone :
  forall v c2,
    step (v, Seq Skip c2) [] (v, c2)
| StepIfTrue :
  forall v e then_ else_,
    eval_arith e v <> 0 ->
    step (v, If e then_ else_) [] (v, then_)
| StepIfFalse :
  forall v e then_ else_,
    eval_arith e v = 0 ->
    step (v, If e then_ else_) [] (v, else_)
| StepWhileTrue :
  forall v e body,
    eval_arith e v <> 0 ->
    step (v, While e body) [] (v, Seq body (While e body))
| StepWhileFalse :
  forall v e body,
    eval_arith e v = 0 ->
    step (v, While e body) [] (v, Skip)
| StepOut :
  forall v e n,
    n = eval_arith e v ->
    step (v, Out e) [n] (v, Skip).
Local Hint Constructors step : hints.

Inductive final : state -> Prop :=
| Final :
    forall v,
      final (v, Skip).

Lemma final_nostep :
  forall s,
    final s ->
    no_step step s.
Proof.
  unfold no_step, not.
  intros s Hfinal t s' Hstep.
  invc Hfinal. invc Hstep.
Qed.

Definition cmd_to_trsys (v : valuation) (c : cmd) : trsys nat state :=
  {| Init := fun s => s = (v, c);
     Step := step;
     FinalNoStep := final_nostep |}.

Lemma step_det :
  forall s1 t12 s2,
    step s1 t12 s2 ->
    forall t13 s3,
      step s1 t13 s3 ->
      t12 = t13 /\ s2 = s3.
Proof.
  induction 1; intros t13 s3 Hstep;
     invc Hstep; eauto; try congruence.
  - edestruct IHstep; eauto.
    break_up_hyps; auto.
  - edestruct final_nostep; eauto. ee.
  - edestruct final_nostep; eauto. ee.
Qed.

Lemma trsys_is_det :
  forall v c,
    is_det_sys (cmd_to_trsys v c).
Proof.
  intros. ee; simpl; intros.
  - congruence.
  - eapply step_det; eauto.
Qed. 

Lemma trsys_has_init :
  forall v c,
    has_init_state (cmd_to_trsys v c).
Proof.
  unfold has_init_state.
  simpl. eauto.
Qed. 

Lemma trsys_has_single_events :
  forall v c,
    single_events (cmd_to_trsys v c).
Proof.
  unfold single_events.
  intros v c s1 t s2 Hstep.
  induction Hstep; auto.
Qed.

Lemma can_step :
  forall s,
    can_step step s \/ final s.
Proof.
  unfold can_step.
  intros [v c]. induction c.
  - right; ee.
  - left; repeat ee.
  - left. invc IHc1.
    + break_up_hyps. destruct x0; repeat ee.
    + invc H. ee; ee. eapply StepSeqLDone.
  - left. case (Nat.eq_dec (eval_arith e v) 0).
    + ee; ee. eapply StepIfFalse; eauto.
    + ee; ee. eapply StepIfTrue; eauto.
  - left. case (Nat.eq_dec (eval_arith e v) 0).
    + ee; ee. eapply StepWhileFalse; eauto.
    + ee; ee. eapply StepWhileTrue; eauto.
  - left; repeat ee.
Qed.

Lemma optimization_fwdsim_lockstep_sufficient_equiv :
  forall (opt : cmd -> cmd) v c sysA sysB,
    sysA = cmd_to_trsys v c ->
    sysB = cmd_to_trsys v (opt c) ->
    forall (ms : state -> state -> Prop),
      fwdsim_lockstep sysA sysB ms ->
      trsys_equiv sysA sysB.
Proof.
  intros; subst.
  eapply det_lockstep_equiv; eauto.
  - apply trsys_is_det.
  - apply trsys_has_init.
  - unfold match_states_progress; intros.
    apply can_step.
Qed.

Fixpoint optimize_arith (opt : arith -> arith) (c : cmd) : cmd :=
  match c with
  | Skip =>
      Skip
  | Assign x e =>
      Assign x (opt e)
  | Seq c1 c2 =>
      Seq (optimize_arith opt c1) (optimize_arith opt c2)
  | If e c1 c2 =>
      If (opt e) (optimize_arith opt c1) (optimize_arith opt c2)
  | While e body =>
      While (opt e) (optimize_arith opt body)
  | Out e =>
      Out (opt e)
  end.

Section OptimizeArithCorrect.

Variable opt : arith -> arith.

Hypothesis opt_ok :
  forall e v,
    eval_arith (opt e) v = eval_arith e v.

Inductive oa_match_states : state -> state -> Prop :=
| OAMS :
    forall v c,
      oa_match_states (v, c) (v, optimize_arith opt c).

Lemma oa_match_lockstep :
  forall a1 t a2,
    step a1 t a2 ->
    forall b1,
      oa_match_states a1 b1 ->
      exists b2,
        step b1 t b2 /\
        oa_match_states a2 b2.
Proof.
  induction 1; intros b1 Hm; invc Hm; simpl in *.
  - ee; ee; [| ee].
    apply StepAssign.
    rewrite opt_ok; auto.
  - edestruct IHstep; [ee |].
    break_up_hyps. invc H1.
    repeat ee.
  - ee; ee; [| ee].
    apply StepSeqLDone.
  - ee; ee; [| ee].
    apply StepIfTrue.
    rewrite opt_ok; auto.
  - ee; ee; [| ee].
    apply StepIfFalse.
    rewrite opt_ok; auto.
  - ee; ee; [| ee].
    apply StepWhileTrue.
    rewrite opt_ok; auto.
  - ee; ee; [| ee].
    apply StepWhileFalse.
    rewrite opt_ok; auto.
  - ee; ee; [| ee].
    apply StepOut.
    rewrite opt_ok; auto.
Qed.

Lemma optimize_arith_fwdsim :
  forall v c,
    fwdsim_lockstep
      (cmd_to_trsys v c)
      (cmd_to_trsys v (optimize_arith opt c))
      oa_match_states.
Proof.
  intros. ee; intros.
  - invc H. exists (v, optimize_arith opt c). repeat ee.
  - eapply oa_match_lockstep; eauto.
  - invc H0. invc H. simpl. ee.
Qed.

End OptimizeArithCorrect.

Theorem optimize_arith_equiv :
  forall (opt : arith -> arith),
    (forall e v, eval_arith e v = eval_arith (opt e) v) ->
    forall v c,
      trsys_equiv
        (cmd_to_trsys v c)
        (cmd_to_trsys v (optimize_arith opt c)).
Proof.
  intros.
  eapply optimization_fwdsim_lockstep_sufficient_equiv; eauto.
  apply optimize_arith_fwdsim; auto.
Qed.

Fixpoint cfold_arith (e : arith) : arith :=
  match e with
  | Const n => Const n
  | Var x => Var x
  | Plus e1 e2 =>
      let e1' := cfold_arith e1 in
      let e2' := cfold_arith e2 in
      match e1', e2' with
      | Const n1, Const n2 => Const (n1 + n2)
      | _, _ => Plus e1' e2'
      end
  | Minus e1 e2 =>
      let e1' := cfold_arith e1 in
      let e2' := cfold_arith e2 in
      match e1', e2' with
      | Const n1, Const n2 => Const (n1 - n2)
      | _, _ => Minus e1' e2'
      end
  | Times e1 e2 =>
      let e1' := cfold_arith e1 in
      let e2' := cfold_arith e2 in
      match e1', e2' with
      | Const n1, Const n2 => Const (n1 * n2)
      | _, _ => Times e1' e2'
      end
  end.

Lemma cfold_arith_ok :
  forall e v,
  eval_arith e v = eval_arith (cfold_arith e) v.
Proof.
  induction e; simpl; intros; auto.
  - rewrite IHe1, IHe2.
    case_eq (cfold_arith e1); case_eq (cfold_arith e2); auto.
  - rewrite IHe1, IHe2.
    case_eq (cfold_arith e1); case_eq (cfold_arith e2); auto.
  - rewrite IHe1, IHe2.
    case_eq (cfold_arith e1); case_eq (cfold_arith e2); auto.
Qed.

Definition cfold : cmd -> cmd :=
  optimize_arith cfold_arith.

Theorem cfold_equiv :
  forall v c,
    trsys_equiv
      (cmd_to_trsys v c)
      (cmd_to_trsys v (cfold c)).
Proof.
  intros.
  apply optimize_arith_equiv.
  apply cfold_arith_ok.
Qed.

Definition arith_eq (e1 e2 : arith) :
  {e1 = e2} + {e1 <> e2}.
Proof.
  decide equality.
  apply Nat.eq_dec.
  apply var_eq.
Qed.

Fixpoint peephole_arith (e : arith) : arith :=
  match e with
  | Const n => Const n
  | Var x => Var x
  | Plus e1 e2 =>
      let e1' := peephole_arith e1 in
      let e2' := peephole_arith e2 in
      match e1', e2' with
      | _, Const 0 => e1'
      | Const 0, _ => e2'
      | _, _ => Plus e1' e2'
      end
  | Minus e1 e2 =>
      let e1' := peephole_arith e1 in
      let e2' := peephole_arith e2 in
      match e1', e2' with
      | _, Const 0 => e1'
      | Const 0, _ => Const 0
      | _, _ =>
        if arith_eq e1' e2'
        then Const 0
        else Minus e1' e2'
      end
  | Times e1 e2 =>
      let e1' := peephole_arith e1 in
      let e2' := peephole_arith e2 in
      match e1', e2' with
      | _, Const 0 => Const 0
      | Const 0, _ => Const 0
      | _, Const 1 => e1'
      | Const 1, _ => e2'
      | _, _ => Times e1' e2'
      end
  end.

Lemma peephole_arith_ok :
  forall v e,
  eval_arith e v = eval_arith (peephole_arith e) v.
Proof.
  induction e; simpl; intros; auto;
  repeat (
    match goal with
    | [ H : eval_arith _ _ = _ |- _ ] =>
        rewrite H
    | [ H : peephole_arith _ = _ |- _ ] =>
        rewrite H
    | [ |- context[match arith_eq ?a ?b with _ => _ end] ] =>
        case (arith_eq a b); intros; subst
    | [ |- context[match ?E with _ => _ end] ] =>
        case_eq E; intros; subst
    | [ H1 : eval_arith ?e _ = _, H2 : ?e = _ |- _ ] =>
        rewrite H2 in H1
    end; simpl in *; auto
  ); lia.
Qed.

Definition peephole : cmd -> cmd :=
  optimize_arith peephole_arith.

Theorem peephole_equiv :
  forall v c,
    trsys_equiv
      (cmd_to_trsys v c)
      (cmd_to_trsys v (peephole c)).
Proof.
  intros.
  apply optimize_arith_equiv.
  intros; apply peephole_arith_ok.
Qed.

Fixpoint reads_arith (e : arith) : list var :=
  match e with
  | Const _ =>
      []
  | Var x =>
      [x]
  | Plus e1 e2 | Minus e1 e2 | Times e1 e2 =>
      reads_arith e1 ++ reads_arith e2
  end.

Fixpoint reads_cmd (c : cmd) : list var :=
  match c with
  | Skip =>
      []
  | Assign _ e =>
      reads_arith e
  | Seq c1 c2 =>
      reads_cmd c1 ++ reads_cmd c2
  | If e c1 c2 =>
      reads_arith e ++ reads_cmd c1 ++ reads_cmd c2
  | While e body =>
      reads_arith e ++ reads_cmd body
  | Out e =>
      reads_arith e
  end.

Lemma vequiv_reads_eval_arith :
  forall e v1 v2,
    vequiv_for (reads_arith e) v1 v2 ->
    eval_arith e v1 = eval_arith e v2.
Proof.
  unfold vequiv_for.
  induction e; simpl; intros; subst; auto.
  - unfold lkup. rewrite H; auto.
  - erewrite IHe1, IHe2; eauto; intros; apply H; apply in_or_app; auto.
  - erewrite IHe1, IHe2; eauto; intros; apply H; apply in_or_app; auto.
  - erewrite IHe1, IHe2; eauto; intros; apply H; apply in_or_app; auto.
Qed.

End IMPrint.
Local Hint Constructors IMPrint.step : hints.


(*
  "Three Address Code" is a common flavor of intermediate representation
  in compilers where each instruction performs at most one operation:
    https://en.wikipedia.org/wiki/Three-address_code

  This is different from our "IMPrint" language above were expressions can
  have arbitrary size, and therefore require many operations to evaluate.
*)
Module ThreeAddressCode.

Local Notation var := string.

(* fixed-size arithmetic expressions *)

Inductive binop : Set :=
| Add
| Sub
| Mul.

Inductive expr : Set :=
| Const (n : nat)
| Var (x : var)
| Binop (op : binop) (x1 x2 : var).

(* expression semantics via interpreter *)

Definition denote_binop (op : binop) : nat -> nat -> nat :=
  match op with
  | Add => Nat.add
  | Sub => Nat.sub
  | Mul => Nat.mul
  end.

Definition eval_expr (e : expr) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x => lkup x v
  | Binop op x1 x2 => (denote_binop op) (lkup x1 v) (lkup x2 v)
  end.

(* programs *)

Inductive cmd :=
| Skip
| Assign (x : var) (e : expr)
| Seq (c1 c2 : cmd)
| If (x : var) (then_ else_ : cmd)
| While (x : var) (body : cmd)
| Out (x : var).

(* small step operational semantics *)

Definition label : Set := nat.
Definition trace : Set := list label.
Definition state : Set := valuation * cmd.

Inductive step : state -> trace -> state -> Prop :=
| StepAssign :
  forall v x e v',
    v' = (x, eval_expr e v) :: v ->
    step (v, Assign x e) [] (v', Skip)
| StepSeqLStep :
  forall v c1 c2 v' c1' t,
    step (v, c1) t (v', c1') ->
    step (v, Seq c1 c2) t (v', Seq c1' c2)
| StepSeqLDone :
  forall v c2,
    step (v, Seq Skip c2) [] (v, c2)
| StepIfTrue :
  forall v x then_ else_,
    lkup x v <> 0 ->
    step (v, If x then_ else_) [] (v, then_)
| StepIfFalse :
  forall v x then_ else_,
    lkup x v = 0 ->
    step (v, If x then_ else_) [] (v, else_)
| StepWhileTrue :
  forall v x body,
    lkup x v <> 0 ->
    step (v, While x body) [] (v, Seq body (While x body))
| StepWhileFalse :
  forall v x body,
    lkup x v = 0 ->
    step (v, While x body) [] (v, Skip)
| StepOut :
  forall v x t,
    t = [lkup x v] ->
    step (v, Out x) t (v, Skip).
Local Hint Constructors step : hints.

Inductive final : state -> Prop :=
| Final :
    forall v,
      final (v, Skip).

Lemma final_nostep :
  forall s,
    final s ->
    no_step step s.
Proof.
  unfold no_step, not.
  intros s Hfinal t s' Hstep.
  invc Hfinal. invc Hstep.
Qed.

Definition cmd_to_trsys (v : valuation) (c : cmd) : trsys nat state :=
  {| Init := fun s => s = (v, c);
     Step := step;
     FinalNoStep := final_nostep |}.

Lemma step_det :
  forall s1 t12 s2,
    step s1 t12 s2 ->
    forall t13 s3,
      step s1 t13 s3 ->
      t12 = t13 /\ s2 = s3.
Proof.
  induction 1; intros t13 s3 Hstep;
     invc Hstep; eauto; try congruence.
  - edestruct IHstep; eauto.
    break_up_hyps; auto.
  - edestruct final_nostep; eauto. ee.
  - edestruct final_nostep; eauto. ee.
Qed.

Lemma trsys_is_det :
  forall v c,
    is_det_sys (cmd_to_trsys v c).
Proof.
  intros. ee; simpl; intros.
  - congruence.
  - eapply step_det; eauto.
Qed. 

Lemma trsys_has_init :
  forall v c,
    has_init_state (cmd_to_trsys v c).
Proof.
  unfold has_init_state.
  simpl. eauto.
Qed.

Lemma trsys_has_single_events :
  forall v c,
    single_events (cmd_to_trsys v c).
Proof.
  unfold single_events.
  intros v c s1 t s2 Hstep.
  induction Hstep; subst; auto.
Qed.

Lemma can_step :
  forall s,
    can_step step s \/ final s.
Proof.
  unfold can_step.
  intros [v c]. induction c.
  - right; ee.
  - left; repeat ee.
  - left. invc IHc1.
    + break_up_hyps. destruct x0; repeat ee.
    + invc H. ee; ee. eapply StepSeqLDone.
  - left. case (Nat.eq_dec (lkup x v) 0).
    + ee; ee. eapply StepIfFalse; eauto.
    + ee; ee. eapply StepIfTrue; eauto.
  - left. case (Nat.eq_dec (lkup x v) 0).
    + ee; ee. eapply StepWhileFalse; eauto.
    + ee; ee. eapply StepWhileTrue; eauto.
  - left; repeat ee.
Qed.

Lemma step_star_seq' :
  forall s1 t s2,
    star step s1 t s2 ->
    forall v1 c1 v1' c1' c2,
      s1 = (v1, c1) ->
      s2 = (v1', c1') ->
      star step (v1, Seq c1 c2) t (v1', Seq c1' c2).
Proof.
  induction 1; intros; subst; break_up_hyps.
  - eauto with hints.
  - destruct s2. eapply star_trans.
    2 : { eapply IHstar; eauto. }
    repeat ee. listy.
Qed.

Lemma step_star_seq :
  forall v1 c1 t v1' c1' c2,
    star step (v1, c1) t (v1', c1') ->
    star step (v1, Seq c1 c2) t (v1', Seq c1' c2).
Proof.
  intros. eapply step_star_seq'; eauto.
Qed.

Lemma step_plus_seq :
  forall v1 c1 t v1' c1' c2,
    plus step (v1, c1) t (v1', c1') ->
    plus step (v1, Seq c1 c2) t (v1', Seq c1' c2).
Proof.
  intros. invc H. destruct s2.
  ee; [ee |]. eapply step_star_seq; eauto.
Qed.

Lemma step_star_seq_inv' :
  forall s1 t s2,
    star step s1 t s2 ->
    forall vA c1 c2 vC cC,
      s1 = (vA, Seq c1 c2) ->
      s2 = (vC, cC) ->
      (exists c1',
        star step (vA, c1) t (vC, c1') /\
        cC = Seq c1' c2)
      \/
      (exists t1 t2 vB,
        star step (vA, c1) t1 (vB, Skip) /\
        star step (vB, c2) t2 (vC, cC) /\
        t = t1 ++ t2).
Proof.
  induction 1; intros; subst; break_up_hyps.
  - eauto with hints.
  - invc H.
    + edestruct IHstar; eauto; break_up_hyps; subst.
      * eauto with hints.
      * right. repeat ee. listy.
    + right. repeat ee.
Qed. 

Lemma step_star_seq_inv :
  forall vA c1 c2 t vC cC,
    star step (vA, Seq c1 c2) t (vC, cC) ->
    (exists c1',
      star step (vA, c1) t (vC, c1') /\
      cC = Seq c1' c2)
    \/
    (exists t1 t2 vB,
      star step (vA, c1) t1 (vB, Skip) /\
      star step (vB, c2) t2 (vC, cC) /\
      t = t1 ++ t2).
Proof.
  intros. eapply step_star_seq_inv'; eauto.
Qed.

Lemma step_star_seq_skip_inv :
  forall vA c1 c2 t vC,
    star step (vA, Seq c1 c2) t (vC, Skip) ->
    (exists t1 t2 vB,
      star step (vA, c1) t1 (vB, Skip) /\
      star step (vB, c2) t2 (vC, Skip) /\
      t = t1 ++ t2).
Proof.
  intros. edestruct step_star_seq_inv; eauto.
  break_up_hyps; subst. congruence.
Qed.

(* relating programs by seq reassociation *)

Inductive seq_assoc_1 : cmd -> cmd -> Prop :=
| SA1_Assoc_LR :
    forall c1 c2 c3,
    seq_assoc_1
      (Seq (Seq c1 c2) c3)
      (Seq c1 (Seq c2 c3))
| SA1_Assoc_RL :
    forall c1 c2 c3,
    seq_assoc_1
      (Seq c1 (Seq c2 c3))
      (Seq (Seq c1 c2) c3)
| SA1_Seq_L :
    forall c1 c1' c2,
      seq_assoc_1 c1 c1' ->
      seq_assoc_1 (Seq c1 c2) (Seq c1' c2)
| SA1_Seq_R :
    forall c1 c2 c2',
      seq_assoc_1 c2 c2' ->
      seq_assoc_1 (Seq c1 c2) (Seq c1 c2')
| SA1_If_Then :
    forall e c1 c1' c2,
      seq_assoc_1 c1 c1' ->
      seq_assoc_1 (If e c1 c2) (If e c1' c2)
| SA1_If_Else :
    forall e c1 c2 c2',
      seq_assoc_1 c2 c2' ->
      seq_assoc_1 (If e c1 c2) (If e c1 c2')
| SA1_While :
    forall e c1 c1',
      seq_assoc_1 c1 c1' ->
      seq_assoc_1 (While e c1) (While e c1').
Local Hint Constructors seq_assoc_1 : hints.

Definition seq_assoc :=
  trc seq_assoc_1.

Lemma seq_assoc_refl :
  forall c,
    seq_assoc c c.
Proof.
  apply trc_refl.
Qed.

Lemma seq_assoc_1_sym :
  forall c1 c2,
    seq_assoc_1 c1 c2 ->
    seq_assoc_1 c2 c1.
Proof.
  induction 1; ee.
Qed.

Lemma seq_assoc_sym :
  forall c1 c2,
    seq_assoc c1 c2 ->
    seq_assoc c2 c1.
Proof.
  induction 1; eauto.
  - apply seq_assoc_refl.
  - eapply trc_back; eauto.
    apply seq_assoc_1_sym; auto.
Qed.

Lemma seq_assoc_trans :
  forall c1 c2 c3,
    seq_assoc c1 c2 ->
    seq_assoc c2 c3 ->
    seq_assoc c1 c3.
Proof.
  eapply trc_trans; eauto.
Qed.

Lemma seq_assoc_1_seq_assoc :
 forall cA cB,
    seq_assoc_1 cA cB ->
    seq_assoc cA cB.
Proof.
  repeat ee.
Qed.

Lemma seq_assoc_seq_l :
  forall cA cB c2,
    seq_assoc cA cB ->
    seq_assoc (Seq cA c2) (Seq cB c2).
Proof.
  intros cA cB c2 HSA; revert c2.
  induction HSA; intros; [ee |].
  eapply seq_assoc_trans; eauto.
  eapply trc_front; eauto; ee.
Qed.

Lemma seq_assoc_seq_r :
  forall c1 cA cB,
    seq_assoc cA cB ->
    seq_assoc (Seq c1 cA) (Seq c1 cB).
Proof.
  intros c1 cA cB HSA; revert c1.
  induction HSA; intros; [ee |].
  eapply seq_assoc_trans; eauto.
  eapply trc_front; eauto; [| ee]. ee.
Qed.

Lemma seq_assoc_seq :
  forall c1 c1' c2 c2',
    seq_assoc c1 c1' ->
    seq_assoc c2 c2' ->
    seq_assoc (Seq c1 c2) (Seq c1' c2').
Proof.
  intros.
  eapply seq_assoc_trans; eauto.
  eapply seq_assoc_seq_l; eauto.
  eapply seq_assoc_seq_r; eauto.
Qed.

Lemma seq_assoc_while :
  forall e cA cB,
    seq_assoc cA cB ->
    seq_assoc (While e cA) (While e cB).
Proof.
  intros e cA cB HSA.
  induction HSA; intros; repeat ee.
Qed.

Local Hint Resolve seq_assoc_1_seq_assoc : hints.
Local Hint Resolve seq_assoc_refl : hints.
Local Hint Resolve seq_assoc_sym : hints.
Local Hint Resolve seq_assoc_trans : hints.
Local Hint Resolve seq_assoc_seq_l : hints.
Local Hint Resolve seq_assoc_seq_r : hints.
Local Hint Resolve seq_assoc_seq : hints.
Local Hint Resolve seq_assoc_while : hints.

(* seq_assoc forward lockstep simulation diagram *)

Lemma seq_assoc_1_fwdsim :
  forall c1 c2,
    seq_assoc_1 c1 c2 ->
    forall v t v' c1',
      step (v, c1) t (v', c1') ->
      exists c2',
        step (v, c2) t (v', c2') /\
        seq_assoc c1' c2'.
Proof.
  intros cA cB HSA.
  induction HSA;
    intros v t v' cA' Hstep;
    invc Hstep; eauto with hints.
  - invc H3; [repeat ee |].
    exists (Seq c1' c3); repeat ee.
  - exists (Seq (Seq c1' c2) c3); repeat ee.
  - edestruct IHHSA; eauto; break_up_hyps.
    eexists; split; [repeat ee |].
    eauto with hints.
  - invc HSA.
  - exists (Seq c1' c2'); split; [repeat ee |].
    eauto with hints.
  - exists (Seq c1' (While e c1')); split; [repeat ee |].
    eauto with hints.
Qed.

Lemma seq_assoc_fwdsim :
  forall c1 c2,
    seq_assoc c1 c2 ->
    forall v t v' c1',
      step (v, c1) t (v', c1') ->
      exists c2',
        step (v, c2) t (v', c2') /\
        seq_assoc c1' c2'.
Proof.
  intros cA cB HSA.
  induction HSA; intros v t v' cA' Hstep.
  - exists cA'; eauto with hints.
  - edestruct seq_assoc_1_fwdsim; eauto; break_up_hyps.
    edestruct IHHSA; eauto; break_up_hyps.
    eauto with hints.
Qed.

Inductive seq_assoc_match_states : state -> state -> Prop :=
| SAMS :
    forall v cA cB,
      seq_assoc cA cB ->
      seq_assoc_match_states (v, cA) (v, cB).

Lemma step_seq_assoc :
  forall s1 t s1',
    step s1 t s1' ->
    forall s2,
      seq_assoc_match_states s1 s2 ->
      exists s2',
        step s2 t s2' /\
        seq_assoc_match_states s1' s2'.
Proof.
  intros. destruct s1'; invc H0.
  edestruct seq_assoc_fwdsim; eauto; break_up_hyps.
  repeat ee.
Qed.

Lemma star_step_seq_assoc :
  forall s1 t s1',
    star step s1 t s1' ->
    forall s2,
      seq_assoc_match_states s1 s2 ->
      exists s2',
        star step s2 t s2' /\
        seq_assoc_match_states s1' s2'.
Proof.
  induction 1; intros; subst.
  - repeat ee.
  - edestruct step_seq_assoc; eauto; break_up_hyps.
    edestruct IHstar; eauto; break_up_hyps.
    repeat ee.
Qed.

Lemma plus_step_seq_assoc :
  forall s1 t s1',
    plus step s1 t s1' ->
    forall s2,
      seq_assoc_match_states s1 s2 ->
      exists s2',
        plus step s2 t s2' /\
        seq_assoc_match_states s1' s2'.
Proof.
  intros s1 t s1' Hplus s2 Hmatch. invc Hplus. 
  edestruct step_seq_assoc; eauto; break_up_hyps.
  edestruct star_step_seq_assoc; eauto; break_up_hyps.
  eauto with hints.
Qed.

End ThreeAddressCode.
Local Hint Constructors ThreeAddressCode.step : hints.
Local Hint Resolve ThreeAddressCode.seq_assoc_refl : hints.


(* translating IMPrint programs to ThreeAddressCode programs *)
Module Imp_to_TAC.

Module S := IMPrint.
Module T := ThreeAddressCode.

Fixpoint translate_arith (tmp : nat) (e_src : S.arith) : T.cmd :=
  let do_binop op e1 e2 :=
    (* translate LHS *)
    let tmp1 := S tmp in
    let c1 := translate_arith tmp1 e1 in
    (* translate RHS *)
    let tmp2 := S (S tmp) in
    let c2 := translate_arith tmp2 e2 in
    (* put it all together *)
    T.Seq c1 (T.Seq c2
      (T.Assign (tmp_var tmp) (T.Binop op (tmp_var tmp1) (tmp_var tmp2))))
  in
  match e_src with
  | S.Const n =>
      T.Assign (tmp_var tmp) (T.Const n)
  | S.Var x =>
      T.Assign (tmp_var tmp) (T.Var x)
  | S.Plus e1 e2 =>
      do_binop T.Add e1 e2
  | S.Minus e1 e2 =>
      do_binop T.Sub e1 e2
  | S.Times e1 e2 =>
      do_binop T.Mul e1 e2
  end.

Fixpoint translate_cmd (c_src : S.cmd) : T.cmd :=
  match c_src with
  | S.Skip =>
      T.Skip
  | S.Assign x e_src =>
      T.Seq
        (translate_arith 0 e_src)
        (T.Assign x (T.Var (tmp_var 0)))
  | S.Seq c1 c2 =>
      T.Seq
        (translate_cmd c1)
        (translate_cmd c2)
  | S.If e_src c1 c2 =>
      T.Seq
        (translate_arith 0 e_src)
        (T.If (tmp_var 0) (translate_cmd c1) (translate_cmd c2))
  | S.While e_src body =>
      (* make sure to recompute loop condition at end of body! *)
      T.Seq
        (translate_arith 0 e_src)
        (T.While (tmp_var 0)
          (T.Seq (translate_cmd body) (translate_arith 0 e_src)))
  | S.Out e_src =>
      T.Seq
        (translate_arith 0 e_src)
        (T.Out (tmp_var 0))
  end.

Ltac star_step_inv :=
  match goal with
  | [ H : star T.step (_, T.Skip) _ _ |- _ ] => invc H
  | [ H : T.step (_, T.Skip) _ _ |- _ ] => invc H
  | [ H : star T.step (_, T.Assign _ _) _ _ |- _] => invc H
  | [ H : T.step (_, T.Assign _ _) _ _ |- _] => invc H
  | [ H : star T.step (_, T.Seq _ _) _ (_, T.Skip) |- _ ] =>
      apply T.step_star_seq_skip_inv in H;
      let t1 := fresh "t1" in
      let t2 := fresh "t2" in
      let vM := fresh "vM" in
      let SM := fresh "SM" in
      destruct H as [t1 [t1 [vM [SM H]]]]
  | [ H : star T.step (_, T.Seq _ _) _ _ |- _ ] =>
      apply T.step_star_seq_inv in H;
      destruct H; break_up_hyps; subst
  end.

Ltac bogus_tmp :=
  match goal with
  | [ H : ~ is_tmp (tmp_var _) |- _ ] =>
      destruct H; apply is_tmp_tmp_var
  | [ H : tmp_var _ = tmp_var _ |- _ ] =>
      apply tmp_var_inj in H; subst; lia
  end.

Lemma translate_arith_not_tmp_same :
  forall e tmp v t v' foo,
    star T.step (v, translate_arith tmp e) t (v', T.Skip) ->
    not_tmp foo ->
    lookup foo v = lookup foo v'.
Proof.
  unfold not_tmp.
  induction e; simpl; intros.
  - repeat star_step_inv; simpl.
    break_if; subst; auto. bogus_tmp.
  - repeat star_step_inv; simpl.
    break_if; subst; auto. bogus_tmp.
  - repeat star_step_inv; try discriminate.
    unfold lkup; simpl.
    erewrite IHe1, IHe2; eauto.
    break_if; subst; auto.
    repeat break_match_goal; bogus_tmp.
  - repeat star_step_inv; try discriminate.
    unfold lkup; simpl.
    erewrite IHe1, IHe2; eauto.
    break_if; subst; auto.
    repeat break_match_goal; bogus_tmp.
  - repeat star_step_inv; try discriminate.
    unfold lkup; simpl.
    erewrite IHe1, IHe2; eauto.
    break_if; subst; auto.
    repeat break_match_goal; bogus_tmp.
Qed.

Lemma translate_arith_vequiv_when_not_tmp :
  forall e tmp v t v',
    star T.step (v, translate_arith tmp e) t (v', T.Skip) ->
    vequiv_when not_tmp v v'.
Proof.
  unfold vequiv_when; intros.
  eapply translate_arith_not_tmp_same; eauto.
Qed.

Lemma translate_arith_preserves_eval_arith :
  forall e1 e2 tmp v v',
    Forall not_tmp (S.reads_arith e1) ->
    star T.step (v, translate_arith tmp e2) [] (v', T.Skip) ->
    S.eval_arith e1 v' = S.eval_arith e1 v.
Proof.
  intros.
  apply S.vequiv_reads_eval_arith.
  unfold vequiv_for; intros. symmetry.
  eapply translate_arith_not_tmp_same; eauto.
  eapply Forall_forall; eauto.
Qed.

Lemma translate_arith_lt_tmp_same :
  forall e tmp v t v' n,
    star T.step (v, translate_arith tmp e) t (v', T.Skip) ->
    n < tmp ->
    lookup (tmp_var n) v = lookup (tmp_var n) v'.
Proof.
  induction e; simpl; intros.
  - repeat star_step_inv; simpl.
    break_if; subst; auto. bogus_tmp.
  - repeat star_step_inv; simpl.
    break_if; subst; auto. bogus_tmp.
  - repeat star_step_inv; try discriminate.
    unfold lkup; simpl.
    erewrite IHe1, IHe2; eauto.
    break_if; subst; auto.
    repeat break_match_goal; bogus_tmp.
  - repeat star_step_inv; try discriminate.
    unfold lkup; simpl.
    erewrite IHe1, IHe2; eauto.
    break_if; subst; auto.
    repeat break_match_goal; bogus_tmp.
  - repeat star_step_inv; try discriminate.
    unfold lkup; simpl.
    erewrite IHe1, IHe2; eauto.
    break_if; subst; auto.
    repeat break_match_goal; bogus_tmp.
Qed.

Ltac star_step :=
  match goal with
  | [ |- star T.step (_, T.Seq T.Skip _) _ _ ] =>
      eapply star_front; [
        eapply T.StepSeqLDone
      | | listy ]
  | [ |- star T.step (_, T.Assign _ _) _ _ ] =>
      eapply star_front; [
        econstructor; eauto
      | | listy ]
  | [ |- star T.step (_, T.Out _) _ _ ] =>
      eapply star_front; [
        econstructor; eauto
      | | listy ]
  | [ H : lkup ?x ?v <> 0
      |- star T.step (?v, T.If ?x _ _) _ _ ] =>
      eapply star_front; [
        eapply T.StepIfTrue; eauto
      | | listy]
  | [ H : lkup ?x ?v = 0
      |- star T.step (?v, T.If ?x _ _) _ _ ] =>
      eapply star_front; [
        eapply T.StepIfFalse; eauto
      | | listy]
  | [ H : lkup ?x ?v <> 0
      |- star T.step (?v, T.While ?x _) _ _ ] =>
      eapply star_front; [
        eapply T.StepWhileTrue; eauto
      | | listy]
  | [ H : lkup ?x ?v = 0
      |- star T.step (?v, T.While ?x _) _ _ ] =>
      eapply star_front; [
        eapply T.StepWhileFalse; eauto
      | | listy]
  | [ |- star T.step (_, T.If _ _ _) _ _ ] =>
      eapply star_front; [ | | listy]
  | [ H : star T.step (_, ?c1) _ _
      |- star T.step (_, T.Seq ?c1 _) _ _ ] =>
      eapply star_trans; [
        eapply T.step_star_seq; eapply H
      | | listy ]
  | [ |- star T.step (_, T.Skip) _ _ ] =>
      eapply star_refl
  | [ |- star T.step (_, ?c) _ (_, ?c) ] =>
      eapply star_refl
  end.

Lemma translate_arith_eval_arith :
  forall e tmp v,
    Forall not_tmp (S.reads_arith e) ->
    exists v',
      star T.step (v, translate_arith tmp e) [] (v', T.Skip) /\
      lookup (tmp_var tmp) v' = Some (S.eval_arith e v).
Proof.
  induction e; simpl; intros.
  - repeat ee; simpl.
    break_if; [auto | congruence].
  - repeat ee; simpl.
    break_if; [auto | congruence].
  - apply Forall_app in H; break_up_hyps.
    edestruct IHe1 with (S tmp) v; eauto; break_up_hyps.
    edestruct IHe2 with (S (S tmp)) x; eauto; break_up_hyps.
    eexists; split; [repeat star_step |].
    simpl; unfold lkup. rewrite if_var_eq_refl.
    erewrite <- translate_arith_lt_tmp_same; eauto.
    repeat rewrite_match_goal; auto.
    f_equal; f_equal; auto.
    erewrite translate_arith_preserves_eval_arith; eauto.
  - apply Forall_app in H; break_up_hyps.
    edestruct IHe1 with (S tmp) v; eauto; break_up_hyps.
    edestruct IHe2 with (S (S tmp)) x; eauto; break_up_hyps.
    eexists; split; [repeat star_step |].
    simpl; unfold lkup. rewrite if_var_eq_refl.
    erewrite <- translate_arith_lt_tmp_same; eauto.
    repeat rewrite_match_goal; auto.
    f_equal; f_equal; auto.
    erewrite translate_arith_preserves_eval_arith; eauto.
  - apply Forall_app in H; break_up_hyps.
    edestruct IHe1 with (S tmp) v; eauto; break_up_hyps.
    edestruct IHe2 with (S (S tmp)) x; eauto; break_up_hyps.
    eexists; split; [repeat star_step |].
    simpl; unfold lkup. rewrite if_var_eq_refl.
    erewrite <- translate_arith_lt_tmp_same; eauto.
    repeat rewrite_match_goal; auto.
    f_equal; f_equal; auto.
    erewrite translate_arith_preserves_eval_arith; eauto.
Qed.

Inductive match_states : S.state -> T.state -> Prop :=
| MatchStates :
    forall vS cS vT cT,
      Forall not_tmp (S.reads_cmd cS) ->
      vequiv_when not_tmp vS vT ->
      T.seq_assoc (translate_cmd cS) cT ->
      match_states (vS, cS) (vT, cT).

Ltac break_state :=
  match goal with
  | [ s : T.state |- _ ] => destruct s
  end.

Ltac setup_branch :=
  match goal with
  | [ H1 : S.eval_arith ?e ?vA <> 0,
      H2 : vequiv_when not_tmp ?vA ?vB,
      H3 : star T.step (?vB, translate_arith _ _) [] (?vB', _),
      H4 : lookup ?foo ?vB' = Some (S.eval_arith ?e ?vB) |- _ ] =>
      assert (lkup foo vB' <> 0); [
        unfold lkup; rewrite H4;
        erewrite S.vequiv_reads_eval_arith; eauto;
        eapply vequiv_when_for; eauto;
        eapply vequiv_when_sym; eauto
      |]
  | [ H1 : S.eval_arith ?e ?vA = 0,
      H2 : vequiv_when not_tmp ?vA ?vB,
      H3 : star T.step (?vB, translate_arith _ _) [] (?vB', _),
      H4 : lookup ?foo ?vB' = Some (S.eval_arith ?e ?vB) |- _ ] =>
      assert (lkup foo vB' = 0); [
        unfold lkup; rewrite H4;
        erewrite S.vequiv_reads_eval_arith; eauto;
        eapply vequiv_when_for; eauto;
        eapply vequiv_when_sym; eauto
      |]
  end.

Ltac plus_step :=
  match goal with
  | [ H : star T.step (_, ?c1) _ _
      |- plus T.step (_, T.Seq ?c1 _) _ _ ] =>
      eapply star_plus_plus; [
        eapply T.step_star_seq; eapply H
      | | listy ]
  | [ H : plus T.step (_, ?c1) _ _
      |- plus T.step (_, T.Seq ?c1 _) _ _ ] =>
      eapply plus_star_plus; [
        eapply T.step_plus_seq; eapply H
      | | listy ]
  | [ |- plus T.step (_, T.Seq T.Skip _) _ _ ] =>
      eapply plus_front; [
        eapply T.StepSeqLDone
      | | listy ]
  | _ => star_step
  end.

Ltac seq_assoc_inv :=
  repeat match goal with
  | [ H : T.seq_assoc_match_states _ _ |- _ ] => invc H
  | [ H : T.seq_assoc T.Skip _ |- _ ] => invc H
  | [ H : T.seq_assoc_1 T.Skip _ |- _ ] => invc H
  | [ H : T.seq_assoc_1 _ T.Skip |- _ ] => invc H
  | [ H : T.seq_assoc _ T.Skip |- _ ] =>
      apply T.seq_assoc_sym in H
  end.

Ltac vequiv :=
  repeat (
    auto;
    match goal with
    | [ H : match_states (?v1, _) (?v2, _)
        |- lookup ?x ?v1 = lookup ?x ?v2 ] =>
        invc H
    | [ |- vequiv_when _ _ _ ] =>
        unfold vequiv_when; simpl; intros
    | [ |- S.eval_arith ?e _ = S.eval_arith ?e _ ] =>
        apply S.vequiv_reads_eval_arith
    | [ H : vequiv_when _ _ _ |- vequiv_for _ _ _ ] =>
        eapply vequiv_when_for; eauto
    | [ H1 : vequiv_when _ ?v1 ?v2
        |- lookup ?x ?v1 = lookup ?x ?v3 ] =>
        eapply vequiv_when_trans; eauto
    | [ H : star T.step (?v1, translate_arith _ _) _ (?v2, _)
        |- lookup ?x ?v1 = lookup ?x ?v2 ] =>
        eapply translate_arith_not_tmp_same; eauto
    | [ |- Some _ = Some _ ] => f_equal
    end || (
      break_if; subst
    ) || (
      unfold lkup; rewrite_match_goal
    )
  ).

Ltac seq_assoc :=
  repeat match goal with
    | [ H : match_states (?v1, _) (?v2, _) |- _ ] =>
        invc H
    | [ |- T.seq_assoc ?x ?x ] =>
        apply T.seq_assoc_refl
    | [ H : T.seq_assoc ?b ?c
        |- T.seq_assoc ?a ?c ] =>
        apply T.seq_assoc_trans with (c2 := b); auto
    | [ |- T.seq_assoc (T.Seq _ ?b) (T.Seq _ ?b) ] =>
        apply T.seq_assoc_seq_l
    end.

Lemma translate_cmd_fwdsim_add_diagram :
  forall a1 t a2,
    S.step a1 t a2 ->
    forall b1,
      match_states a1 b1 ->
      exists b2,
        plus T.step b1 t b2 /\
        match_states a2 b2.
Proof.
  induction 1; intros b1 MS; invc MS; simpl in *.
  (* ASSIGN *)
  - destruct (translate_arith_eval_arith e 0 vT);
      eauto; break_up_hyps.
    edestruct T.plus_step_seq_assoc;
      [| ee |]; [repeat plus_step |]; break_up_hyps.
    seq_assoc_inv.
    eexists; split; eauto.
    ee; simpl.
    + apply Forall_nil.
    + vequiv.
    + seq_assoc.
  (* SEQ STEP *)
  - find_apply_lem_hyp Forall_app; break_up_hyps.
    edestruct IHstep; eauto; [repeat ee | break_up_hyps].
    break_state. (* <== important for automation below! *)
    edestruct T.plus_step_seq_assoc;
      [| ee |]; [repeat plus_step; eapply star_refl |]; break_up_hyps.
    seq_assoc_inv.
    eexists; split; eauto.
    ee; simpl.
    + apply Forall_app; split; auto.
      invc H4; auto. (* not structural :\ *)
    + vequiv.
    + seq_assoc.
  (* SEQ SKIP *)
  - edestruct T.plus_step_seq_assoc;
      [| ee |]; [repeat plus_step; eapply star_refl |]; break_up_hyps.
    seq_assoc_inv.
    eexists; split; eauto.
    ee.
  (* IF TRUE *)
  - find_apply_lem_hyp Forall_app; break_up_hyps.
    find_apply_lem_hyp Forall_app; break_up_hyps.
    destruct (translate_arith_eval_arith e 0 vT);
      eauto; break_up_hyps.
    setup_branch.
    edestruct T.plus_step_seq_assoc;
      [| ee |]; [repeat plus_step; eapply star_refl |]; break_up_hyps.
    seq_assoc_inv.
    eexists; split; eauto.
    ee. vequiv.
  (* IF FALSE *)
  - find_apply_lem_hyp Forall_app; break_up_hyps.
    find_apply_lem_hyp Forall_app; break_up_hyps.
    destruct (translate_arith_eval_arith e 0 vT);
      eauto; break_up_hyps.
    setup_branch.
    edestruct T.plus_step_seq_assoc;
      [| ee |]; [repeat plus_step; eapply star_refl |]; break_up_hyps.
    seq_assoc_inv.
    eexists; split; eauto.
    ee. vequiv.
  (* WHILE TRUE *)
  - find_apply_lem_hyp Forall_app; break_up_hyps.
    destruct (translate_arith_eval_arith e 0 vT);
      eauto; break_up_hyps.
    setup_branch.
    edestruct T.plus_step_seq_assoc;
      [| ee |]; [repeat plus_step; eapply star_refl |]; break_up_hyps.
    seq_assoc_inv.
    eexists; split; eauto.
    ee; simpl.
    + apply Forall_app; split; auto.
      apply Forall_app; split; auto.
    + vequiv.
    + seq_assoc. repeat ee.
  (* WHILE FALSE *)
  - find_apply_lem_hyp Forall_app; break_up_hyps.
    destruct (translate_arith_eval_arith e 0 vT);
      eauto; break_up_hyps.
    setup_branch.
    edestruct T.plus_step_seq_assoc;
      [| ee |]; [repeat plus_step; eapply star_refl |]; break_up_hyps.
    seq_assoc_inv.
    eexists; split; eauto.
    ee; simpl.
    + apply Forall_nil.
    + vequiv.
    + seq_assoc.
  (* OUT *)
  - destruct (translate_arith_eval_arith e 0 vT);
      eauto; break_up_hyps.
    edestruct T.plus_step_seq_assoc;
      [| ee |]; [repeat plus_step |]; break_up_hyps.
    seq_assoc_inv.
    (* first fix up the trace, not structural :\ *)
    unfold lkup in *.
      rewrite H0 in H1.
      erewrite <- S.vequiv_reads_eval_arith in H1; eauto.
      2 : eapply vequiv_when_for; eauto.
    eexists; split; eauto.
    ee; simpl.
    + apply Forall_nil.
    + vequiv.
    + seq_assoc.
Qed.

Lemma translate_cmd_fwdsim_add :
  forall cS,
    Forall not_tmp (S.reads_cmd cS) ->
    forall v,
      fwdsim_add
        (S.cmd_to_trsys v cS)
        (T.cmd_to_trsys v (translate_cmd cS))
        match_states.
Proof.
  constructor.
  - intros [v0 c0] Ha0. invc Ha0.
    exists (v, (translate_cmd cS)); split; ee.
    + vequiv.
    + seq_assoc.
  - intros. eapply translate_cmd_fwdsim_add_diagram; eauto.
  - intros aN bN Hmatch Hfinal.
    invc Hfinal. invc Hmatch.
    simpl in *. seq_assoc_inv.
    ee.
Qed.

Theorem translate_cmd_equiv :
  forall cS,
    Forall not_tmp (S.reads_cmd cS) ->
    forall v,
      trsys_equiv
        (S.cmd_to_trsys v cS)
        (T.cmd_to_trsys v (translate_cmd cS)).
Proof.
  intros.
  eapply det_fwdsim_add_equiv with (MS := match_states); eauto.
  - apply T.trsys_is_det.
  - apply S.trsys_has_init.
  - apply S.trsys_has_single_events.
  - unfold match_states_progress.
    intros. apply S.can_step.
  - apply translate_cmd_fwdsim_add.
    assumption.
Qed.

End Imp_to_TAC.


Lemma if_nat_eq_refl :
  forall T (n : nat) (a b : T),
  (if Nat.eq_dec n n then a else b) = a.
Proof.
  intros. break_if; auto; congruence.
Qed.


(*
A control flow graph IR.
  https://en.wikipedia.org/wiki/Control-flow_graph

This IR will help simplify expressing and proving analyses.
We'll represent graphs as finite maps from node ids (nats) to instructions
where instruction contains the node ids of its successor instructions.
*)
Module ControlFlowGraph.

Local Notation var := string.

Definition node := nat.

Inductive binop : Set :=
| Add
| Sub
| Mul.

Inductive instr :=
| Nop (next : node)
| Load (dst : var) (const : nat) (next : node)
| Copy (dst : var) (src : var) (next : node)
| Op (dst : var) (op : binop) (arg_l arg_r : var) (next : node)
| Cond (test : var) (next_true next_false : node)
| Out (arg : var) (next : node)
| Halt.

Definition cfg :=
  list (node * instr).

(* small step operational semantics *)

Definition label : Set := nat.
Definition trace : Set := list label.
Definition state : Set := valuation * cfg * node.

Fixpoint fetch (n : node) (c : cfg) : option instr :=
  match c with
  | [] => None
  | (id, instr) :: cfg' =>
      if Nat.eq_dec n id
      then Some instr
      else fetch n cfg'
  end.

Definition denote_binop (op : binop) : nat -> nat -> nat :=
  match op with
  | Add => Nat.add
  | Sub => Nat.sub
  | Mul => Nat.mul
  end.

Inductive step : state -> trace -> state -> Prop :=
| StepNop :
    forall v cfg pc pc',
      fetch pc cfg = Some (Nop pc') ->
      step (v, cfg, pc) [] (v, cfg, pc')
| StepLoad :
    forall v cfg pc v' dst n pc',
      fetch pc cfg = Some (Load dst n pc') ->
      v' = (dst, n) :: v ->
      step (v, cfg, pc) [] (v', cfg, pc')
| StepCopy :
    forall v cfg pc v' dst src pc',
      fetch pc cfg = Some (Copy dst src pc') ->
      v' = (dst, lkup src v) :: v ->
      step (v, cfg, pc) [] (v', cfg, pc')
| StepOp :
    forall v cfg pc n v' dst op arg_l arg_r pc',
      fetch pc cfg = Some (Op dst op arg_l arg_r pc') ->
      n = denote_binop op (lkup arg_l v) (lkup arg_r v) ->
      v' = (dst, n) :: v ->
      step (v, cfg, pc) [] (v', cfg, pc')
| StepCondTrue :
    forall v cfg pc test pc_t pc_f,
      fetch pc cfg = Some (Cond test pc_t pc_f) ->
      lkup test v <> 0 ->
      step (v, cfg, pc) [] (v, cfg, pc_t)
| StepCondFalse :
    forall v cfg pc test pc_t pc_f,
      fetch pc cfg = Some (Cond test pc_t pc_f) ->
      lkup test v = 0 ->
      step (v, cfg, pc) [] (v, cfg, pc_f)
| StepOut :
    forall v cfg pc n arg pc',
      fetch pc cfg = Some (Out arg pc') ->
      n = lkup arg v ->
      step (v, cfg, pc) [n] (v, cfg, pc').
Local Hint Constructors step : hints.

Definition interp_step (v : valuation) (code : cfg) (pc : node)
           : option (trace * state) :=
  match fetch pc code with
  | None =>
      None
  | Some (Nop pc') =>
      Some ([], (v, code, pc'))
  | Some (Load dst n pc') =>
      Some ([], ((dst, n) :: v, code, pc'))
  | Some (Copy dst src pc') =>
      Some ([], ((dst, lkup src v) :: v, code, pc'))
  | Some (Op dst op arg_l arg_r pc') =>
      Some ([], ((dst, denote_binop op (lkup arg_l v) (lkup arg_r v)) :: v, code, pc'))
  | Some (Cond test pc_t pc_f) =>
      if Nat.eq_dec (lkup test v) 0
      then Some ([], (v, code, pc_f))
      else Some ([], (v, code, pc_t))
  | Some (Out arg pc') =>
      Some ([lkup arg v], (v, code, pc'))
  | Some Halt =>
      None
  end.

Lemma interp_step_step :
  forall v code pc t v' pc',
  interp_step v code pc = Some (t, (v', code, pc')) ->
  step (v, code, pc) t (v', code, pc').
Proof.
  unfold interp_step; intros.
  break_match_hyp; [| congruence].
  destruct i; invc H.
  - eapply StepNop; eauto. 
  - eapply StepLoad; eauto.
  - eapply StepCopy; eauto.
  - eapply StepOp; eauto.
  - break_if; invc H1.
    + eapply StepCondFalse; eauto.
    + eapply StepCondTrue; eauto.
  - eapply StepOut; eauto.
Qed.

Lemma step_interp_step :
  forall v code pc t v' pc',
    step (v, code, pc) t (v', code, pc') ->
    interp_step v code pc = Some (t, (v', code, pc')).
Proof.
  unfold interp_step; intros.
  invc H; find_rewrite; auto.
  break_if; auto; congruence.
  break_if; auto; congruence.
Qed.

Definition successors_i (i : instr) : list node :=
  match i with
  | Nop pc' => [pc']
  | Load _ _ pc' => [pc']
  | Copy _ _ pc' => [pc']
  | Op _ _ _ _ pc' => [pc']
  | Cond _ pc_t pc_f => [pc_t; pc_f]
  | Out _ pc' => [pc']
  | Halt => []
  end.

Fixpoint successors pc code : list node :=
  match code with
  | [] => []
  | (nd, instr) :: code' =>
      if Nat.eq_dec pc nd
      then successors_i instr
      else successors pc code'
  end.

Fixpoint predecessors pc code : list node :=
  match code with
  | [] => []
  | (nd, instr) :: code' =>
      if in_dec Nat.eq_dec pc (successors_i instr)
      then nd :: predecessors pc code'
      else predecessors pc code'
  end.

Lemma fetch_some_in :
  forall code pc i,
    fetch pc code = Some i ->
    In (pc, i) code.
Proof.
  induction code as [| [pc' i'] code];
    simpl; intros pc i Hfetch.
  - discriminate.
  - break_if; auto; subst.
    invc Hfetch; auto.
Qed.

Definition successors' pc code : list node :=
  match fetch pc code with
  | None => []
  | Some i => successors_i i
  end.

Lemma successors_successors' :
  forall code pc,
    successors pc code = successors' pc code.
Proof.
  unfold successors'.
  induction code as [| [pc' i'] code];
    simpl; intros pc; auto.
  break_if; subst; auto.
Qed.

Lemma successors'_ok :
  forall v code pc t v' code' pc',
    step (v, code, pc) t (v', code', pc') ->
    In pc' (successors' pc code).
Proof.
  unfold successors'.
  intros v code pc t v' code' pc' Hstep.
  invc Hstep; simpl; find_rewrite; simpl; auto.
Qed.

Lemma successors_ok :
  forall v code pc t v' code' pc',
    step (v, code, pc) t (v', code', pc') ->
    In pc' (successors pc code).
Proof.
  intros. rewrite successors_successors'.
  eapply successors'_ok; eauto.
Qed.

Lemma fetch_some_in_predecessors :
  forall code pc i,
    fetch pc code = Some i ->
    forall pc_succ,
      In pc_succ (successors_i i) ->
      In pc (predecessors pc_succ code).
Proof.
  induction code as [| [pc' i'] code];
    simpl; intros pc i Hfetch pc_succ Hin.
  - discriminate.
  - break_if; simpl.
    + break_if; subst; auto.
      right; eapply IHcode; eauto.
    + break_if; subst; auto.
      invc Hfetch. destruct n; auto.
      eapply IHcode; eauto.
Qed.

Lemma predecessors_ok :
  forall v code pc t v' code' pc',
    step (v, code, pc) t (v', code', pc') ->
    In pc (predecessors pc' code).
Proof.
  intros v code pc t v' code' pc' Hstep.
  invc Hstep; simpl;
    eapply fetch_some_in_predecessors; eauto;
    simpl; auto.
Qed.

Inductive final : state -> Prop :=
| Final :
  forall v cfg pc,
    fetch pc cfg = Some Halt ->
    final (v, cfg, pc).

Lemma final_nostep :
  forall s,
    final s ->
    no_step step s.
Proof.
  unfold no_step, not.
  intros s Hfinal t s' Hstep.
  invc Hfinal. invc Hstep; congruence.
Qed.

Inductive prog :=
| Prog (code : cfg) (entry : node).

Definition prog_to_trsys (v : valuation) prog : trsys nat state :=
  match prog with Prog code entry =>
    {| Init := fun s => s = (v, code, entry);
      Step := step;
      FinalNoStep := final_nostep |}
  end.

Ltac fetch :=
  match goal with
  | [ H1 : fetch ?pc ?cfg = Some ?i1,
      H2 : fetch ?pc ?cfg = Some ?i2 |- _ ] =>
        rewrite H1 in H2; invc H2
  end.

Lemma step_det :
  forall s1 t12 s2,
    step s1 t12 s2 ->
    forall t13 s3,
      step s1 t13 s3 ->
      t12 = t13 /\ s2 = s3.
Proof.
  induction 1; intros t13 s3 Hstep;
    invc Hstep; fetch; split; congruence.
Qed.

Lemma trsys_is_det :
  forall v p,
    is_det_sys (prog_to_trsys v p).
Proof.
  intros v [code entry]; ee; simpl; intros.
  - congruence.
  - eapply step_det; eauto.
Qed. 

Lemma trsys_has_init :
  forall v p,
    has_init_state (prog_to_trsys v p).
Proof.
  unfold has_init_state.
  intros v [code entry]; simpl.
  eauto.
Qed.

Lemma trsys_has_single_events :
  forall v p,
    single_events (prog_to_trsys v p).
Proof.
  unfold single_events.
  intros v [code entry] s1 t s2 Hstep.
  invc Hstep; auto.
Qed.

Lemma can_step :
  forall v cfg pc instr,
    fetch pc cfg = Some instr ->
    can_step step (v, cfg, pc) \/ final (v, cfg, pc).
Proof.
  unfold can_step.
  intros v cfg pc instr Hfetch.
  destruct instr.
  - left; ee; ee. eapply StepNop; eauto.
  - left; ee; ee. eapply StepLoad; eauto.
  - left; ee; ee. eapply StepCopy; eauto.
  - left; ee; ee. eapply StepOp; eauto.
  - left; ee. destruct (Nat.eq_dec (lkup test v) 0).
    + exists (v, cfg, next_false); eapply StepCondFalse; eauto.
    + exists (v, cfg, next_true); eapply StepCondTrue; eauto.
  - left; ee; ee. eapply StepOut; eauto.
  - right; ee.
Qed.

End ControlFlowGraph.


(* translating ThreeAddressCode programs for Control Flow Graphs *)
Module TAC_to_CFG.

Module S := ThreeAddressCode.
Module T := ControlFlowGraph.

Definition translate_op (op : S.binop) : T.binop :=
  match op with
  | S.Add => T.Add
  | S.Sub => T.Sub
  | S.Mul => T.Mul
  end.

(*
  To translate a TAC program to a CFG, we work "backwards" through the TAC program.
  At each iteration, we take:
    pcDone  -- the pc translated code should jump to after execution
    pcFresh -- the smallest pc that does not yet map to any instruction
    cfg     -- the CFG constructed so far from later code
  Each iteration also produces updated versions of these values.
*)

Record trans_state :=
  { pc_fresh : T.node
  ; pc_next : T.node
  ; cfg : T.cfg }.

Definition set_pc_fresh (ts : trans_state) (pc : T.node) :=
  {| pc_fresh := pc
   ; pc_next := pc_next ts
   ; cfg := cfg ts |}.

Definition set_pc_next (ts : trans_state) (pc : T.node) :=
  {| pc_fresh := pc_fresh ts
   ; pc_next := pc
   ; cfg := cfg ts |}.

Definition set_cfg (ts : trans_state) (code : T.cfg) :=
  {| pc_fresh := pc_fresh ts
   ; pc_next := pc_next ts
   ; cfg := code |}.

Fixpoint translate_cmd (ts : trans_state) (cmd : S.cmd) : trans_state :=
  match cmd with
  | S.Skip =>
      let pc := pc_fresh ts in
      {| pc_fresh := S pc
       ; pc_next := pc
       ; cfg := (pc, T.Nop (pc_next ts)) :: cfg ts |}
  | S.Assign x (S.Const n) =>
      let pc := pc_fresh ts in
      {| pc_fresh := S pc
      ; pc_next := pc
      ; cfg := (pc, T.Load x n (pc_next ts)) :: cfg ts |}
  | S.Assign x (S.Var y) =>
      let pc := pc_fresh ts in
      {| pc_fresh := S pc
      ; pc_next := pc
      ; cfg := (pc, T.Copy x y (pc_next ts)) :: cfg ts |}
  | S.Assign x (S.Binop op y z) =>
      let pc := pc_fresh ts in
      {| pc_fresh := S pc
      ; pc_next := pc
      ; cfg := (pc, T.Op x (translate_op op) y z (pc_next ts)) :: cfg ts |}
  | S.Seq c1 c2 =>
      (* TODO maybe should put a nop in here for lockstep? *)
      translate_cmd (translate_cmd ts c2) c1
  | S.If x c1 c2 =>
      let pc_merge := pc_next ts in
      let ts2 := translate_cmd ts c2 in
      let ts1 := translate_cmd (set_pc_next ts2 pc_merge) c1 in
      let pc := pc_fresh ts1 in
      {| pc_fresh := S pc
       ; pc_next := pc
       ; cfg := (pc, T.Cond x (pc_next ts1) (pc_next ts2)) :: cfg ts1 |}
  | S.While x body =>
      let pc := pc_fresh ts in
      let ts_body :=
        translate_cmd
          {| pc_fresh := S pc
           ; pc_next := pc
           ; cfg := cfg ts |}
          body
      in
      {| pc_fresh := pc_fresh ts_body
       ; pc_next := pc
       ; cfg := (pc, T.Cond x (pc_next ts_body) (pc_next ts)) :: cfg ts_body |}
  | S.Out x =>
      let pc := pc_fresh ts in
      {| pc_fresh := S pc
      ; pc_next := pc
      ; cfg := (pc, T.Out x (pc_next ts)) :: cfg ts |}
  end.

Definition translate_prog (cmd : S.cmd) : T.node * T.cfg :=
  let ts0 :=
    {| pc_fresh := 1
     ; pc_next := 0
     ; cfg := [(0, T.Halt)] |}
  in
  let tsN := translate_cmd ts0 cmd in
  (pc_next tsN, cfg tsN).

Definition is_fresh_pc (code : T.cfg) pc :=
  forall pc' i,
    In (pc', i) code ->
    pc' < pc.

Lemma translate_cmd_preserves_fresh_same :
  forall cmd ts1 ts2,
    pc_fresh ts1 = pc_fresh ts2 ->
    pc_fresh (translate_cmd ts1 cmd) = pc_fresh (translate_cmd ts2 cmd).
Proof.
  induction cmd; simpl; intros ts1 ts2 Hfresh; auto.
  - destruct e; simpl; auto.
  - f_equal.
    eapply IHcmd1; eauto.
    eapply IHcmd2; eauto.
  - rewrite Hfresh; auto.
Qed.

Lemma translate_cmd_pc_fresh_ignore_pc_next :
  forall cmd ts pc,
    pc_fresh (translate_cmd (set_pc_next ts pc) cmd)
      = pc_fresh (translate_cmd ts cmd).
Proof.
  intros cmd ts pc.
  apply translate_cmd_preserves_fresh_same; auto.
Qed.

Lemma translate_cmd_pc_fresh_monotonic :
  forall cmd ts ts',
    translate_cmd ts cmd = ts' ->
    pc_fresh ts < pc_fresh ts'.
Proof.
  induction cmd; simpl; intros ts ts' Htrans.
  - invc Htrans; simpl in *; auto.
  - destruct e; invc Htrans; simpl in *; auto.
  - remember (translate_cmd ts cmd2) as ts2; symmetry in Heqts2.
    find_apply_hyp_hyp. find_apply_hyp_hyp. lia.
  - invc Htrans; simpl in *; invc H.
    rewrite translate_cmd_pc_fresh_ignore_pc_next.
    eapply lt_trans. eapply IHcmd2; eauto.
    eapply lt_trans. eapply IHcmd1; eauto.
    auto.
  - invc Htrans; simpl in *; invc H.
    eapply lt_trans; [| apply IHcmd; auto].
    auto.
  - invc Htrans; simpl in *; auto.
Qed.

(* 
Lemma translate_cmd_preserves_fetch :
  forall cmd ts ts',
    translate_cmd ts cmd = ts' ->
    forall pc,
      pc < pc_fresh ts ->
      T.fetch pc (cfg ts') = T.fetch pc (cfg ts).
Proof.
  induction cmd; intros ts ts' Htrans pc Hpc.
  - invc Htrans; simpl in *; invc H.
    break_if; subst; auto. lia.
  - destruct e; invc Htrans; simpl in *; invc H.
    + break_if; subst; auto. lia.
    + break_if; subst; auto. lia.
    + break_if; subst; auto. lia.
  - eapply eq_trans; revgoals.
      eapply IHcmd2; eauto.
    eapply eq_trans; revgoals.
      eapply IHcmd1; eauto.
      eapply lt_trans; revgoals.
      eapply translate_cmd_pc_fresh_monotonic; eauto. auto.
    auto.
Admitted.

Inductive match_code : S.cmd -> T.cfg -> T.node -> T.node -> Prop :=
| MCSkip :
    forall cfg pc pc',
      T.fetch pc cfg = Some (T.Nop pc') ->
      match_code S.Skip cfg pc pc'
| MCAssignConst :
    forall x n cfg pc pc',
      T.fetch pc cfg = Some (T.Load x n pc') ->
      match_code (S.Assign x (S.Const n)) cfg pc pc'
| MCAssignVar :
    forall x y cfg pc pc',
      T.fetch pc cfg = Some (T.Copy x y pc') ->
      match_code (S.Assign x (S.Var y)) cfg pc pc'
| MCAssignBinop :
    forall x op y z cfg pc pc',
      T.fetch pc cfg = Some (T.Op x (translate_op op) y z pc') ->
      match_code (S.Assign x (S.Binop op y z)) cfg pc pc'
| MCSeq :
    forall c1 c2 cfg pc1 pc2 pc3,
      match_code c1 cfg pc1 pc2 ->
      match_code c2 cfg pc2 pc3 ->
      match_code (S.Seq c1 c2) cfg pc1 pc3
| MCIf :
    forall x c_t c_f cfg pc pc_t pc_f pc_merge,
      T.fetch pc cfg = Some (T.Cond x pc_t pc_f) ->
      match_code c_t cfg pc_t pc_merge ->
      match_code c_f cfg pc_f pc_merge ->
      match_code (S.If x c_t c_f) cfg pc pc_merge
| MCWhile :
    forall x body cfg pc pc_t pc_f,
      T.fetch pc cfg = Some (T.Cond x pc_t pc_f) ->
      match_code body cfg pc_t pc ->
      match_code (S.While x body) cfg pc pc_f
| MCOut :
    forall x cfg pc pc',
      T.fetch pc cfg = Some (T.Out x pc') ->
      match_code (S.Out x) cfg pc pc'
| MCHalt :
    forall cfg pc,
      T.fetch pc cfg = Some T.Halt ->
      match_code S.Skip cfg pc pc.

Lemma match_code_cons_fresh :
  forall cmd cfg pc1 pc2,
    match_code cmd cfg pc1 pc2 ->
    forall freshPC freshInstr,
      (forall pc instr, In (pc, instr) cfg -> pc < freshPC) ->
      match_code cmd ((freshPC, freshInstr) :: cfg) pc1 pc2.
Proof.
  (* TODO de-copy-paste (write some Ltac) *)
  induction 1; intros freshPC freshInstr Hfresh.
  - ee; simpl. break_if; auto; subst.
    find_apply_lem_hyp fetch_some_in.
    find_apply_hyp_hyp. lia.
  - ee; simpl. break_if; auto; subst.
    find_apply_lem_hyp fetch_some_in.
    find_apply_hyp_hyp. lia.
  - ee; simpl. break_if; auto; subst.
    find_apply_lem_hyp fetch_some_in.
    find_apply_hyp_hyp. lia.
  - ee; simpl. break_if; auto; subst.
    find_apply_lem_hyp fetch_some_in.
    find_apply_hyp_hyp. lia.
  - ee.
  - ee; simpl. break_if; auto; subst.
    find_apply_lem_hyp fetch_some_in.
    find_apply_hyp_hyp. lia.
  - ee; simpl. break_if; auto; subst.
    find_apply_lem_hyp fetch_some_in.
    find_apply_hyp_hyp. lia.
  - ee; simpl. break_if; auto; subst.
    find_apply_lem_hyp fetch_some_in.
    find_apply_hyp_hyp. lia.
  - eapply MCHalt; eauto; simpl.
    break_if; auto; subst.
    find_apply_lem_hyp fetch_some_in.
    find_apply_hyp_hyp. lia.
Qed.

Lemma translate_cmd_preserves_match_code :
  forall cA ts ts',
    translate_cmd ts cA = ts' ->
    forall cB pc1 pc2,
      match_code cB (cfg ts) pc1 pc2 ->
      match_code cB (cfg ts') pc1 pc2.
Proof.
  induction cA; simpl; intros ts ts' Htrans cB pc1 pc2 Hmatch.
  - invc Htrans; simpl in *.
Admitted.

Lemma translate_cmd_match_code :
  forall c ts ts',
    translate_cmd ts c = ts' ->
    match_code c (cfg ts') (pc_next ts') (pc_next ts).
Proof.
  induction c; simpl; intros ts ts' Htrans.
  - invc Htrans; simpl.
    ee; simpl. apply if_nat_eq_refl.
  - destruct e; invc Htrans; simpl.
    + ee; simpl. apply if_nat_eq_refl.
    + ee; simpl. apply if_nat_eq_refl.
    + ee; simpl. apply if_nat_eq_refl.
  - remember (translate_cmd ts c2) as ts2; symmetry in Heqts2.
    find_apply_hyp_hyp.
    find_apply_hyp_hyp.
    econstructor.
      apply Htrans.
      apply Heqts2.
     ee. ee.
  - invc Htrans; simpl.
Admitted.

*)

Definition test01 :=
  S.Seq (S.Assign "x" (S.Const 3)) (
  S.Seq (S.Assign "one" (S.Const 1))
    (S.While "x" (S.Assign "x" (S.Binop S.Sub "x" "one")))).

Definition test02 :=
  S.Seq (S.Assign "x" (S.Const 3)) (
  S.Seq (S.Assign "one" (S.Const 1)) (
  S.Seq (S.Assign "two" (S.Const 2)) (
  S.Seq (S.Assign "flipflop" (S.Const 0))
    (S.While "x"
      (S.If "flipflop"
        (S.Seq (S.Assign "x" (S.Binop S.Sub "x" "one")) (S.Assign "flipflop" (S.Const 0)))
        (S.Seq (S.Assign "x" (S.Binop S.Sub "x" "two")) (S.Assign "flipflop" (S.Const 1)))))))).

Ltac step :=
  match goal with
  | [ |- star T.step _ _ _ ] =>
      eapply star_front; [
        eapply T.interp_step_step; eauto; cbn; auto; fail
      | | listy]
  end.

Lemma test :
  let (pc0, cfg) := translate_prog test02 in
  exists v' pc',
    star T.step ([], cfg, pc0) [] (v', cfg, pc') /\
    T.fetch pc' cfg = Some T.Halt.
Proof.
  simpl. ee; ee; split.
  - repeat step. eapply star_refl.
  - cbn; auto.
Qed.

End TAC_to_CFG.