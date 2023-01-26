Require Import Lia.

(* enable type inference *)
Set Implicit Arguments.

Module TrSys.

(*
CREDITS: This formalization follows the development from Chlipala's
excellent FRAP textbook: http://adam.chlipala.net/frap/
*)


Module FirstExample.

(*
    x = 5;
    while 1 loop
      x = x + 1
    done
*)
Definition counter_state : Type := nat.

Definition counter_init (s : counter_state) : Prop :=
  s = 5.

Definition counter_step (s1 s2 : counter_state) : Prop :=
  s2 = S s1. (* s1 + 1 = s2 *)

(* ... now what?! *)

End FirstExample.

(* transitive reflexive closure of "R" *)
Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| trc_refl :
    forall x,
      trc R x x
| trc_front :
    forall x y z,
      R x y ->
      trc R y z ->
      trc R x z.

(* need to prove it's actually transitive! *)
Lemma trc_transitive :
  forall {A} (R : A -> A -> Prop) x y,
    trc R x y ->   (* if   x can reach y following the trc of R *)
    forall z,
      trc R y z -> (* and  y can reach z following the trc of R *)
      trc R x z.   (* then x can reach z following the trc of R *)
Proof.
  (* we already know everything we need for this kind of proof,
     but remember to DO INDUCTION ON THE DERIVATION!
     (Like we saw for le last week!)*)
  intros A R x y Hxy.
  induction Hxy; intros.
  - assumption.
  - apply trc_front with (y := y). (* have to use "y0" b/c "y" in scope... *)
    + assumption.
    + apply IHHxy. assumption.

  (* this proof is easier with "eapply" and "eauto" *)
  Restart.
  intros A R x y Hxy.
  induction Hxy; intros.
  - assumption.
  - eapply trc_front; eauto.

  (* with a little sugar, it gets even shorter *)
  Restart.
  intros A R x y Hxy.
  induction Hxy; auto.
  econstructor; eauto. (* find and apply constructor for the goal's type *)
Qed.

(* a generic definition of transition systems *)
Record trsys X :=
  { Init : X -> Prop
  ; Step : X -> X -> Prop }.

(* what states can a transition system reach? *)
Definition reachable {A} (sys : trsys A) (sN : A) : Prop :=
  exists s0,
    sys.(Init) s0 /\
    trc sys.(Step) s0 sN.

(* using the above defs *)
Definition counter_state : Type := nat.
Definition counter_init (s : counter_state) : Prop := s = 5.
Definition counter_step (s1 s2 : counter_state) : Prop := s2 = S s1.

Definition counter_sys : trsys counter_state := {|
  Init := counter_init;
  Step := counter_step
|}.

(* we will get stuck if we just try to prove our goal! *)
Lemma counter_sys_ok :
  forall s,
    reachable counter_sys s ->
    5 <= s.
Proof.
Abort.



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
  intros state sys P Q HP Himp s0 Hinit sN Htrc.
  apply Himp.
  apply HP with (s0 := s0).
  - apply Hinit.
  - apply Htrc.
  Restart.

  (* Or more quickly: *)
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

(* Now we can finally prove our counter system! *)
Definition counter_ge_5 (s : counter_state) : Prop :=
  s >= 5.

Theorem counter_ge_5_invariant :
  is_invariant counter_sys counter_ge_5.
Proof.
  apply invariant_induction.
  - unfold initially_holds. simpl.
    unfold counter_init, counter_ge_5.
    intros. lia.
  - unfold closed_under_step. simpl.
    unfold counter_step, counter_ge_5.
    intros s1 IH s2 Hstep.
    lia.
Qed.

(* But often need to strengthen... *)
Definition counter_ne_4 (s : counter_state) : Prop :=
  s <> 4.

Theorem counter_ne_4_invariant :
  is_invariant counter_sys counter_ne_4.
Proof.
  apply invariant_induction.
  - (* base case is no problem *)
    unfold initially_holds. simpl.
    unfold counter_init, counter_ne_4.
    intros.
    lia.
  - (* but the inductive case gets wedged :\ *)
    unfold closed_under_step. simpl.
    unfold counter_step, counter_ne_4.
    intros s1 IH s2 Hstep.
    Fail lia. (* oh no! *)
    (* Our induction hypothesis is useless!
       It only tells us that s1 is not 4,
       but what if s1 is 3?? *)

  (* let's try again *)
  Restart.

  (* Our property is not inductive.
  
     To see why consider this "counter example to induction" (CTI):
        The state 3 satisfies our target invariant "counter_ne_4", AND
        the state 3 steps to the state 4, BUT
        the state 4 does NOT satisfy our target invariant!

     Instead of trying to prove "counter_ne_4" directly by induction,
     we need to use a *stronger* invariant that will always 'imply itself'
     after every step!
     
     ... like counter_ge_5 above ;)
   *)
  apply invariant_implies with (P := counter_ge_5).
  - apply counter_ge_5_invariant.
  - unfold counter_ge_5, counter_ne_4.
    intros.
    lia.
Qed.

(*
    x = 0;
    y = input;
    while y loop
      x = x + 1;
      y = y - 1
    done
*)
Definition two_counters_state : Type := nat * nat.

Definition two_counters_init (input : nat) (s : two_counters_state) : Prop :=
  s = (0, input).

(*
Definition two_counters_step (s1 s2 : two_counters_state) : Prop :=
  ...
*)

Inductive two_counters_step :
    two_counters_state -> two_counters_state -> Prop :=
| two_counters_step_step :
    forall x y,
      two_counters_step (x, S y) (S x, y).

Definition two_counters_sys (input : nat) : trsys two_counters_state := {|
  Init := two_counters_init input;
  Step := two_counters_step
|}.

(* this program terminates! *)
Definition two_counters_final (s : two_counters_state) : Prop :=
  snd s = 0.

(* a specification *)
Definition two_counters_safe (input : nat) (s : two_counters_state) : Prop :=
  two_counters_final s ->
  fst s = input.

(* ... which is not inductive! *)
Theorem two_counters_safe_invariant :
  forall input,
    is_invariant (two_counters_sys input) (two_counters_safe input).
Proof.

Abort.

(* step back and strengthen! *)
Definition two_counters_inv (input : nat) (s : two_counters_state) : Prop :=
  let (x, y) := s in
  x + y = input.

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

Lemma two_counters_inv_invariant :
  forall input,
    is_invariant (two_counters_sys input) (two_counters_inv input).
Proof.
  invariant_induction_boilerplate; lia.
  Restart.


  apply invariant_induction.
  - unfold initially_holds. simpl.
    unfold two_counters_init, two_counters_inv.
    intros s H.
    subst s.
    reflexivity.
  - unfold closed_under_step. simpl.
    unfold two_counters_inv.
    intros [x1 y1] IH [x2 y2] Hstep. 
    inversion Hstep; subst.
    lia.
Qed.

(* no sweat with the stronger invariant! *)
Theorem two_counters_safe_invariant :
  forall input,
    is_invariant (two_counters_sys input) (two_counters_safe input).
Proof.
  intros input.
  apply invariant_implies with (P := two_counters_inv input).
  - apply two_counters_inv_invariant.
  - unfold two_counters_inv, two_counters_safe, two_counters_final.
    intros [x y] Hinv Hfinal.
    simpl in *.
    lia.
Qed.

(*

The recipe is always the same:

(A) Given a program, define a transition system for it by answering
    the 3 questions:
      (1) What are the states?
      (2) What are the initial states?
      (3) What is the transition relation?

(B) Figure out what you want to prove about all the reachable states
    of the system.

(C) The property from (B) is usually not inductive, so figure out a
    *stronger* property that IS inductive an prove that using
    "invariant_induction".

(D) Come back and finish the proof for (B) using "invariant_implies".
*)

(* Factorial

    n = input;
    acc = 1;
    while n loop
      acc = acc * n;
      n = n - 1
    done
*)

(* pairs representing the values of "(n, acc)" *)
Definition fact_state : Type := nat * nat.

(* again parameterized over the input to the system *)
Definition fact_init (input : nat) (s : fact_state) :=
  s = (input, 1).

(* the program is 'done' when "n" reaches 0 *)
Definition fact_final (s : fact_state) : Prop :=
  fst s = 0.

(* each time through the loop, multiply "acc" by "n" then decrement "n" *)
Inductive fact_step : fact_state -> fact_state -> Prop :=
| fact_step_step : forall n acc,
  fact_step (S n, acc) (n, acc * S n).

Definition fact_sys (input : nat) : trsys fact_state := {|
  Init := fact_init input;
  Step := fact_step
|}.

(* Our specification is showing that the transition system,
   once it terminates, will have computed the same thing as
   another 'math only' version of factorial in pure Coq. *)
Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => fact n' * S n'
  end.

Definition fact_safe (input : nat) (s : fact_state) : Prop :=
  fact_final s ->
  snd s = fact input.

(* of course, the target property is not inductive... *)
Theorem fact_safe_invariant :
  forall input,
    is_invariant (fact_sys input) (fact_safe input).
Proof.
  (* Our property only talks about final states. It won't be inductive!
     But in case you were to give it a try, here's what would happen. *)
  intros input.
  apply invariant_induction.
  - unfold initially_holds. simpl.
    unfold fact_init, fact_safe, fact_final.
    intros s0 Hinit Hfinal.
    subst s0.
    simpl in *.
    subst input.
    simpl.
    reflexivity.
  - unfold closed_under_step. simpl.
    unfold fact_safe, fact_final.
    intros s1 IH s2 Hstep Hfinal2.
    inversion Hstep; subst.
    simpl in *.
    subst.
    (* As expected, our induction hypothesis is useless because it only gives us
      information when the counter is zero. *)
Abort.

(*
We need to state an invariant that says something useful about all the states of
the system, not just the final states.
*)
Definition fact_inv (input : nat) (s : fact_state) : Prop :=
  let (n, acc) := s in
  fact input = fact n * acc.

(*
It's all easy with the right invariant.
*)
Theorem fact_inv_invariant : forall input,
  is_invariant (fact_sys input) (fact_inv input).
Proof.
  intros input.
  apply invariant_induction.
  - unfold initially_holds. simpl.
    unfold fact_init, fact_inv.
    intros s Hinit.
    subst.
    lia.
  - unfold closed_under_step. simpl.
    unfold fact_inv.
    intros [n1 acc1] IH [n2 acc2] Hstep.
    inversion Hstep; subst.
    simpl in *.
    lia.
Qed.

(*
And now we can prove the target property with "invariant_implies".
*)
Theorem fact_safe_invariant :
  forall input,
    is_invariant (fact_sys input) (fact_safe input).
Proof.
  intros input.
  apply invariant_implies with (P := fact_inv input).
  - apply fact_inv_invariant.
  - unfold fact_inv, fact_safe, fact_final.
    intros [n acc] Hinv Hfinal.
    simpl in *.
    subst.
    simpl in *.
    lia.
Qed.

(*
ROBOT 🤖

      x = 0;
      y = 5;
      while ?? loop
        when ?? then
          y = y + 1
         else
          x = x + 1;
          y = y - 1
      done
      done

This one is a little different -- we didn't actually specify how long it
runs or when it decides to increment "y" or instead increment "x" and
decrement "y". The "??" above conceptually mean 'some complex code I don't
want to think about, so I will abstract out as a nondeterministic choice'.
*)

Require Import ZArith.

(* states are pairs of *integers* representing "(x, y)" *)
Definition robot_state : Type := Z * Z.

(* our robot always starts at "(0, 5)" *)
Definition robot_init (s : robot_state) :=
  s = (0, 5)%Z.

(* Our robot can move either down and to the right or
   instead move up. We don't say when it choose to do
   one or other -- it's modeled as a nondeterministic choice! *)
Inductive robot_step : robot_state -> robot_state -> Prop :=
| robot_step_southeast :
  forall x y,
    robot_step (x, y) (x + 1, y - 1)%Z
| robot_step_north :
  forall x y,
    robot_step (x, y) (x, y + 1)%Z.

Definition robot_sys : trsys robot_state := {|
  Init := robot_init;
  Step := robot_step
|}.

(* Suppose we want to make sure the robot never
   gets too close to the origin. *)
Definition robot_safe (s : robot_state) : Prop :=
  let (x, y) := s in
  (x * x + y * y > 9)%Z.

(* But of course our target propery is not inductive... *)
Theorem robot_safe_invariant :
  is_invariant robot_sys robot_safe.
Proof.
  (* We know this is not inductive. But here's what would happen if you try. *)
  apply invariant_induction.
  - unfold initially_holds. simpl.
    unfold robot_init, robot_safe.
    intros [x y] Hinit.
    inversion Hinit; subst.
    lia.
  (* halfway there! :P *)
  - unfold closed_under_step. simpl.
    unfold robot_safe.
    intros [x1 y1] IH [x2 y2] Hstep.
    inversion Hstep; subst. (* two possible steps, so we get two subgoals *)
    + (* case southeast *)
      Fail lia.
      Fail nia.
      (* In fact, this is just not true. For example, x1 = -2, y1 = 3 is a
         counterexample. *)
      admit.
    + (* case north *)
      Fail lia.
      Fail nia.
      (* This one is also false. For example, x1 = 1, y1 = -3. *)
Abort.

(* so we find a stronger invariant *)
Definition robot_inv (s : robot_state) : Prop :=
  let (x, y) := s in
  (x + y >= 5)%Z.

(* which is easy to prove by "invariant_induction" *)
Lemma robot_inv_invariant :
  is_invariant robot_sys robot_inv.
Proof.
  apply invariant_induction.
  - unfold initially_holds. simpl.
    unfold robot_init, robot_inv.
    intros [x y] Hinit.
    inversion Hinit; subst.
    lia.
  - unfold closed_under_step. simpl.
    unfold robot_inv.
    intros [x1 y1] IH [x2 y2] Hstep.
    inversion Hstep; subst. (* two possible steps, so we get two subgoals *)
    + (* case southeast *)
      lia.
    + (* case north *)
      lia.
Qed.

(* and we show that this stronger property implies the target proptery of
   always avoiding the area 'too close to the origin': *)
Theorem robot_safe_invariant :
  is_invariant robot_sys robot_safe.
Proof.
  apply invariant_implies with (P := robot_inv).
  - apply robot_inv_invariant.
  - unfold robot_inv, robot_safe.
    intros [x y] Hinv.
    Fail lia.
    Fail nia.
    cut (x * x + (5 - x) * (5 - x) > 9)%Z; [nia|].
    clear y Hinv.
    Fail nia.
    replace (x * x + (5 - x) * (5 - x))%Z
    with (2 * x * x - 10 * x + 25)%Z by lia.
    Fail nia.
    assert (x >= 3 \/ x <= 2)%Z by lia. (* :O *)
    nia. (* :O :O :O *)
    (* Why did we pick that case split? Because the quadratic polynomial
           2 * x * x - 10 * x + 25
       has a minimum at x = 2.5. On either side of this minimum, the polynomial
       gets bigger as x gets farther away from 2.5. So in either case, nia is
       (probably) able to give a lower bound for the polynomial in terms of its
       value at 2 or 3. *)
    (* This is completely black magic. We won't do many proofs like this.
       But it's fun to see one :) *)
Qed.

(* ANOTHER ROBOT PROPERTY *)

(* Here's another property we may want to know about our robot's 
   reachable states: *)
Definition robot_x_nonneg (s : robot_state) : Prop :=
  let (x, y) := s in
  (x >= 0)%Z.

(*
Now our goal is to develop some custom tactics to make doing these proofs
a bit more convenient. First we'll want a tactic that can do all the
unfolding steps for us:

Given an expression P, this custom tactic tries to find the predicate at
the "head" of P, and unfolds that. Never throws an error, just silently
does nothing.
*)
Ltac unfold_predicate P :=
  match P with
  | ?head _ => unfold_predicate head
  | _ => try unfold P
  end.

(*
Next we'll want a tactic that wraps up all the normal "invariant_induction"
'boilerplate' that we've been copy/pasting in each example:

This custom tactic applies the invariant_induction lemma and sets up subgoals
for the base case and each inductive case. While somewhat long winded, it's
not doing anything we haven't done a couple times by hand above.
*)
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

(* this makes life much easier ;) *)
Theorem robot_x_nonneg_invariant :
  is_invariant robot_sys robot_x_nonneg.
Proof.
  (* watch this! *)
  invariant_induction_boilerplate; lia.
Qed.


(*
So far, we have been proving that all the states reachable by a transition
system are 'safe' -- they satisfy some predicate that we are using to specify
which states are the 'good states'.

We generally call systems that avoid bad states "safe".

But what if we flip this around?

What if instead we wanted to characterize all the states that we would like
for our system to be able to reach and then prove that it can reach all those
states? We do this less often in practice, but for the robot example, it's
not too hard:
*)

Definition robot_reach (s : robot_state) : Prop :=
  let (x, y) := s in
  (x + y >= 5 /\ x >= 0)%Z.

Theorem robot_reach_invariant :
  is_invariant robot_sys robot_reach.
Proof.
  eapply invariant_implies.
  eapply invariant_and.
  apply robot_inv_invariant.
  apply robot_x_nonneg_invariant.
  simpl.
  unfold robot_inv, robot_x_nonneg, robot_reach.
  intros [x y]; auto.

  Restart.
  invariant_induction_boilerplate; lia.
Qed.

Theorem robot_characterize_reachable :
  forall s,
    robot_reach s ->
    reachable robot_sys s.
Proof.
Abort.

Lemma robot_vertical_reachable :
  forall x y1 y2,
    reachable robot_sys (x, y1) ->
    (y2 >= y1)%Z ->
    reachable robot_sys (x, y2).
Proof.
  intros x y1 y2 Hy1 Hle.
  apply Zlt_lower_bound_ind with (z := y1) (x := y2); [|lia].
  intros z IH Hz.
  apply Zle_lt_or_eq in Hz.
  destruct Hz as [Hz|Hz].
  - specialize (IH (z - 1)%Z).
    eapply reachable_transitive.
    + apply IH. lia.
    + eapply trc_front.
      * simpl. apply robot_step_north.
      * replace (z - 1 + 1)%Z with z by lia.
        apply trc_refl.
  - subst z. assumption.
Qed.

Lemma trc_eq :
  forall (A : Type) (R : A -> A -> Prop) x y,
    x = y ->
    trc R x y.
Proof.
  intros A R x y H.
  subst.
  apply trc_refl.
Qed.

Lemma robot_horizontal_reachable :
  forall x,
    (x >= 0)%Z ->
    reachable robot_sys (x, 5 - x)%Z.
Proof.
  intros x Hle.
  apply Zlt_lower_bound_ind with (z := 0%Z) (x := x); [|lia].
  clear x Hle.
  intros x IH Hx.
  apply Zle_lt_or_eq in Hx.
  destruct Hx as [Hx|Hx].
  - specialize (IH (x - 1))%Z.
    eapply reachable_transitive.
    + apply IH. lia.
    + eapply trc_front.
      * apply robot_step_southeast.
      * apply trc_eq.
        f_equal; lia.
  - subst x.
    unfold reachable.
    exists (0, 5)%Z.
    simpl.
    split.
    + unfold robot_init. reflexivity.
    + apply trc_refl.
Qed.

Theorem robot_characterize_reachable :
  forall s,
    robot_reach s ->
    reachable robot_sys s.
Proof.
  unfold robot_reach.
  intros [x y] [Hxy Hx].
  apply robot_horizontal_reachable in Hx.
  eapply robot_vertical_reachable.
  - eassumption.
  - lia.
Qed.

Theorem robot_characterize_reachable_iff :
  forall s,
    reachable robot_sys s <-> robot_reach s.
Proof.
  intros s.
  split.
  - intros Hreach.
    eapply by_invariant; eauto.
    apply robot_reach_invariant.
  - apply robot_characterize_reachable.
Qed.

End TrSys.