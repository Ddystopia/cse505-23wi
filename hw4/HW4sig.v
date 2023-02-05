Require HW4.

Require Import Arith Lia List String.
Import ListNotations.
Open Scope string.

Set Implicit Arguments.

(*
 * This "Module Type" contains the type of everything we expect you to define or
 * prove in this homework.
 *)
Module Type HW4sig.
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
Definition cmd_init (v : valuation) (c : cmd) (s : valuation * cmd) : Prop :=
  s = (v, c).

Definition cmd_to_trsys (v : valuation) (c : cmd) : trsys (valuation * cmd) :=
  {| Init := cmd_init v c
   ; Step := step
   |}.
Parameter reconstruct_sequence_execution :
  forall v1 c1 v2 c2 v3,
    trc step (v1, c1) (v2, Skip) ->
    trc step (v2, c2) (v3, Skip) ->
    trc step (v1, Sequence c1 c2) (v3, Skip).
Parameter sequence_assoc :
  forall v c1 c2 c3 v',
    trc step (v, Sequence (Sequence c1 c2) c3) (v', Skip) ->
    trc step (v, Sequence c1 (Sequence c2 c3)) (v', Skip).




(* has_no_whiles is omitted due to the Coq bug where you can't instantiate a
   Parameter with an Inductive :\ *)



Parameter n_not_zero_is_succ :
  forall n,
    n <> 0 ->
    exists m,
      n = S m.

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

Parameter two_counters_correct :
  forall input,
    is_invariant (two_counters_sys input) (two_counters_safe input).



Definition assertion := (valuation -> Prop).
Definition assert_implies (P Q : assertion) : Prop :=
  (forall v, P v -> Q v).
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

Definition sum :=
  "output" <- 0;;
  while "input" loop
    "output" <- "output" + "input";;
    "input" <- "input" - 1
  done.

Fixpoint sum_upto (n : nat) :=
  match n with
  | 0 => 0
  | S m => n + sum_upto m
  end.

Parameter sum_triple :
  forall input,
    hoare_triple
     (fun v => eval_arith "input" v = input)
     sum
     (fun v => eval_arith "output" v = sum_upto input).

Definition doesnt_terminate :=
  "x" <- 5;;
  while 1 loop
    assert (("x" - 4) + (4 - "x"));; (* x <> 4 *)
    "x" <- "x" + 1
                  done.

Parameter doesnt_terminate_ht :
  hoare_triple
    (fun _ => True)
    doesnt_terminate
    (fun v => eval_arith "x" v <> 4).


Module NondeterministicImp.
(* Unfortunately, all these problems depend on hoare_triple, which also trips
   over the Parameter/Inductive bug. *)
End NondeterministicImp.

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

Notation "e '-->' e'" := (step e e') (at level 75).
Notation "e '-->*' e'" := (trc step e e') (at level 75).

(* Here are two lambda calculus programs. *)
Definition T := \"x", \"y", "x".
Definition F := \"x", \"y", "y".
Parameter T_T :
  T @ T @ F -->* T.
Definition Omega :=
  (\"x", "x" @ "x") @
  (\"x", "x" @ "x").

Definition diverges e :=
  forall e',
    e -->* e' ->
    exists e'',
      e' --> e''.
Parameter omega_diverges :
  diverges Omega.
End UTLC.
End HW4sig.

(* Check that HW4 has the above signature. *)
Module M <: HW4sig := HW4.
