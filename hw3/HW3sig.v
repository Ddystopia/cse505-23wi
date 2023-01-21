Require HW3.

Require Import Arith Lia List String.
Import ListNotations.
Open Scope string.

Set Implicit Arguments.

(*
 * This "Module Type" contains the type of everything we expect you to define or
 * prove in this homework.
 *)
Module Type HW3sig.
  Module AST.
    Inductive optree : Set :=
    | Const (n : nat)
    | Plus (e1 e2 : optree)
    | Times (e1 e2 : optree).
  
  Fixpoint kinda_sum (e : optree) : nat :=
    match e with
    | Const n => n
    | Plus e1 e2 => kinda_sum e1 + kinda_sum e2
    | Times e1 e2 => kinda_sum e1 * kinda_sum e2
  end.

  Fixpoint commuter (e : optree) : optree :=
    match e with
    | Const n => e
    | Plus e1 e2 => Plus (commuter e2) (commuter e1)
    | Times e1 e2 => Times (commuter e2) (commuter e1)
  end.

  Parameter kinda_sum_commuter :
    forall e, kinda_sum e = kinda_sum (commuter e).
  
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

  Parameter kinda_sum_constant_fold :
    forall e, kinda_sum (constant_fold e) = kinda_sum e.
    
  End AST.

  Module Interpreters.
    Parameter sum_upto : nat -> nat.

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

    Definition sum_n : cmd :=
    "output" <- 0;
    repeat "input" doing
      "output" <- "output" + "input";
      "input" <- "input" - 1
    done.

    Parameter sum_n_ok :
      forall v input,
        lookup "input" v = Some input ->
        lookup "output" (eval_cmd sum_n v) = Some (sum_upto input).
  End Interpreters.

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

  Parameter trc_back :
    forall {A} (R : A -> A -> Prop) x y,
      trc R x y ->
      forall z,
        R y z ->
        trc R x z.

  Definition counter2_state : Type := nat.

  Definition counter2_init (s : counter2_state) : Prop :=
    s = 0.

  Definition counter2_step (s1 s2 : counter2_state) : Prop :=
    s2 = S (S s1).

  Definition counter2_sys : trsys counter2_state := {|
    Init := counter2_init;
    Step := counter2_step
  |}.

  Definition counter2_safe (s : counter2_state) : Prop :=
    s <> 3.

  Parameter counter2_safe_invariant :
    is_invariant counter2_sys counter2_safe.

  Parameter counter2_ge :
    forall s0 sN,
      trc counter2_sys.(Step) s0 sN ->
      sN >= s0.

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

  Definition rotater_a_ne_b (s : rotater_state) : Prop :=
    let '(a, b, c) := s in
    a <> b.

  Parameter rotater_a_ne_b_invariant :
    is_invariant rotater_sys rotater_a_ne_b.

  Definition rotater_a_in_range (s : rotater_state) : Prop :=
    let '(a, b, c) := s in
    0 <= a <= 2.

  Parameter rotater_a_in_range_invariant :
    is_invariant rotater_sys rotater_a_in_range.

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

  Definition sum : cmd :=
    "output" <- 0;;
    while "input" loop
      "output" <- "output" + "input";;
      "input" <- "input" - 1
    done.

  Parameter sum_3 :
    forall v1,
      lookup "input" v1 = Some 3 ->
      exists v2,
        trc step (v1, sum) (v2, Skip) /\
        lookup "output" v2 = Some 6.

  Parameter sum_state : Type.

  Parameter sum_init: nat -> sum_state -> Prop.

  Parameter sum_safe : nat -> sum_state -> Prop.

  Parameter sum_inv : nat -> sum_state -> Prop.
End HW3sig.

(* Check that HW3 has the above signature. *)
Module M <: HW3sig := HW3.
