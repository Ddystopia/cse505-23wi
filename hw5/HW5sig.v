Require HW5.

Require Import Arith Lia List String.
Import ListNotations.
Open Scope string.

Set Implicit Arguments.

(*
 * This "Module Type" contains the type of everything we expect you to define or
 * prove in this homework.
 *)
Module Type HW5sig.

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

Record trsys state :=
  { Init : state -> Prop
  ; Step : state -> state -> Prop }.

Definition is_invariant {state} (sys : trsys state) (P : state -> Prop) :=
  forall s0,
    sys.(Init) s0 ->
    forall sN,
      trc sys.(Step) s0 sN ->
      P sN.

Module UTLC.

(* Copied stuff from Week06.v *)
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

Fixpoint is_free_var (e : expr) (y : var) : Prop :=
  match e with
  | Var x => x = y
  | Abs x e => x <> y /\ is_free_var e y
  | App e1 e2 => is_free_var e1 y \/ is_free_var e2 y
  end.

Definition closed (e : expr) : Prop :=
  forall x,
    ~ is_free_var e x.

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

Fixpoint numeral_body (n : nat) : expr :=
  match n with
  | O => "z"
  | S m => "s" @ ((\"s", \"z", numeral_body m) @ "s" @ "z")
  end.

Definition numeral (n : nat) : expr :=
  \"s", \"z", numeral_body n.

Parameter or_T_left_T :
  forall e1 e2 v2,
    e1 -->* T ->
    e2 -->* v2 ->
    value v2 ->
    or e1 e2 -->* T.

Parameter or_T_right_wrong_answer :
  exists e1 v1 e2,
    e1 -->* v1 /\
    value v1 /\
    e2 -->* T /\
    or e1 e2 -->* F.

Parameter or_T_right_fixed :
  forall e1 e2 b,
    e1 -->* church_bool b ->
    e2 -->* T ->
    or e1 e2 -->* T.

Parameter free_vars_subst_1 :
  forall from to e x,
    is_free_var (subst from to e) x ->
    (is_free_var e x /\ x <> from) \/ (is_free_var to x /\ is_free_var e from).

Parameter free_vars_subst_2_nope :
  exists from to e x,
    ((is_free_var e x /\ x <> from) \/
     (is_free_var to x /\ is_free_var e from)) /\
    ~ is_free_var (subst from to e) x.

Parameter subst_closed :
  forall from to e,
    closed e ->
    subst from to e = e.

Parameter SumUpto : expr.

Definition Two := Succ @ One.
Definition Three := Succ @ Two.
Definition Four := Succ @ Three.
Definition Five := Succ @ Four.

Parameter SumUpto5 :
  SumUpto @ Five -->* numeral 15.

Fixpoint is_bound_var (e : expr) (y : var) : Prop :=
  match e with
  | Var x => False
  | \x, e => x = y \/ is_bound_var e y
  | e1 @ e2 => is_bound_var e1 y \/ is_bound_var e2 y
  end.

Parameter can_be_both_bound_and_free :
  exists e x,
    is_free_var e x /\ is_bound_var e x.

Definition safe_to_subst (e to : expr) : Prop :=
  forall y,
    ~ (is_free_var to y /\ is_bound_var e y).

Parameter free_vars_subst_no_capture :
  forall e to,
    safe_to_subst e to ->
    forall from x,
        is_free_var (subst from to e) x
      <->
        (is_free_var e x /\ x <> from) \/
        (is_free_var to x /\ is_free_var e from).

Parameter safe_to_subst_not_inductive :
  exists e1 e2 e3 e4,
    e1 @ e2 --> e3 @ e4 /\
    safe_to_subst e1 e2 /\
    ~ safe_to_subst e3 e4.
End UTLC.

Module STLC.

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

Fixpoint is_free_var (e : expr) (y : var) : Prop :=
  match e with
  | T | F => False
  | Var x => x = y
  | Abs x e => x <> y /\ is_free_var e y
  | App e1 e2 => is_free_var e1 y \/ is_free_var e2 y
  | If c Then e1 Else e2 =>
    is_free_var c y \/ is_free_var e1 y \/ is_free_var e2 y
  end.

Definition expr_init (e : expr) (e' : expr) :=
  e' = e.

Definition expr_to_trsys (e : expr) := {|
  Init := expr_init e;
  Step := step
|}.

Definition closed_expr_of_type (t : type) : expr -> Prop :=
  fun e =>
    [] |- e : t.

Parameter program_with_stlc :
  exists G t,
    G |- t : ((Bool ==> Bool) ==> (Bool ==> Bool ==> Bool)).

Definition closed (e : expr) : Prop :=
  forall x,
    ~ is_free_var e x.

Parameter well_typed_empty_closed :
  forall e t,
    [] |- e : t ->
    closed e.

Parameter context_extentionality :
  forall G1 G2 e t,
    (forall x,
      is_free_var e x ->
      lookup x G1 = lookup x G2) ->
    G1 |- e : t ->
    G2 |- e : t.

Parameter weakening_empty_again :
  forall G e t,
    [] |- e : t ->
    G |- e : t.

Parameter strengthening_again :
  forall G x t1 t2 e t,
    (G ++ [(x, t2)])%list |- e : t ->
    lookup x G = Some t1 ->
    G |- e : t.

Parameter ill_typed_but_safe :
  exists e,
    (forall G t, ~ (G |- e : t)) /\
    e -->* T.

Definition terminates (e : expr) :=
  exists v,
    e -->* v /\
    value v.

Parameter termination_ite :
  forall c e1 e2 t,
    [] |- c : Bool ->
    [] |- e1 : t ->
    [] |- e2 : t ->
    terminates c ->
    terminates e1 ->
    terminates e2 ->
    terminates (If c Then e1 Else e2).

Parameter termination_app :
  forall e1 e2 tA tB,
    [] |- e1 : tA ==> tB ->
    [] |- e2 : tA ->
    terminates e1 ->
    terminates e2 ->
    terminates (e1 @ e2).

Parameter termination_attempt :
  forall e t,
    [] |- e : t ->
    terminates e.
End STLC.

Module STLC_pairs.
(* Not possible to give useful signatures here due to Inductive/Parameter bug *)
End STLC_pairs.

End HW5sig.

(* Check that HW5 has the above signature. *)
Module M <: HW5sig := HW5.
