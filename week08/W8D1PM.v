Require Import Arith Lia List String.
Require Import ListSet.
Import ListNotations.

Set Implicit Arguments.
Set Nested Proofs Allowed.

(*

        _____                                _   _     _                 
       |_   _|  _ __    __ _   _ __    ___  (_) | |_  (_)   ___    _ __  
         | |   | '__|  / _` | | '_ \  / __| | | | __| | |  / _ \  | '_ \ 
         | |   | |    | (_| | | | | | \__ \ | | | |_  | | | (_) | | | | |
         |_|   |_|     \__,_| |_| |_| |___/ |_|  \__| |_|  \___/  |_| |_|
                                                                         
               ____                  _                            
              / ___|   _   _   ___  | |_    ___   _ __ ___    ___ 
              \___ \  | | | | / __| | __|  / _ \ | '_ ` _ \  / __|
               ___) | | |_| | \__ \ | |_  |  __/ | | | | | | \__ \
              |____/   \__, | |___/  \__|  \___| |_| |_| |_| |___/
                       |___/                                      

*)

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


(*
          _____          _                        _   _                 
         | ____| __  __ | |_    ___   _ __     __| | (_)  _ __     __ _ 
         |  _|   \ \/ / | __|  / _ \ | '_ \   / _` | | | | '_ \   / _` |
         | |___   >  <  | |_  |  __/ | | | | | (_| | | | | | | | | (_| |
         |_____| /_/\_\  \__|  \___| |_| |_|  \__,_| |_| |_| |_|  \__, |
                                                                  |___/ 
                _                           _           _         
               | |       __ _   _ __ ___   | |__     __| |   __ _ 
               | |      / _` | | '_ ` _ \  | '_ \   / _` |  / _` |
               | |___  | (_| | | | | | | | | |_) | | (_| | | (_| |
               |_____|  \__,_| |_| |_| |_| |_.__/   \__,_|  \__,_|
                                                                  
                ____           _                  _               
               / ___|   __ _  | |   ___   _   _  | |  _   _   ___ 
              | |      / _` | | |  / __| | | | | | | | | | | / __|
              | |___  | (_| | | | | (__  | |_| | | | | |_| | \__ \
               \____|  \__,_| |_|  \___|  \__,_| |_|  \__,_| |___/

*)

(* variable names + our regular decidable equality stuff *)

Definition eq_dec (A : Type) :=
  forall (x : A),
    forall (y : A),
      {x = y} + {x <> y}.

Notation var := string.
Definition var_eq : eq_dec var := string_dec.

(* To make the type system interesting, we'll extend our lambda calculus (LC)
   to include boolean literals "T" (true) and "F" (false) as well as an
   'if then else' expression form "Ite". *)
Inductive expr : Type :=
| T   : expr (* << NEW! *)
| F   : expr (* << NEW! *)
| Var : var -> expr
| Ite : expr -> expr -> expr -> expr (* << NEW! *)
| Abs : var -> expr -> expr
| App : expr -> expr -> expr.

(* Some notation like last week to make it easier to write programs in our LC. *)
Declare Scope stlc_scope.
Coercion Var : var >-> expr.
Notation "'\' x ',' y" := (Abs x y) (left associativity, at level 75).
Notation "'If' c 'Then' e1 'Else' e2" := (Ite c e1 e2) (no associativity, at level 69).
Infix "@" := App (left associativity, at level 68).
Delimit Scope stlc_scope with expr.
Bind Scope stlc_scope with expr.

(* Since we extended our LC, we also need to extend the substitution function.
   In the slides, we wrote this as "e[from ↦ to]".
   The new cases are all fairly straightforward: there's no substitution to do
   for the boolean constants "T" and "F" and the 'if then else' "Ite" case
   just recurses on the (1) condition, (2) then, and (3) else branches. *)
Fixpoint subst (from : var) (to : expr) (e : expr) : expr :=
  match e with
  | T => T (* << NEW : nothing to do for the constant "T" (true)  *)
  | F => F (* << NEW : nothing to do for the constant "F" (false) *)
  | Var x => if var_eq from x then to else e
  | Abs x e1 => Abs x (if var_eq from x then e1 else subst from to e1)
  | App e1 e2 => App (subst from to e1) (subst from to e2)
  | If c Then e1 Else e2 =>
      (* NEW: just recurse on all the parts! *)
      If (subst from to c)    (* << (1) substitute in the condition   *)
      Then (subst from to e1) (* << (2) substitute in the then branch *)
      Else (subst from to e2) (* << (3) substitute in the else branch *)
  end.

(* There also more kinds of expressions that are 'done evaluating', in
   particular, the boolean constants "T" (true) and "F" (false). *)
Inductive value : expr -> Prop :=
| value_abs : forall x e, value (\x, e)
| value_T   : value T
| value_F   : value F.
Local Hint Constructors value : core.

(* Having extended the syntax and substitution function, we're now
   ready to give a small step operational semantics for our extended LC.
   This boils down to just adding 3 new rules for how to evaluate an
   'if then else' ("Ite"). *)
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
(* NEW: An "if" can step if its condition can step. *)
| step_ite_cond :
  forall c c' e1 e2,
    step c c' ->
    step (If c Then e1 Else e2) (If c' Then e1 Else e2)
(* NEW: An "if" can step if its condition is "T" (true),
        just take the 'then' branch! *)
| step_true :
  forall e1 e2,
    step (If T Then e1 Else e2) e1
(* NEW: An "if" can step if its condition is "F" (false),
        just take the 'else' branch! *)
| step_false :
  forall e1 e2,
    step (If F Then e1 Else e2) e2.
Local Hint Constructors step : core.

(* Some notation to help connect our LC with transition system view. *)
Notation "e '-->' e'" := (step e e') (at level 75).
Notation "e '-->*' e'" := (trc step e e') (at level 75).

(* An initial state in an LC trsys is just the initial expression. 
   (there's no 'memory' so we don't need valuations, etc.) *)
Definition expr_init (e : expr) (e' : expr) :=
  e' = e.

Definition expr_to_trsys (e : expr) := {|
  Init := expr_init e;
  Step := step
|}.


(*

                          ____    _____   _        ____ 
                         / ___|  |_   _| | |      / ___|
                         \___ \    | |   | |     | |    
                          ___) |   | |   | |___  | |___ 
                         |____/    |_|   |_____|  \____|

*)


(* In Simply Typed Lambda Calculus (STLC) we have a simple language of types.
   In particular, a type can either be "Bool" or "Fun t1 t2" which is the type
   of a function from some type "t1" to another type "t2". *)
Inductive type :=
| Bool
| Fun : type -> type -> type.

(* Some notation to make it easier to write function types. *)
Notation "t1 ==> t2" := (Fun t1 t2) (at level 68, left associativity).

(* In our type system, we want to track mapping from variables to their type.
   In the slides we called this "Gamma" (𝚪), but here we'll just call it "ctx".  *)
Notation ctx := (list (var * type)).

(* We'll also need to be able to look up what variable a type is bound to
   within a given typing context: *)
Fixpoint lookup (x : var) (gamma : ctx) : option type :=
  match gamma with
  | [] => None
  | (y, n) :: gamma' =>
    if var_eq x y
    then Some n
    else lookup x gamma'
  end.

(* Some notation to help our Coq code match what we used in slides.
  "G |- e : t" means 'In context "G", we can show "e" has type "t". *)
Reserved Notation "G |- e : t" (at level 76, e at next level, no associativity).

(* The typing rules for our STLC.
   The goal is that these should allow a user to easily prove
   that their program will never 'get stuck', e.g., by trying 
   to branch on a function in an "Ite" or by trying to call
   a boolean as if it were a function in an "App". *)
Inductive hasty : ctx -> expr -> type -> Prop :=
| HtTrue :
    forall G, G |- T : Bool
| HtFalse :
    forall G, G |- F : Bool
| HtVar :
    forall G x t,
     lookup x G = Some t ->
     G |- x : t
| HtIte :
    forall G c e1 e2 t,
      (G |- c : Bool) ->
      (G |- e1 : t) ->
      (G |- e2 : t) ->
      (G |- If c Then e1 Else e2 : t)
| HtApp :
    forall G e1 e2 t1 t2,
      (G |- e1 : (t1 ==> t2)) ->
      (G |- e2 : t1) ->
      (G |- e1 @ e2 : t2)
| HtAbs :
    forall G x e t1 t2,
      ((x, t1) :: G |- e : t2) ->
      (G |- \x, e : (t1 ==> t2))
where "G |- e : t" := (hasty G e t).
Local Hint Constructors hasty : core.

(*
               ____                           _                 
               |  _ \   _ __    ___   __   __ (_)  _ __     __ _ 
               | |_) | | '__|  / _ \  \ \ / / | | | '_ \   / _` |
               |  __/  | |    | (_) |  \ V /  | | | | | | | (_| |
               |_|     |_|     \___/    \_/   |_| |_| |_|  \__, |
                                                           |___/ 
                          _____                        
                         |_   _|  _   _   _ __     ___ 
                           | |   | | | | | '_ \   / _ \
                           | |   | |_| | | |_) | |  __/
                           |_|    \__, | | .__/   \___|
                                  |___/  |_|           
        ____                                _                            
       / ___|    ___    _   _   _ __     __| |  _ __     ___   ___   ___ 
       \___ \   / _ \  | | | | | '_ \   / _` | | '_ \   / _ \ / __| / __|
        ___) | | (_) | | |_| | | | | | | (_| | | | | | |  __/ \__ \ \__ \
       |____/   \___/   \__,_| |_| |_|  \__,_| |_| |_|  \___| |___/ |___/
                                                                         
*)


(* As last week, we'll only be proving safety for "closed" terms,
   i.e., no terms with "free variables". *)
Fixpoint is_free_var (e : expr) (y : var) : Prop :=
  match e with
  | T | F => False
  | Var x => x = y
  | Abs x e => x <> y /\ is_free_var e y
  | App e1 e2 => is_free_var e1 y \/ is_free_var e2 y
  | If c Then e1 Else e2 => is_free_var c y \/ is_free_var e1 y \/ is_free_var e2 y
  end.

Definition closed (e : expr) : Prop :=
  forall x,
    ~ is_free_var e x.

(* Our goal is to prove that well-typed terms never get stuck! *)
Definition unstuck e :=
  value e \/ exists e', e --> e'.

(* As we saw in the slides, proving that well-typed terms never
   get stuck boils down to proving the key "Progress Lemma"
   (which we'll use to strengthen our induction) and
   the key "Preservation Lemma" which shows that types are
   preserved throughout execution. *)

(* First, let's prove the "Progress Lemma": *)
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
Qed.
(* Wow! That was even easier than on the slides! *)

(* Moving on to preservation, we have some more work to do... *)

(* We'll need a handful of lemmas about how things can still
   typecheck even under different contexts. *)

(* First up, we'll want to be able to 'split' the context
   and show that looking up a variable's type 'follows the split'. *)
Lemma lookup_app :
  forall x G1 G2,
    lookup x (G1 ++ G2) =
    match lookup x G1 with
    | Some t => Some t
    | None => lookup x G2
    end.
Proof.
  induction G1; simpl; intros; auto.
  destruct a, var_eq; auto.
Qed.

(* If we can typecheck a term without some variable "x" in the
   context, then we can still type check it if we add a binding
   for "x" in the context... *)
Lemma weakening_middle :
  forall G1 G2 G3 e t,
    (forall x t1,
      lookup x G3 = Some t1 ->
      lookup x G2 = None) ->
    G1 ++ G3 |- e : t ->
    G1 ++ G2 ++ G3 |- e : t.
Proof.
  intros G1 G2 G3 e t Disjoint He.
  remember (G1 ++ G3) as G.
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
    G1 ++ G2 |- e : t.
Proof.
  intros G1 G2 e t Disjoint He.
  revert G1 Disjoint.
  induction He; intros; eauto.
  - econstructor.
    rewrite lookup_app.
    erewrite Disjoint; eauto.
  - econstructor.
    (* also not provable!!! *)
  Restart.
  intros G1 G2 e t Disjoint He.
  apply weakening_middle with (G1 := []); auto.
Qed.

(* If we can typecheck a term in the empty context,
   then we can typecheck it in any context! *)
Lemma weakening_empty :
  forall G e t,
    [] |- e : t ->
    G |- e : t.
Proof.
  intros G e.
  induction e; intros t He; invc He; eauto.
  - simpl in *. discriminate.
  - (* Not provable by induction! *)
  Restart.
  intros G e t He.
  apply weakening_append with (G1 := G) in He.
  - rewrite app_nil_r in He. auto.
  - simpl. discriminate.
Qed.

(* Conversely, we can also *drop* variable bindings
   that are shadowed in the context by more recent bindings. *)
Lemma strengthening :
  forall G x t1 t2 e t,
    G ++ [(x, t2)] |- e : t ->
    lookup x G = Some t1 ->
    G |- e : t.
Proof.
  intros G x t1 t2 e t He HG.
  remember (G ++ [(x, t2)]) as G'.
  revert G t1 HeqG' HG.
  induction He; intros; subst; eauto.
  - rewrite lookup_app in H.
    destruct (lookup x0 G0) eqn:?.
    + invc H. auto.
    + simpl in *. destruct var_eq; congruence.
  - constructor.
    apply IHHe with (t3 := if var_eq x x0 then t1 else t3); auto.
    simpl.
    destruct var_eq; auto.
Qed.

(* Now the key "Substitution Lemma": if the context
   binds "x" to type "t1" (and is the only binding
   for "x" in that context) and expression "e" type
   checks under that assumption to have type "t",
   then if we substitute a value of type "t" in for
   "x" everywhere in "e", then the result of substitution
   will still have the type "t". *)
Lemma substitution :
  forall (G : ctx) e t x t1 v,
    G ++ [(x, t1)] |- e : t ->
    lookup x G = None ->
    [] |- v : t1 ->
    G |- subst x v e : t.
Proof.
  intros G e t x t1 v He Hlook Hv.
  remember (G ++ [(x, t1)]) as G'.
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
    [] |- v : t1 ->
    [] |- subst x v e : t.
Proof.
  intros x t1 e t v He Hv.
  remember [(x, t1)] as G.
  revert x t1 v Hv HeqG.
  induction He; simpl; intros; subst; eauto.
  - simpl in *. repeat destruct var_eq; try congruence; auto.
    (* so far so good... *)
  - (* IH is useless because our lemma is about contexts of size 1 *)
  Restart.
  intros x t1 e.
  revert x t1.
  induction e; simpl; intros x t1 t v He Hv; invc He; eauto.
  - simpl in *. repeat destruct var_eq; try congruence; auto.
  - (* IH is useless because our lemma is about contexts of size 1 *)
  Restart.
  (* Need to strengthen the induction hypothesis to an *arbitrary* context *)
  eauto using substitution.
Qed.

(* Once we have the substituion lemma, proving the key
   "Presevation Lemma" is mostly just 'eauto' 😂. *)
Lemma preservation :
  forall e e' t,
    [] |- e : t ->
    e --> e' ->
    [] |- e' : t.
Proof.
  intros e e' t HT Step.
  revert t HT.
  induction Step; intros t HT; invc HT; eauto.
  idtac.
  (* only the case for step_beta remains *)
  invc H3.
  idtac.
  eauto using substitution_one.
Qed.

(*
  Finally, we just need to use our generic transition reasoning
  reasoning rules (`invariant_implies` and `invariant_induction`)
  to stitch all the pieces together!
*)

Definition closed_expr_of_type (t : type) : expr -> Prop :=
  fun e =>
    [] |- e : t.

Lemma preservation_star :
  forall e t,
    [] |- e : t ->
    is_invariant (expr_to_trsys e) (closed_expr_of_type t).
Proof.
  invariant_induction_boilerplate.
  assumption.
  eauto using preservation.
Qed.

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

(* 😎 *)

(* STLC Type Safety ASCII Proof

Syntax

e ::= T | F | (\x. e) | e e | if e then e else e | x

Substitution
        x [x |-> e] = e
        x [y |-> e] = x (x != y)
  (\x. e) [x |-> e] = (\x. e)
  (\x. e) [y |-> e] = (\x. e[y |-> e]) (x != y)
  (e1 e2) [x |-> e] = (e1 [x |-> e]) (e2 [x |-> e])
        T [x |-> e] = T
        F [x |-> e] = F
    (if e1 then e2 else e3) [x |-> e] = 
    if (e1 [x |-> e]) then (e2 [x |-> e]) else (e3 [x |-> e])

Operational Semantics

       e1 --> e1'
  -------------------- StepAppL
    e1 e2 --> e1' e2

       e2 --> e2'
  -------------------- StepAppR
     v e2 --> v e2'

  ------------------------------- StepBeta
   (\x. e1) v2 --> e1 [x |-> v2]

                    e1 --> e1'
  ------------------------------------------------ StepIfL
  if e1 then e2 else e3 --> if e1' then e2 else e3

  ---------------------------- StepIfTrue
  if T then e2 else e3 --> e2

  ---------------------------- StepIfFalse
  if F then e2 else e3 --> e3

Type System

  ---------------------- HTTrue
       G |- T : bool
  
  ---------------------- HTFalse
       G |- F : bool
  
         G(x) = t
  ---------------------- HTVar
       G |- x : t

    G |- e1 : bool    G |- e2 : t   G |- e3 : t
  ---------------------------------------------- HTIf
          G |- if e1 then e2 else e3 : t
    
        G |- e1 : t1 -> t2    G |- e2 : t1
  ---------------------------------------------- HTApp
                G |- e1 e2 : t2
  
     G, x:t1 |- e : t2
  ------------------------ HTAbs
  G |- (\x. e) : t1 -> t2

  Definition (Value):
    T, F, and (\x. e) are values for all x and e.  

  Definition (Unstuck):
    An expression e is unstuck if e is a value
    or e can step to another expression e' by the rules of Operational Semantics

  Lemma (Progress):
    If . |- e : t, then e is unstuck
  Proof.
    By induction on the derivation of . |- e : t.
    - Base Cases
      + Case ----------------------
                . |- T : bool
        If e is T, then e is a value. e is unstuck by definition.

      + Case ----------------------
                . |- F : bool
        Similar argument as the previous case.

      + Case       G(x) = t
              -------------------
                  G |- x : t
            This case is impossible because G is empty, there is no way to
            get t by looking up x in G.
  
    - Inductive Case
      + Case    G |- e1 : bool    G |- e2 : t   G |- e3 : t
              ----------------------------------------------
                    G |- if e1 then e2 else e3 : t
            By the induction hypothesis, because . |- e1 : bool, e1 is unstuck.
            Therefore, e1 is either some value or can step to e1'. By case analysis
            this:
            Subcase 1.
                e1 is a value. By definition of value, e1 is T, F or (\x. e)
                Since we know that . |- e1 : bool, e1 cannot be an abstraction, so e1
                can only be T or F. In both case, according to StepIfTrue and StepIfFalse,
                `if e1 then e2 else e3` can take a step, and thus it is unstuck.
            
            Subcase 2.
                e1 can step to e1', then by StepIfL, `if e1 then e2 else e3` can also take a
                step hence unstuck.
      
      + Case         G |- e1 : t1 -> t2    G |- e2 : t1
              ----------------------------------------------
                            G |- e1 e2 : t2

            By the induction hypothesis, we know e1 is unstuck and e2 is unstuck,
            so e1 and e2 are value or can step to e1' and e2' respectively. By case analysis

            Subcase 1.
              e1 is a value and e2 is a value. By definition of value, e1 is T, F or (\x. e)
              Since . |- e1 : t1 -> t2, e1 cannot be T or F. Thus e1 can only be (\x. e).
              Since e2 also is a value, by StepBeta rule, `e1 e2` can take a step and thus it is unstuck.

            Subcase 2.
              e1 is a value and e2 steps to e2'. Then by StepAppR, it is unstuck.
            
            Subcase 3.
              e1 steps to e1' and e2 is a value. Then by StepAppL, it is unstuck.
            
            Subcase 4.
              e1 steps to e1' and e2 steps to e2'. Similar as Subcase 3.
      
    + Case        G, x:t1 |- e : t2
              ------------------------
               G |- (\x. e) : t1 -> t2
            \x. e is a value by definition, so it is unstuck.
Qed.

Lemma (Gamma Lookup App)
  If G1, G2 |- x : t, then either G1 |- x : t or G2 |- x : t.
Proof.
  By induction on G1.
  Base Case. G1 is [], then ([], G2) (x) = G2 (x) = t. Therefore G2 |- x : t.
  Induction Hypothesis.
    Suppose the lemma holds for some arbitrary G1' and G2, that is, if G1', G2 |- x : t,
    then either G1' |- x : t or G2 |- x : t.
  Inductive Step.
    We are to show that if ((x0 : t0), G1'), G2 |- x : t then either (x0 : t0), G1' |- x : t
    or G2 |- x : t.
    By case analysis on whether x = x0
    - Case 1. x = x0. then (x0 : t0), G1' |- x : t0 and t0 = t in this case.
      Thus (x0 : t0), G1 |- x : t0 holds.
    - Case 2. x != x0. Then G1', G2 |- x : t,
      and thus this case holds by induction hypothesis.
Qed.

Lemma (Gamma Weakening)
  If . | e : t, then G |- e : t.
Proof Sketch. Generalize to an arbitrary Gamma, and then induction on e. Qed.

Lemma (Gamma Strenthening)
  If G, (x : t1) |- e : t, G |- x : t1, then G |- e : t.
Proof.
  By induction on derivation of G, (x : t1) |- e : t.
  Detail left for readers.
Qed,

Lemma (Substitution)
  If G, x:t1 |- e : t where x is not in G and . |- v : t1
  then G |- subst x v e : t.
Proof.
  By induction on the derivation of G, x:t1 |- e : t
  Base Cases
    + Case   ----------------------
                  G |- T : bool
            By definition, subst x v T is T. By definition, G |- T : bool
  
    + Case   ----------------------
                  G |- F : bool
            Similar as the previous case

    + Case        G(x1) = t
            ----------------------
                 G |- x1 : t
            We know that G, x:t1 |- x1 : t.  By the Gamma Lookup App lemma,
            either G |- x1 :t or (x : t1) |- x1 : t.
            We case analysis on this result,
            
            Subcase 1. G |- x1 : t.
              Since x is not in G, x1 != x. By definition of subst, x1 [x |-> v] = x1, so
              G |- subst x v x1 : t = G |- x1 : t, and it holds by assumption.
            
            Subcase 2. (x : t1) |- x1 : t
                Then in this case x1 = x and t = t1, so x1 [x |-> v] = v.
                Since . |- v : t1, by Gamma Weakening lemma, G |- v : t1.
                 
  Inductive Case
    + Case      G |- e1 : bool    G |- e2 : t   G |- e3 : t
              ----------------------------------------------
                      G |- if e1 then e2 else e3 : t
            According to induction hypotheses,
            G |- subst x v e1 : bool
            G |- subst x v e2 : t
            G |- subst x v e3 : t
            and thus G |- If (subst x v e1) then (subst x v e2) else (subst x v e3) : t holds by HTIf
    
    + Case         G |- e1 : t1 -> t2    G |- e2 : t1
             ----------------------------------------------
                           G |- e1 e2 : t2
            Similar as the previous case.
    
    + Case     G, x0:t1' |- e : t2
             ------------------------
             G |- (\x0. e) : t1' -> t2
            We are to show that G |- subst x v (\x0. e) : t1' -> t2.
            We case analysis on the result of subst.
            Subcase 1. (\x0. e) [x |-> v] = (\x0. e)
              In this case, x0 = x, therefore, our goal becomes
              G |- (\x0. e) : t1' -> t2. It is suffcient to show that
              G, (x0 : t1') |- e : t2. Our assumption says that
              G, (x0, t1'), (x0, t1) |- e : t2. By Gamma Strenthening Lemma, 
              G, (x0, t1') |- e : t2.
            
            Subcase 2. (\x0. e) [x |-> v] = (\x0. e [x |-> v])
              In this case x0 != x, therefore our goal is
              G |- (\x0. e [x |-> v]) : t1' -> t2. It is sufficient to show that
              G, (x0, t1') |- e [x |-> v] : t2. This holds by induction hypothesis.
Qed.

Lemma (Preservation)
  If . |- e : t, e --> e', then . |- e' : t.
Proof.
  By induction on derivation of e --> e'
  Base Case.
    Case   -------------------------------
            (\x. e1) v2 --> e1 [x |-> v2]
        In this case . |- (\x. e1) v2 : t, so by definition
        (*)  . |- v2 : t1
        (**) . |- (\x. e1) : t1 -> t
        By (**), (x : t1) |- e1 : t2, and we are to show that 
        . |- subst x v e : t
        This follows the substitution lemma proved above with (G = .)
    
    Case  ----------------------------
           if T then e2 else e3 --> e2
          . |- if T then e2 else e3 : t follows . |- e2 : t.
    
    Case  ----------------------------
           if F then e2 else e3 --> e3
           . |- if F then e2 else e3 : t follows . |- e3 : t.

  Inductive Step.
    Case      e1 --> e1'
          --------------------
            e1 e2 --> e1' e2
          
          Since . |- e1 e2 : t, and by HTApp,
          . |- e1 : t1 -> t
          . |- e2 : t1
          By induction hypothesis, . |- e1' : t1 -> t, then by HTApp,
          . |- e1' e2 : t
    
    Case      e2 --> e2'
          --------------------
             v e2 --> v e2'
          Similar as previous case.
    
    Case                  e1 --> e1'
        ------------------------------------------------
         if e1 then e2 else e3 --> if e1' then e2 else e3
        
        From . |- if e1 then e2 else e3 : t, we know that
        . |- e1 : bool
        . |- e2 : t
        . |- e3 : t
        By induction hypothesis, we know that . |- e1' : bool
        therefore by HtIf
        . |- if e1' then e2 else e3 : t
Qed.
*)