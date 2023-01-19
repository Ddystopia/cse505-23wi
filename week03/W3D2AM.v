Require Import Arith Lia List String.
Import ListNotations.
Open Scope string.

Set Implicit Arguments.


Print le.
(*

Inductive le (n : nat) : nat -> Prop :=
	| le_n : n <= n 
  | le_S : forall m : nat, n <= m -> n <= S m.

a <= b

how many constructors does that proof have?

b - a applications of le_S followed by one le_n

*)

Lemma le_O_n : forall n, le O n.
Proof.
  intros.
  destruct n.
  - apply le_n.
  - apply le_S.
  Restart.
  intros. 
  induction n.
  - apply le_n.
  - apply le_S.
    apply IHn.
Qed.

Lemma le_transitive : 
  forall x y z,
    le x y ->
    le y z ->
    le x z.
Proof.
  (* options to induct on: x,y,z and the two le hyps *)
  intros x.
  induction x.
  - intros y z Hxy Hyz.
    apply le_O_n.

  - intros y z Hxy Hyz.
    
    inversion Hxy.
    + subst. apply Hyz.
    + subst. inversion Hyz.
      * subst. auto.
      * subst. 

  Restart.

  intros x y z Hxy Hyz.
  induction Hyz.
  - auto.
  - apply le_S. apply IHHyz.
 
    
Qed.

Definition eq_dec (A : Type) :=
  forall (x : A),
    forall (y : A),
      {x = y} + {x <> y}.

Module Interpreters.

Notation var := string.
Definition var_eq : eq_dec var := string_dec.

(* abstract syntax *)
Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

Lemma syntax_is_not_semantics :
  Plus (Const 1) (Const 1) <> Const 2.
Proof.
  unfold not.
  intro.
  (* destruct H. *)
  inversion H.
Qed.

Print eq.

(* syntactic analysis *)
Fixpoint has_zero (e : arith) : bool :=
  match e with
  | Const n => Nat.eqb n 0
  | Var x => false
  | Plus e1 e2  => has_zero e1 || has_zero e2
  | Minus e1 e2 => has_zero e1 || has_zero e2
  | Times e1 e2 => has_zero e1 || has_zero e2
  end.

Compute has_zero (Const 0). (* true *)
Compute has_zero (Const 1). (* false *)
Compute has_zero (Plus (Var "x") (Var "y")). (* false *)
Compute has_zero (Minus (Plus (Var "x") (Var "y")) (Const 0)). (* true *)

(* notation for writing ASTs *)
Declare Scope arith_scope. (* defines a name for our collection of notations *)
Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Infix "+" := Plus : arith_scope.
Infix "-" := Minus : arith_scope.
Infix "*" := Times : arith_scope.
Delimit Scope arith_scope with arith. (* lets us use "%arith" annotations *)
Bind Scope arith_scope with arith.

(* Now let's see those same examples again. *)
Compute has_zero 0. (* true *)
Compute has_zero 1. (* false *)
Compute has_zero ("x" + "y")%arith. (* false *)
Compute has_zero ("x" + "y" - 0)%arith. (* true *)

(* memory *)
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
    | None => 0  (* sorta bogus! *)
    | Some n => n
    end
  | Plus  e1 e2 => eval_arith e1 v + eval_arith e2 v
  | Minus e1 e2 => eval_arith e1 v - eval_arith e2 v
  | Times e1 e2 => eval_arith e1 v * eval_arith e2 v
  end.

Compute eval_arith (1 + 1)%arith [].  (* 2 *)
Compute eval_arith (2)%arith [].      (* also 2 *)

Lemma eval_one_plus_one_is_eval_two :
  forall v,
    eval_arith (1 + 1)%arith v = eval_arith 2 v.
Proof.
Admitted.


(* from expressions to commands *)
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

Compute do_n_times (cons true) 7 [false; false]. (* 7 "true"s followed by 2 "false"s *)

Fixpoint eval_cmd (c : cmd) (v : valuation) : valuation :=
  match c with
  | Skip => v
  | Assign x e => (x, eval_arith e v) :: v
  | Sequence c1 c2 => eval_cmd c2 (eval_cmd c1 v)
  | Repeat e body => do_n_times (eval_cmd body) (eval_arith e v) v
  end.

(* more notation *)
Declare Scope cmd_scope.
Delimit Scope cmd_scope with cmd.
Bind Scope cmd_scope with cmd.
Notation "x <- e" := (Assign x e%arith) (at level 75) : cmd_scope.
Infix ";" := Sequence (at level 76) : cmd_scope.
Notation "'repeat' e 'doing' body 'done'" :=
  (Repeat e%arith body) (at level 75) : cmd_scope.

Fixpoint factorial_tr (n : nat) (acc : nat) : nat :=
  match n with
  | O => acc
  | S m => factorial_tr m (n * acc)
  end.

Definition factorial_tailrec (n : nat) : nat :=
  factorial_tr n 1.

Definition factorial : cmd :=
  "output" <- 1;
  repeat "input" doing
    "output" <- "output" * "input";
    "input" <- "input" - 1
  done.

Definition factorial_loop_body : cmd :=
  "output" <- "output" * "input";
  "input" <- "input" - 1.

Theorem factorial_ok :
  forall v input,
    lookup "input" v = Some input ->
    lookup "output" (eval_cmd factorial v) = Some (factorial_tailrec input).
Proof.
  (* motto... *)
  intros v input Hinput.
  unfold factorial, factorial_tailrec.
  fold factorial_loop_body.
  cbn -[factorial_loop_body].
  (* do_n_times (eval_cmd factorial_loop_body) *)
Abort.

Definition map_equiv m1 m2 := forall v, lookup v m1 = lookup v m2.

Example map_equiv_example :
  forall m,
    map_equiv (("x", 0) :: ("y", 1) :: m) (("y", 1) :: ("x", 0) :: m).
Proof.
  (* example of destructing on a non-variable *)
Admitted.

Ltac solve_map_cases :=
  unfold map_equiv; intros; simpl;
  repeat destruct (var_eq _ _); try congruence.

(* key lemma for factorial *)
Lemma factorial_loop_body_ok :
  forall n acc v,
    lookup "input" v = Some n ->
    lookup "output" v = Some acc ->
    map_equiv
      (do_n_times (eval_cmd factorial_loop_body) n v)
      (("input", 0) :: ("output", factorial_tr n acc) :: v).
Proof.
  (* do_n_times is recursive on n. So is factorial_tr. Let's induct on n. *)
  induction n; intros acc v Hinput Houtput x.
  - simpl. solve_map_cases.
  - cbn [do_n_times factorial_tr].
    unfold map_equiv in *.
    rewrite IHn with (acc := S n * acc); solve_map_cases.
    + rewrite Hinput. f_equal. lia.
    + rewrite Hinput, Houtput. f_equal. lia.
Qed.

Theorem factorial_ok :
  forall v input,
    lookup "input" v = Some input ->
    lookup "output" (eval_cmd factorial v) = Some (factorial_tailrec input).
Proof.
  intros v input Hinput.
  unfold factorial, factorial_tailrec.
  fold factorial_loop_body.
  cbn -[factorial_loop_body].
  rewrite Hinput.
  rewrite factorial_loop_body_ok with (acc := 1); solve_map_cases.
Qed.

End Interpreters.