(* Comments in Coq go between "(*" and "*)". *)

(* comments (* can (* be (* nested *)*)*)*)


Module Booleans.

Inductive bool : Set :=
| true : bool
| false : bool.

Definition negb (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

Compute negb true.
Compute negb false.

Definition andb (b1 : bool) (b2 : bool) : bool :=
    match b1 with
    | true => b2
    | false => false
    end.

Compute andb true true.
Compute andb true false.
Compute andb false true.
Compute andb false false.

Lemma andb_comm :
  forall b1 b2,
    andb b1 b2 = andb b2 b1.
Proof.
Admitted.

(* currying and function types *)
Check negb.
Check andb.

Definition andb_no_sugar : bool -> bool -> bool :=
  fun b1 =>
    fun b2 =>
      match b1 with
      | true => b2
      | false => false
      end.

Print andb.
Print andb_no_sugar.

End Booleans.


Module Nats.

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Check O.           (* 0 *)
Check S O.         (* 1 *)
Check S (S O).     (* 2 *)
Check S (S (S O)). (* 3 *)

Definition isZero (n : nat) : bool :=
  match n with
  | O => true
  | S _ => false
  end.

Compute isZero O.         (* true  *)
Compute isZero (S O).     (* false *)
Compute isZero (S (S O)). (* false *)

Definition isOne (n : nat) : bool :=
  match n with
  | O   => false
  | S O => true
  | _   => false
  end.

Compute isOne O.         (* false *)
Compute isOne (S O).     (* true  *)
Compute isOne (S (S O)). (* false *)

Fail Definition add (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => n2
  | S m1 => add m1 (S n2)
  end.

Fixpoint add (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => n2
  | S m1 => S (add m1 n2)
  end.

Print add.

Lemma add_O_n :
  forall n,
    add O n = n.
Proof.
Admitted.

Lemma add_n_O :
  forall n,
    add n O = n.
Proof.
Admitted.

Fixpoint mul (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => O
  | S m1 => add n2 (mul m1 n2)
  end.

Compute mul (S (S O)) (S (S O)). (* S (S (S (S O))) *)

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S m => mul n (factorial m)
  end.

Compute factorial (S (S (S O))). (* S (S (S (S (S (S O))))) *)

Fixpoint factorial_tr (n : nat) (acc : nat) : nat :=
  match n with
  | O => acc
  | S m => factorial_tr m (mul n acc)
  end.

Definition factorial_tailrec (n : nat) : nat :=
  factorial_tr n (S O).

End Nats.


Module Options.

Inductive option (T : Type) : Type :=
| None : option T
| Some : T -> option T.

Check option. (* option : Type -> Type *)
Check None.   (* forall (T : Type), option T *)
Check Some.   (* forall (T : Type), T -> option T *)

Check None bool. (* None bool : option bool *)
Check None nat.  (* None nat  : option nat  *)

Check Some bool true.  (* Some bool true : option bool *)
Check Some nat  (S O). (* Some nat (S O) : option nat  *)

(* forall is just "->" generalized! *)
Check Nat.add : forall (n1 : nat), forall (n2 : nat), nat.

(* we can also ask for type inference *)
Arguments None {T}.
Arguments Some {T} _.

Check None. (* None : option ?T *)
Check Some. (* Some : ?T -> option ?T *)

Check Some true.  (* Some true : option bool *)
Check Some (S O). (* Some (S O) : option nat  *)

Definition pred (n : nat) : option nat :=
  match n with
  | O => None
  | S m => Some m
  end.

Compute pred 0. (* None   *)
Compute pred 1. (* Some 0 *)
Compute pred 2. (* Some 1 *)

Lemma pred_None_inv :
  forall n,
    pred n = None ->
    n = 0.
Proof.
Admitted.

End Options.


Module Lists.

Inductive list (T : Type) : Type :=
| nil : list T
| cons : T -> list T -> list T.

(* infer some parameters *)
Arguments nil {T}.
Arguments cons {T} _ _.

Fixpoint length {A : Type} (l : list A) : nat :=
  match l with
  | nil => O
  | cons x xs => S (length xs)
  end.

Compute length nil.                   (* 0 ... but which nil?! *)
Compute length (cons 1 nil).          (* 1 *)
Compute length (cons 1 (cons 2 nil)). (* 2 *)

Fixpoint countdown (n : nat) : list nat :=
  match n with
  | O => cons n nil
  | S m => cons n (countdown m)
  end.

Compute countdown 1. (* cons 0 nil *)
Compute countdown 3. (* cons 3 (cons 2 (cons 1 (cons 0 nil))) *)

Lemma length_countdown :
  forall n,
    length (countdown n) = S n.
Proof.
Admitted.


Set Implicit Arguments.

Fixpoint app (A : Type) (l1 l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | cons x xs => cons x (app xs l2)
  end.

(* looks familiar! *)
Print Nat.add.
Print app.

Lemma app_nil_l :
  forall A (l : list A),
    app nil l = l.
Proof.
  (* think add_O_n *)
Admitted.

Lemma app_l_nil :
  forall A (l : list A),
    app l nil = l.
Proof.
  (* think add_n_O *)
Admitted.

Lemma app_assoc :
  forall A (l1 l2 l3 : list A),
    app l1 (app l2 l3) = app (app l1 l2) l3.
Proof.
Admitted.

Lemma length_app :
  forall A (l1 l2 : list A),
    length (app l1 l2) = length l1 + length l2.
Proof.
Admitted.

Fixpoint rev A (l : list A) : list A :=
  match l with
  | nil => nil
  | cons x xs => app (rev xs) (cons x nil)
  end.

Compute rev (cons 1 (cons 2 nil)). (* cons 2 (cons 1 nil) *)
Compute rev (countdown 10).

Lemma rev_involutive :
  forall A (l : list A),
    rev (rev l) = l.
Proof.
Admitted.

Fixpoint rev_tr A (l : list A) (acc : list A) : list A :=
  match l with
  | nil => acc
  | cons x xs => rev_tr xs (cons x acc)
  end.

Definition rev_tailrec A (l : list A) : list A :=
  rev_tr l nil.

Compute rev_tailrec (countdown 10).

Lemma rev_tailrec_rev :
  forall A (l : list A),
    rev_tailrec l = rev l.
Proof.
Admitted.

Fixpoint map A B (f : A -> B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons x xs => cons (f x) (map f xs)
  end.

Compute countdown 3.
(* cons 3 (cons 2 (cons 1 (cons 0 nil))) *)

Compute map (fun x => x + 1) (countdown 3).
(* cons 4 (cons 3 (cons 2 (cons 1 nil))) *)

Fixpoint isEven (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S m) => isEven m
  end.

Compute map isEven (countdown 3).
(* cons false (cons true (cons false (cons true nil))) *)

Lemma length_map :
  forall A B (f : A -> B) l,
    length (map f l) = length l.
Proof.
Admitted.

Definition compose A B C (f : B -> C) (g : A -> B) x :=
   f (g x).

Lemma map_map_compose :
  forall A B C (f : B -> C) (g : A -> B) l,
    map f (map g l) = map (compose f g) l.
Proof.
Admitted.

End Lists.


(* list notations *)
Require Import List.
Import ListNotations.

Print list.

Check [1; 2; 3] : list nat.
Check [true; false; true] : list bool.

Check [] : list bool.
Compute (1 :: 2 :: 3 :: []) : list nat.
Compute (true :: [false; true]) : list bool.

Compute [1; 2; 3] ++ [4; 5; 6].
Compute [true] ++ [false].

Fixpoint myrev {A} (l : list A) :=
  match l with
  | [] => []
  | x :: xs => myrev xs ++ (x :: nil)
  end.


(* =========== Proving factorial = factorial_tailrec ========= *)

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S m => n * factorial m
  end.

Fixpoint factorial_tr (n : nat) (acc : nat) : nat :=
  match n with
  | O => acc
  | S m => factorial_tr m (n * acc)
  end.

Definition factorial_tailrec (n : nat) : nat :=
  factorial_tr n 1.

(* include the arithmetic solver tactics *)
Require Import Psatz.

(* need to be clever! *)
Lemma factorial_tr_factorial :
  forall n acc,
    factorial_tr n acc = factorial n * acc.
Proof.
  induction n; simpl; intros; auto.
  rewrite IHn. lia.
Qed.

Lemma factorial_tailrec_factorial :
  forall n,
    factorial_tailrec n = factorial n.
Proof.
  unfold factorial_tailrec. intros.
  rewrite factorial_tr_factorial.
  lia.
Qed.


(* ======================== Environments ======================= *)

(* pairs for (key, values) *)
Print pair.

Check (1, 2) : (nat * nat)%type.
Check (true, [1; 2; 3]) : (bool * list nat)%type.

Compute fst (1, true). (* evalutes to 1 *)
Compute snd (1, true). (* evaluates to true *)

Definition myfst A B (pr : A * B) : A :=
  match pr with
  | (a, b) => a
  end.

Definition mysnd A B (pr : A * B) : B :=
  match pr with
  | (a, b) => b
  end.

(* strings for keys *)
Require Import String.
Open Scope string_scope.

Check "Hello World!" : string.
Check string_dec : forall s1 s2 : string, {s1 = s2} + {s1 <> s2}.

Module Env.
Set Implicit Arguments.

Definition var : Type := string.
Definition var_eq : forall v1 v2 : var, {v1 = v2} + {v1 <> v2} :=
   string_dec.

Definition env (V : Type) :=
  list (string * V).

Fixpoint lookup V (kvs : env V) (x : var) : option V :=
  match kvs with
  | [] => None
  | (key, val) :: rest =>
      if var_eq key x
      then Some val
      else lookup rest x
  end.

Definition update V (kvs : env V) (x : var) (v : V) : env V :=
  (x, v) :: kvs.

Definition empty {V} : env V := [].


(* if we lookup a var we just set, we get whatever we set it to *)
Compute lookup (update empty "x" 1) "x".
(* Some 1 *)

(* if we lookup a var we never set, we get back None *)
Compute lookup (update empty "y" 1) "x".
(* None *)

(* lookup finds the 'most recent' binding for a variable *)
Compute lookup (update (update empty "x" 1) "x" 2) "x".
(* Some 2 *)

(* lookup skips over keys until it finds the one we're looking for *)
Compute lookup (update (update empty "x" 1) "y" 2) "x".
(* Some 1 *)

End Env.