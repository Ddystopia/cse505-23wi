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
