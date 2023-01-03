Require HW1.

(*
 * This "Module Type" contains the type of everything we expect you to define or
 * prove in this homework.
 *)
Module Type HW1sig.
  Inductive bool : Type :=
  | true : bool
  | false : bool.

  Definition notb (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

  Definition andb (b1 : bool) (b2 : bool) : bool :=
    match b1 with
    | true => b2
    | false => false
    end.

  Parameter orb : bool -> bool -> bool.

  Parameter orb_comm :
    forall b1 b2,
      orb b1 b2 = orb b2 b1.

  Parameter notb_andb_is_orb_notb :
    forall b1 b2,
      notb (andb b1 b2) = orb (notb b1) (notb b2).

  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  Fixpoint add (n1 : nat) (n2 : nat) : nat :=
    match n1 with
    | O => n2
    | S m1 => S (add m1 n2)
    end.

  Parameter add_S_n :
    forall n1 n2,
      add (S n1) n2 = S (add n1 n2).

  Parameter add_n_S :
    forall n1 n2,
      add n1 (S n2) = S (add n1 n2).

  Parameter add_comm :
    forall n1 n2,
      add n1 n2 = add n2 n1.
End HW1sig.

(* Check that HW1 has the above signature. *)
Module M <: HW1sig := HW1.
