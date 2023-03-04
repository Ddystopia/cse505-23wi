Require HW6.

Require Import Arith Lia List String.
Import ListNotations.
Open Scope string.

Set Implicit Arguments.

(*
 * This "Module Type" contains the type of everything we expect you to define or
 * prove in this homework.
 *)
Module Type HW6sig.


End HW6sig.

(* Check that HW6 has the above signature. *)
Module M <: HW6sig := HW6.
