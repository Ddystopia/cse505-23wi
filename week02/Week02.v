(*
We use functional programming a lot in Coq, and functional programming
typically involves a lot of list manipulation (the name for one of
the original functional programming languages, "LISP", stands for
"list processing"!).

We can combine the ideas we've seen from "nat" (recursive constructors)
and "option" (parameterized types) to encode the type "list" in Coq.
*)

Module Lists.

Inductive list (T : Type) : Type :=
| nil : list T
| cons : T -> list T -> list T.

(*
A "list T" value is either "nil" (the empty list) or made by applying
the "cons" constructor to some value of type "T" and ANOTHER "list T".

As with options, writing the types out over and over gets tedious, so let's
ask Coq to infer some of the typically-obvious type parameters for us:
*)

Arguments nil {T}.
Arguments cons {T} _ _.

(*
We can define functions over lists using pattern matching and recursion,
just as we saw for natural numbers. One new trick is that we also ask Coq
to infer type parameters for *function* arguments too:
*)

Fixpoint length {A : Type} (l : list A) : nat :=
  match l with
  | nil => O
  | cons x xs => S (length xs)
  end.

(*
Similar to how our earlier "Arguments" declaration where we asked Coq to
infer the type parameters of the "nil" and "cons" constructors, here we
put curly braces "{ }" around the type argument to "length" so that Coq
will try to infer it for us.
*)

Compute length nil.                   (* 0 ... but which nil?! *)
Compute length (cons 1 nil).          (* 1 *)
Compute length (cons 1 (cons 2 nil)). (* 2 *)

(*
Here's a simple function that's useful for testing later functions.
*)
Fixpoint countdown (n : nat) : list nat :=
  match n with
  | O => cons n nil
  | S m => cons n (countdown m)
  end.

Compute countdown 1. (* cons 0 nil *)
Compute countdown 3. (* cons 3 (cons 2 (cons 1 (cons 0 nil))) *)

(*
Just to check, let's prove a little lemma about "length" and "countdown".
*)
Lemma length_countdown :
  forall n,
    length (countdown n) = S n.
Proof.
  (* EXERCISE: why doesn't this go through without simpl? *)
  induction n; simpl; auto.
Qed.


(*
Before we continue, let's ask Coq to always try to infer all 'obvious'
type arguments so we don't have to add the curly brace annotations
ourselves. This sort of turns on 'global type inference wherever possible'.
*)
Set Implicit Arguments.

(*
We often want to make a bigger list by 'putting two smaller' lists together.
For example, maybe we have the lists [1, 2, 3] and [4, 5, 6] and we want the
list [1, 2, 3, 4, 5, 6]. For that we use the "app" (short for 'append')
function:
*)

Fixpoint app (A : Type) (l1 l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | cons x xs => cons x (app xs l2)
  end.

(*
A couple things to note about this definition of "app":
    - In Coq, we never mutate any data structures. There are no pointers
      or anything else that we can directly access to change a value once
      it has been defined. Thus when we append two lists, what we're really
      doing is making a *new* list that has the content of both of the
      input lists.

    - "app" for lists looks a lot like "add" for nats!
*)
Print Nat.add.
Print app.

(*
In some sense, nats are just lists 'with no data, just links'!

That means that our theorems about nats often provide good intuition for proving
things about proving things for lists.

For example, "app nil l = l" is sort of like "add 0 n = n":
*)
Lemma app_nil_l :
  forall A (l : list A),
    app nil l = l.
Proof.
  (* just goes through, like we saw for add_O_n *)
  auto.
Qed.

(*
And "app l nil = l" is sort of like "add n 0 = n" -- it requires induction!
*)
Lemma app_l_nil :
  forall A (l : list A),
    app l nil = l.
Proof.
  intros A l.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.  

  Restart.
  (* or more concisely: *)
  induction l; simpl; auto.
  f_equal; auto.
Qed.

(*
Associativity follows the same pattern again.
*)
Lemma app_assoc :
  forall A (l1 l2 l3 : list A),
    app l1 (app l2 l3) = app (app l1 l2) l3.
Proof.
  (* EXERCISE: compare to induction hypothesis if we do intros first! *)
  induction l1; simpl; intros; auto.
  f_equal; auto.
Qed.

(*
The length of two lists appended together is just the sum of their
individual lengths.
*)
Lemma length_app :
  forall A (l1 l2 : list A),
    length (app l1 l2) = length l1 + length l2.
Proof.
  induction l1; intros.
  - simpl. reflexivity.
  - simpl. f_equal. apply IHl1. 

  (* or as a one-liner *)
  Restart.
  induction l1; simpl; auto.
Qed.

(*
Once we have "app", we can also define a function to reverse lists:
*)
Fixpoint rev A (l : list A) : list A :=
  match l with
  | nil => nil
  | cons x xs => app (rev xs) (cons x nil)
  end.

(*
"rev" works by first recursively reversing the tail of a list and then
adding what used to be the first element to the end.

Let's test a few examples to check that our definition is working.
*)

Compute rev (cons 1 (cons 2 nil)). (* cons 2 (cons 1 nil) *)
Compute rev (countdown 10).

(*
As expected, "rev" preserves the length of a list.
*)
Lemma length_rev :
  forall A (l : list A),
    length (rev l) = length l.
Proof.
  (* EXERCISE *)
Admitted.

(*
If we reverse a list and then reverse that result, we should get back the same
list we started with:
*)
Lemma rev_involutive :
  forall A (l : list A),
    rev (rev l) = l.
Proof.
  induction l; simpl; auto.
  (* uh oh... kinda stuck -- we don't know anything about rev and app! *)
Abort.

(*
In general, if you need some additional fact to complete a proof, you should back up
and prove the lemma you need first. You should almost *never* do nested inductions!
*)
Lemma rev_app :
  forall A (l1 l2 : list A),
    rev (app l1 l2) = app (rev l2) (rev l1).
Proof.
  induction l1; simpl; intros; auto.
  - (* would like to use "app_l_nil" here, but equality is flipped... *)
    symmetry.
    (* now it's in the right order! *)
    apply app_l_nil.

    (* we could also have just used app_l_nil as a rewrite: *)
    Undo. Undo.
    rewrite app_l_nil. reflexivity.
  - rewrite IHl1. rewrite app_assoc. reflexivity.
Qed.

(*
Now we can finish that "rev_involutive" proof!
*)
Lemma rev_involutive :
  forall A (l : list A),
    rev (rev l) = l.
Proof.
  induction l; simpl; auto.
  rewrite rev_app. rewrite IHl.
  simpl. reflexivity.
Qed.

(*
When we define functions in Coq, we are usually just using them to specify
a formal model of some system. The main point of such functions is just to
give us mathematical definitions we can reason about. So we typically
optimize our definitions for *simplicity* and ease of reasoning. We typically
do *not* care too much about how 'fast' our functions are.

Having said that, you may have noticed that "rev" actually takes O(N^2)
time to reverse a list of length N. A standard trick for making functions
like "rev" more efficient is to use 'tail recursion':
    https://en.wikipedia.org/wiki/Tail_call

The details of tail recursion are not too important for 505 generally, BUT
it is a useful trick to know because it's often a more direct way to model
the behavior of a loop from an imperative programming language in pure
functional code in Coq.

A function is "tail recursive" if all recursive calls are in "tail position",
which roughly means that there's 'no work left to do' when the function
returns. Often, to make a function tail recursive, we add an extra
'accumulator' argument that we update as the function recurses and which
we use to return the result in the base case. This musical presentation
parodies a few Disney songs and provides a good, funny introduction to
tail recursion:
    https://www.youtube.com/watch?v=-PX0BV9hGZY

Let's see how to make a tail-recursive version of "rev":
*)

(* tail-recursive helper function that takes an 'accumulator' *)
Fixpoint rev_tr A (l : list A) (acc : list A) : list A :=
  match l with
  | nil =>
      (* just return the accumulator in the nil (base) case *)
      acc
  | cons x xs =>
      (* cons the head onto the accumulator in the cons (recursive) case *)
      rev_tr xs (cons x acc)
  end.

(* (non-recursive) wrapper to set the right initial accumulator *)
Definition rev_tailrec A (l : list A) : list A :=
  rev_tr l nil.

(*
This tail-recursive version of reverse works by repeatedly consing the head
of the list onto the accumulator and then just returning the accumulator in
the base case.

Since the first element of the list will be the first thing consed onto the
accumulator, it will end up as the last element in the accumulator. Similarly,
the second element will end up as the second-to-last last element in the
accumulator. The last element of the list will be the last thing cons onto
the accumulator, so it will be the first element of the result, just as it
should.
*)

Compute rev_tailrec (countdown 10).

(*
Let's prove that "rev_tailrec" and "rev" always do the same thing.
*)
Lemma rev_tailrec_rev :
  forall A (l : list A),
    rev_tailrec l = rev l.
Proof.
  induction l as [| x xs].
  - simpl.
    (* "simpl" didn't do anything?!
       That's because we need to first "unfold" rev_tailrec!
       In this case, that should also be a hint to us that we
       should be proving a lemma about rev_tr instead, but
       in many cases just using "unfold" to reveal a helper
       function is fine. *)

  Restart.
  unfold rev_tailrec.
  induction l as [| x xs].
  - simpl. reflexivity.
  - simpl.
    (* Looks like the only way to use the induction hypothesis
       IHxs is to rewrite with it 'backwards' (right-to-left). *)
    rewrite <- IHxs.
    (* But now we're stuck: we haven't proved anything about
       the relationship between "app" and "rev_tr". At this
       point we should back out and try doing that first. *)
Abort.

(* Let's first try to just prove exactly what we needed above. *)
Lemma rev_tr_app_attempt :
  forall A (xs : list A) (x : A),
    rev_tr xs (cons x nil) = app (rev_tr xs nil) (cons x nil).
Proof.
  induction xs; intros.
  - simpl. reflexivity.
  - simpl.
    (* Hmm, there's no place we can use the induction hypothesis IHxs...
       That's because our property only talks about a *specific* 
       accumulator!
       
       At this point we are stuck again :\
       We need to back up and *generalize* the property we want to prove! *)
Abort.

(*
If we just generalize the accumulator, then we'll try to prove something
like:
         forall A (xs acc : list A),
            rev_tr xs acc = app (rev_tr xs nil) acc

Which is OK (and provable), but we can save ourselves a little trouble
(and actually makes the proofs simpler) if we notice that "rev_tr xs nil"
is just "rev xs"!
*)

Lemma rev_tr_app_rev :
  forall A (xs acc : list A),
    rev_tr xs acc = app (rev xs) acc.
Proof.
  (* NOTE: induction *before* the other intros! *)
  induction xs; intros.
  - simpl. reflexivity.
  - simpl.
    (* Now we get a great rewrite from the induction hypothesis IHxs. *)
    rewrite IHxs.
    (* At this point, we just need to reassociate the "app" on the RHS. *)
    rewrite <- app_assoc. simpl. reflexivity.
Qed.

(*
You may not have noticed it, but we narrowly avoided getting stuck again.
If we had been 'too greedy' with intros, we would have ended up with a
weaker induction hypothesis that doesn't enable our key rewriting step!
*)
Lemma rev_tr_app_rev_don't_be_greedy :
  forall A (xs acc : list A),
    rev_tr xs acc = app (rev xs) acc.
Proof.
  intros; induction xs.
  - simpl. reflexivity.
  - simpl.
    (* Yikes! If we introduce too much, our induction hypothesis is too
       weak and we can't get that key rewrite!!
       
    rewrite IHxs. (* <== does not work any more! *)
    *)
Abort.

(*
Anyways, using "rev_tr_app_rev" makes proving our original specification
for "rev_tailrec" easy.
*)
Lemma rev_tailrec_rev :
  forall A (l : list A),
    rev_tailrec l = rev l.
Proof.
  unfold rev_tailrec; intros.
  rewrite rev_tr_app_rev.
  rewrite app_l_nil.
  reflexivity.
Qed.

(*
To wrap up our brief introduction to lists, here's one of the 'hall of fame'
functions from functional programming: "map"!
*)
Fixpoint map A B (f : A -> B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons x xs => cons (f x) (map f xs)
  end.

(*
In some sense "map" just takes an "A -> B" function and 'lifts' it to be
a "list A -> list B" function by simplifying applying the function to each
element of a list.
*)

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

(*
As expected, map preserves the length of a list.
*)
Lemma length_map :
  forall A B (f : A -> B) l,
    length (map f l) = length l.
Proof.
  induction l; simpl; auto.
Qed.

(*
We can also show how to perform a 'deforestation' on sequences of maps
by replacing nested maps with a single map that uses the composed functions.
*)
Definition compose A B C (f : B -> C) (g : A -> B) x :=
   f (g x).

Lemma map_map_compose :
  forall A B C (f : B -> C) (g : A -> B) l,
    map f (map g l) = map (compose f g) l.
Proof.
  unfold compose.
  induction l; simpl; auto.
  f_equal. auto.
Qed.

End Lists.

(*
The version of lists from the Coq standard library also comes with
some nice notation that makes it a bit easier to work with lists.

Let's include the library and look at some of those notations.
*)
Require Import List.
Import ListNotations.

(*
First, note that the standard library lists are defined just like
we defined our own lists earlier.
*)
Print list.

(*
The standard library lists provide "[ ]" notation for writing out
literal lists where elements are separated by semicolons ";".
*)
Check [1; 2; 3] : list nat.
Check [true; false; true] : list bool.

(*
This lets us write the empty list "nil" as "[]".
*)
Check [] : list bool.

(*
We also get an infix "::" operator for cons.
*)
Compute (1 :: 2 :: 3 :: []) : list nat.
Compute (true :: [false; true]) : list bool.

(*
Somewhat similarly, there's also an infix "++" operator for append.
*)
Compute [1; 2; 3] ++ [4; 5; 6].
Compute [true] ++ [false].

(*
Finally, we can also use the notations (for the constructors, not
for append) in pattern matches as well!
*)
Fixpoint myrev {A} (l : list A) :=
  match l with
  | [] => []
  | x :: xs => myrev xs ++ (x :: nil)
  end.


(* =========== Proving factorial = factorial_tailrec ========= *)


(*
OK, now that we've seen more tactics, let's get back to proving our tail-recursive
version of factorial equivalent to 'regular' factorial. We'll use the standard
library version of nats because they have better notation, lemmas, and tactic support.
*)
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

(*
If we are clever and first prove just the right lemma from the very beginning,
then things go through without much hassle!
*)
Lemma factorial_tr_factorial :
  forall n acc,
    factorial_tr n acc = factorial n * acc.
Proof.
  induction n; simpl; intros; auto.
  rewrite IHn.
  (* the lia tactic is a decision procedure for linear arithmetic *)
  lia.
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

(*
In PL we often want to build "environments" that associate names
with 'something' where 'something' could be a value, a type, etc.

For simplicity, we'll plan on using "association lists" to model
environments:
    https://en.wikipedia.org/wiki/Association_list

An association list is just a list of pairs where we consider the
first thing in each pair a 'key' and the second thing in each pair
a 'value'.

The Coq standard library already provides pairs in an inductive type
called "prod" which has just one constructor called "pair".
*)
Print pair.

(*
The standard library version of pairs also comes with nice notation
for building pairs with "( )" where elements are separated by a
comma ",".
*)

Check (1, 2) : (nat * nat)%type.
Check (true, [1; 2; 3]) : (bool * list nat)%type.

(*
If the first value in a pair has type "A" and the second value has
type "B", then the pair has type "A * B". In the type context we
consider "*" the 'pair type constructor. However, since in other
contexts we think of the same symbol "*" as meaning multiplication
on numbers, we need to disambiguate the the "%type" annotations
above to tell Coq that we mean 'the type version of "*"' in those
cases.
*)

(*
The standard library version of pairs provide the "fst" and "snd"
functions for extracting the first and second elements of pairs
respectively.
*)
Compute fst (1, true). (* evaluates to 1 *)
Compute snd (1, true). (* evaluates to true *)

(*
Finally, we can also use the "( )" notation in pattern matches when
we define functions over lists. To show this, here are recreations
of the "fst" and "snd" functions:
*)
Definition myfst A B (pr : A * B) : A :=
  match pr with
  | (a, b) => a
  end.

Definition mysnd A B (pr : A * B) : B :=
  match pr with
  | (a, b) => b
  end.

(*
In addition to pairs, we will also need some type to use for 'names'
as the 'keys' in our association lists. We'll use the String type
from Coq's standard library for that.
*)
Require Import String.
Open Scope string_scope.

Check "Hello World!" : string.

(*
In addition to the nice notation, the main function we need from
the String library is a function that decides equality between
strings.
*)
Check string_dec : forall s1 s2 : string, {s1 = s2} + {s1 <> s2}.
(*
This type is fancy, and we'll see how to use it below, but for
now you can really just think about using string_dec as if it
had the type:
    string -> string -> bool
*)

Module Env.
Set Implicit Arguments.

(* First let's define some synonyms for our types. *)
Definition var : Type := string.
Definition var_eq : forall v1 v2 : var, {v1 = v2} + {v1 <> v2} :=
   string_dec.

(*
Now we'll define an environment to be a list of "(string, V)"
pairs for any type V that we want to use. "V" could be values in
a programming language we're modeling, types, etc.
*)
Definition env (V : Type) :=
  list (string * V).

(*
Environments need to support two basic operations:
"lookup" and "update".

Given an environment "kvs" and a target variable name "x",
the "lookup" function scans the list of "(key, value)" pairs
in "kvs" until it finds a pair where the first element is equal
to "x". At that point it returns whatever the second element of
that pair is. If "lookup" gets to the end of the list "kvs" without
finding a match, it returns "None", so the whole type needs to
return an 'optional value' (see the discussion on options earlier).
*)
Fixpoint lookup V (kvs : env V) (x : var) : option V :=
  match kvs with
  | [] => None
  | (key, val) :: rest =>
      if var_eq key x
      then Some val
      else lookup rest x
  end.

(*
Given an environment "kvs", a target variable name "x",
and a value "v" we want to 'bind' (associate) "x" to, the
"update" function just adds the pair "(x, v)" to the front
of the "kvs" environment so that subsequent calls to look up
"x" will get "Some v".
*)
Definition update V (kvs : env V) (x : var) (v : V) : env V :=
  (x, v) :: kvs.

(*
For convenience, we also define the "empty" environment as just
the empty list ("nil").
*)
Definition empty {V} : env V := [].

(*
Let's test a couple of examples to see how these functions
work together.
*)

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
