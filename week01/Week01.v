(* Comments in Coq go between "(*" and "*)". *)

(* comments (* can (* be (* nested *)*)*)*)

(*

We'll begin our introduction to Coq by studying how to define
basic types.

While Coq comes with extensive standard libraries, very few
types are truly "built in". We even define things like booleans
and numbers for ourselves in Coq!

Since we will be re-defining types that are already available
in the standard library, we'll put our definitions inside of
"modules" which are really just a collection of definitions.
That way, outside of the module, we can still use the definitions
and theorems about these types from the standard library.

*)
Module Booleans.

(*
The keyword "Inductive" begins the definition of a new inductive type.

Let's see the definition of booleans as an inductive type:
*)

Inductive bool : Set :=
| true : bool
| false : bool.

(*
When we define an inductive type "T", we specify its "constructors" which
are the ONLY ways to construct an expression that has type "T".

The definition above says that "true" and "false" are expressions of
type "bool" and, implicitly, are the ONLY expressions of type "bool".

The syntax "e : T" means "expression e has type T".

In Coq, every valid expression has a type.
Also in Coq, types *are* expressions.
That means types must also have types!

So the definition above is declaring "bool" as a type whose own type
is "Set". We won't be too concerned about the details of types of types
for now, but we can roughly thing of "Set" as the "type of types that
we use in 'normal programming'", e.g., booleans, numbers, lists, etc.
*)

(*
In addition to inductive types, the other kind of thing we can define
directly in Coq are functions.
*)

Definition negb (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

(*
Here we used the keyword "Definition" to bind the name "negb" to a function
which takes one argument, "b", and returns its negation.

Our definition of "negb" uses "pattern matching" to test which constructor
was used to construct its argument "b".
    - In the first case, it says that, if "b" was constructed with "true",
      then the function returns "false".
    - In the second case, it says that, if "b" was constructed with "false",
      the the function returns "true".

You can think of "match" expressions like case or switch statements from
other languages.

In Coq, pattern matches *must* be exhaustive. Try removing the
"| false => true" line above and see what Coq says about it.
*)

(*
To call a function, you just put its name followed by a space " " and
then the argument you want to pass to the function.

You can see how Coq will evaluate an expression using the "Compute" command.
*)

Compute negb true.
Compute negb false.

(*
We can also define functions that take multiple arguments:
*)

Definition andb (b1 : bool) (b2 : bool) : bool :=
    match b1 with
    | true => b2
    | false => false
    end.

(*
We call functions with multiple arguments the same way as single argument
functions: by putting a space before each argument.
*)

Compute andb true true.
Compute andb true false.
Compute andb false true.
Compute andb false false.

(*
Let's prove that "andb" is commutative.
*)

Lemma andb_comm :
  forall b1 b2,
    andb b1 b2 = andb b2 b1.
Proof.
  (* assume an arbitrary boolean and name it "x" *)
  intro x.

  (* assume another arbitrary boolean and name it "y" *)
  intro y.

  (* case analysis on "x"
     --> 2 subgoals: "x is true" and "x is false"
    
    We know these are the only possible values for "x"
    from the definition of its type: "bool"! *)
  destruct x.

    - (* in this first subgoal we assume "x is true" *)

      (* case analysis on "y"
         --> 2 nested subgoals: "y is true" and "y is false" *)
      destruct y.

      + (* first nested subgoal, additionally assume "y is true" *)

        (* solve goal that something is equal to itself *)
        reflexivity.

        (* first nested subgoal done! *)

      + (* second nested subgoal, still in "x is true" outer case,
           but now additionally assuming "y is true" *)

        (* simplify the goal by evaluating the "andb" function *)
        simpl.

        (* solve goal that something is equal to itself *)
        reflexivity.
    
  - (* second outer subgoal where we are assuming "x is false" *)

      (* another case analysis on "y" *)
      destruct y.

      + (* in nested subgoal where we assume "x is false" and "y is true" *)

        (* simplify the goal by evaluating the "andb" function *)
        simpl.

        (* solve goal that something is equal to itself *)
        reflexivity.

      + (* in nested subgoal where we assume "x is false" and "y is false" *)

        (* solve goal that something is equal to itself *)
        reflexivity.

(* all subgoals solved, check completed proof *)
Qed.

(*
That was pretty verbose and repetitive. In Coq we usually don't need to
step through each detail quite so explicitly and repeatedly if we structure
our proof scripts carefully. Here is another version of the same proof.
*)

Lemma andb_comm_shorter_proof_script :
  forall b1 b2,
      andb b1 b2 = andb b2 b1.
Proof.
  destruct b1; destruct b2; auto.
Qed.

(*
In a proof script, "tac1 ; tac2" means "run tactic tac2 on every subgoal
that results from running tactic tac1". The "auto" tactic handles 'easy'
goals like proving things equal to themselves, etc.
*)

(*
We can ask Coq to tell us the type of an expression using
the "Check" command.
*)

Check negb.

(*
The above command should print something like:

      negb : bool -> bool

We use the arrow "->" to construct function types.

The above type for "negb" means that "negb is a function which takes
a bool as its argument and returns a bool as its result".

Let's use "Check" to see the type of "andb" as well:
*)

Check andb.

(*
The above command should print something like:

      andb : bool -> bool -> bool

What the heck does that mean?!

In Coq (and many functional programming languages), functions can only
take a *single* argument. There are different ways to simulate multi-argument
functions though. In this case we are using a technique known as "currying"
to encode "andb" as a binary function.

In particular, the arrow "->" in functions types "associates to the right",
so the type of "and" really means:

      andb : bool -> (bool -> bool)

That is, "andb" is a function which takes a bool as its argument and
RETURNS ANOTHER FUNCTION as its result. That function in turn takes
a bool as its argument and produces a bool as its result.

When we define curried functions using "Definition" we are taking
advantage of some "syntactic sugar" in Coq. In the case of "andb",
the 'real' definition of the function is more like:
*)

Definition andb_no_sugar : bool -> bool -> bool :=
  fun b1 =>
    fun b2 =>
      match b1 with
      | true => b2
      | false => false
      end.

(*
But this alternate version works just the same as our original "andb".

You can see the definition a name is bound to using the "Print" command.
*)

Print andb.
Print andb_no_sugar.

(*
See? No difference!
*)

End Booleans.

(*
OK, enough booleans for now, let's move on to bigger types.

There were only 2 possible values of type "bool", but if we
want to encode things like numbers we'll need some way of defining
infinite sets of values.
*)

Module Nats.

(*
To define infinite sets of values, we can use recursive
constructors in Inductive type definitions:
*)

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

(*
This definition says that "nat" is a type whose type is "Set" and that
there are only two ways to construct a "nat" value:
  (1) Using the "O" constructor, which is just a "nat".
  (2) Using the "S" constructor APPLIED TO ANOTHER "nat"!

At this point, it's worth noting that constructors are NOT functions!

It may be a bit confusing since we wrote the type for "S" as "nat -> nat".

However, constructors are more like 'tags' that hang on to their arguments.
Later, when we pattern match on a value of an inductive type T, we are
testing which constructor was used as a 'tag' to make that value.

"nat" encodes the numbers O, 1, 2, 3, ... using unary:
*)

Check O.           (* 0*)
Check S O.         (* 1 *)
Check S (S O).     (* 2 *)
Check S (S (S O)). (* 3 *)

(*
Don't worry, there is nice built in notation when use the standard
library version of "nat" so that we don't have to type N "S"s to
write the number N!

Since all constructors are just tags, we can use pattern matching
to write functions over "nat" similar what we did early in the 
"Booleans" module:
*)

Definition isZero (n : nat) : bool :=
  match n with
  | O => true
  | S _ => false
  end.

Compute isZero O.         (* true  *)
Compute isZero (S O).     (* false *)
Compute isZero (S (S O)). (* false *)

(*
The "isZero" function shows how we can use pattern matching on a value
of any inductive type. We also see our first use of the "_" pattern
which is a 'wildcard' -- it will match any argument to "S" in the second
case above.

Cases in pattern matches are also processed in order with the first case
that matches being the one that gets evaluated.
*)

Definition isOne (n : nat) : bool :=
  match n with
  | O   => false
  | S O => true
  | _   => false
  end.

Compute isOne O.         (* false *)
Compute isOne (S O).     (* true  *)
Compute isOne (S (S O)). (* false *)

(*
Let's try to define addition ...
*)

Fail Definition add (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => n2
  | S m1 => add m1 (S n2)
  end.

(*
This fails with a message like:

      The command has indeed failed with message:
      The reference add was not found in the current environment.

That's because, when use "Definition" to define something, the
thing we're defining is not available in the body of the definition.

To define recursive functions like "add" we need to use
a "Fixpoint" definition:
*)

Fixpoint add (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => n2
  | S m1 => S (add m1 n2)
  end.

(*
In Coq, all functions must terminate. When we use a "Fixpoint" definition,
Coq checks that all recursive arguments are on *smaller* syntactic
subterms of the function's recursive argument.
*)

Print add.

(*
The output of this "Print" command indicates that "add" recurses
structurally on its first argument "n1":

      add = 
        fix add (n1 n2 : nat) {struct n1} : nat :=
          match n1 with
          | O => n2
          | S m1 => S (add m1 n2)
          end
          : nat -> nat -> nat

This can have important consequences when we try to prove things about
recursive functions! Since we often want to use tactics like "simpl",
we need to consider how and when Coq will be able to evaluate part of
a function call.

For example, proving that "0 + n = n" is trivial:
*)

Lemma add_O_n :
  forall n,
    add O n = n.
Proof.
  intro n.
  simpl.
  reflexivity.

  (* alternately, we could have just used "auto" *)
  Restart.
  auto.
Qed.

(*
This proof is easy because "add" recurses on its first argument.
When we know that first argument is "O", then "add" just immediately
evaluates and returns its second argument.

But what happens if we flip the order of the arguments?
*)

Lemma add_n_O :
  forall n,
    add n O = n.
Proof.
  intro n.
  simpl.
  (* "simpl" didn't do anything! Yikes! *)
Abort.

(*
Well, earlier we saw how "destruct" let us perform case analysis so
that we could learn something about a function's arguments and then
evaluate it. Let's see how that works out here:
*)
Lemma add_n_O :
  forall n,
    add n O = n.
Proof.
  intro n.

  (* "n" could be "O" or "S m" for other nat "m" *)
  destruct n as [| m].

  - (* Progress! If "n" is "O" the proof is easy. *)
    simpl. reflexivity.

  - (* Ah, but what if "n" is "S m" for some other nat "m"? ...
        Let's do the same trick on "m"! *)
    simpl. destruct m as [| p].

    + (* More progress! If "m" is "O" then "n" is "1"
         and the proof is easy. *)
      simpl. reflexivity.

    + (* Ah, but what if "m" is "S p" for other nat "p"? ...
         Something seems wrong about this ...  *)
      simpl. destruct p as [| q].

      * simpl. reflexivity.

      * (* This could take a while... *)
        simpl. destruct q as [| r].

        (* OH FOR GOODNESS SAKE! *)

(* We need a better strategy!! *)
Abort.

(*
While destruct did let us perform case analysis, it didn't tell
us enough to prove the recursive case of "add".

In general, to prove properties of recursive functions over
recursive types, we need recursive proofs!

That's what "induction" is for :)
*)
Lemma add_n_O :
  forall n,
    add n O = n.
Proof.
  intro n.

  (* "induction" is like case analysis, but we will also get
     an 'induction hypothesis' in the recursive case below. *)
  induction n as [| m].

  (* base case for "n = 0" *)
  - simpl. reflexivity.

  (* inductive case for "n = S m" where we know that
     "add m O = m" and still need to show "add n O = n" *)
  - simpl.

    (* Notice that we have an additional hypothesis "IHm"!
       We can use it to "rewrite" the goal. *)
    rewrite IHm.

    (* Now the goal is easy! *)
    reflexivity.
Qed.

(*
Here's another different, though also very reasonable, way to define "add".
*)

Fixpoint add_tailrec (n1 : nat) (n2 : nat) : nat :=
  match n1 with
  | O => n2
  | S m1 => add_tailrec m1 (S n2)
  end.

(*
This version is still structurally recursive on its first argument "n1",
but it 'stashes the successor "S"' from the first onto its second argument
*before* recursing rather than recursing and then 'adding a successor "S"'
*after* the recursive call returns.

Working with this alternate version of "add" makes some proofs play out
a bit differently. We'll see more about the differences between these
styles of recursion, but if you'd like to explore for yourself, we've
included a couple of exercises that may help develop a feel for them.
*)

Lemma add_tailrec_n_S :
  forall n1 n2,
    add_tailrec n1 (S n2) = S (add_tailrec n1 n2).
Proof.
  (* EXERCISE : FILL IN PROOF HERE *)
Admitted.

Lemma add_add_tailrec :
  forall n1 n2,
    add n1 n2 = add_tailrec n1 n2.
Proof.
  (* EXERCISE : FILL IN PROOF HERE *)
Admitted.

(*
We could keep formalizing nats and all different kinds of numbers,
but most of that work is already done for us in the standard library.

To give a taste for proving functions over nats, let's briefly define a couple
versions of factorial and stub out the lemmas we would need to prove them equivalent.

You can see many more operations and theorems about nat in Coq's
documentation at: https://coq.inria.fr/stdlib/Coq.Init.Nat.html
*)

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

(*
Somewhat similar to how we made an alternate version of "add" above with
"add_tailrec", we can also make a different version of "factorial" that
doesn't have any work left to do once a recursive call returns, though
we'll have to make a helper function that takes an "accumulator" argument:
*)

Fixpoint factorial_tr (n : nat) (acc : nat) : nat :=
  match n with
  | O => acc
  | S m => factorial_tr m (mul n acc)
  end.

Definition factorial_tailrec (n : nat) : nat :=
  factorial_tr n (S O).

(*
To prove that factorial and factorial_tr are equivalent, we need to be
a little clever. We'll actually see this problem over and over throughout
505, but we'll skip ahead for now and come back to this problem once we've
learned a few more tactics.
*)

End Nats.

(*
We saw earlier that all pattern matches in Coq must be exhaustive.

That means that all functions in Coq are *total*, i.e., they must return some
value for every well-typed argument.

Being required to always return some result can sometimes be a bummer though.
Consider trying to define the predecessor function on nats (the function that 
subtracts 1 from its argument):

    Definition pred (n : nat) : nat :=
      match n with
      | S m => m
      | O => ... (* nothing we can put here! *)
      end.

The predecessor of O "should be" -1, but that's not a natural number! There are 
a few choices for things we could do. For example, we could just return a wrong
(but well typed) answer, like O or 42. But that's kind of displeasing. A better
choice would be to signal an error of some kind. Coq doesn't have exceptions, 
but we can use the return value to safely signal an error.

We could define another inductive type to represent data that is "maybe a nat":

    Inductive maybe_nat : Set :=
    | NoNat : maybe_nat
    | SomeNat : nat -> maybe_nat.

This type is either NoNat, which we will use to indicate an error, or SomeNat, 
which contains the natural number if there is not an error. Another way to think
about it is as a type with "one more" element that the type nat has, and we can 
use this extra element for some other purpose, like error handling. (This is 
vaguely analogous to how a null pointer is sometimes used to signal an error, 
except that Coq's type system will force us to keep track of whether something
is a maybe_nat (analogous to a possibly null pointer) or a nat (analogous to a 
definitely non-null pointer).

Now we can implement an error-signaling version of predecessor like this:

    Definition pred (n : nat) : maybe_nat :=
      match n with
      | O => NoNat
      | S m => SomeNat m
      end.

But what if we have another "partial function" over a type T other than nat?
Do we have to make a maybe_T type as well for that case? There are a lot
of types, so we would end up with a lot of "maybe_T" inductive definitions...

Lucky for us, Coq allows us to define "parameterized" inductive types so
we can capture this pattern once and for all! (This is similar to generics in 
other languages.)
*)

Module Options.

Inductive option (T : Type) : Type :=
| None : option T
| Some : T -> option T.

(*
This parameterized definition of "option" encodes our "maybe_T" pattern for
any type T!

We say that "option" is a "type constructor" since it "takes a type as an argument
and forms a new type".
*)

Check option. (* option : Type -> Type *)

(*
Given a type "T", the only ways to build a value of type "option T" is use either:
    - the "None" constructor, which is a valid "option T" for any "T" or
    - the "Some" constructor applied to some value of type "T"
*)

Check None. (* forall (T : Type), option T *)
Check Some. (* forall (T : Type), T -> option T *)

(*
Wait a second, what are these "forall"s doing in the types of our constructors?!

Well, the *type* of a value built with one of the "option" constructors *depends on*
the type we are parameterizing the "option" over!

As we can see with types of "None" and "Some" above, the constructors of parameterized
inductive types implicitly first take the same arguments as their type's parameters.

But the *type* of values they construct depends on the *value* of the type we are
parameterizing over!

(This is somewhat similar to a generic method in Java or C#, where you would say 
something like Some<T> : T -> Option<T> to indicate that Some is parameterized 
on a type T. The "forall" is just the Coq syntax for the angle brackets.)
*)

Check None bool. (* None bool : option bool *)
Check None nat.  (* None nat  : option nat  *)

Check Some bool true.  (* Some bool true : option bool *)
Check Some nat  (S O). (* Some nat (S O) : option nat  *)

(*
The "forall" type constructor for "dependent products" is actually just a
generalization of the "->" type constructor we have seen for functions and
constructors so far. In fact, "->" in Coq is really just syntactic sugar for
a "forall" where the types are not dependent.
*)

Check Nat.add : forall (n1 : nat), forall (n2 : nat), nat.

(*
Anyways, writing out the type parameter arguments for "None" and "Some" all the
time gets very annoying. If you think about, Coq should almost always be able
to figure out those parameters for us based on context. If we're returning "None"
as the result of a function whose return type is "option nat", the what we
obviously really mean is "None nat". Similarly, if we have an expression like
"Some bool true", the "bool" part in there feels very redundant -- it's the only
possible value for the type parameter given that "true" is the second argument!

We can ask Coq to always try to figure these things out for us using the
"Arguments" command:
*)

Arguments None {T}.
Arguments Some {T} _.

(*
The curly braces indicates which arguments we would like to try and infer
for us. You can read more about how "Arguments" work here:
    https://coq.inria.fr/refman/language/extensions/arguments-command.html

Coq also provides several ways to globally enable type inference 'wherever
possible' documented here:
    https://coq.inria.fr/refman/language/extensions/implicit-arguments.html

Now if we ask Coq what types "None" and "Some" have, it indicates that it no
longer expects us to pass their parameter arguments and will try to infer the
types that start with a "?":
*)

Check None. (* None : option ?T *)
Check Some. (* Some : ?T -> option ?T *)

(*
This means we can write some of the above examples more simply:
*)

Check Some true.  (* Some true : option bool *)
Check Some (S O). (* Some (S O) : option nat  *)

(*
Type inference can make debugging a bit confusing at first, but the added
convenience is well worth the cost in complexity!

Anyways, the whole point of "option" was so that we could write the "pred"
function! When we're encoding partial functions like predecessor, we use
"None" to indicate "no result" and "Some" to indicate "normal result".
*)

Definition pred (n : nat) : option nat :=
  match n with
  | O => None
  | S m => Some m
  end.

Compute pred O.         (* None   *)
Compute pred (S O).     (* Some 0 *)
Compute pred (S (S O)). (* Some 1 *)

(*
Oh and now that we're outside of our Nats module and back to using the
standard library version of natural numbers, we also have nice notation
for writing nats!
*)

Compute pred 0. (* None   *)
Compute pred 1. (* Some 0 *)
Compute pred 2. (* Some 1 *)

(*
In practice, we often use "option" in places where you might throw an exception
in other programming languages.

How many values of type "option" are there? Well, it depends on what type we are
parameterized over.

"option bool" has only three values:

    None
    Some true
    Some false

"option nat" on the other hand has infinitely many values:

    None
    Some O
    Some (S 0)
    Some (S (S O))
    Some (S (S (S O)))
    ...
*)

(*
All the tactics we've seen so far also work for "option" since it's just another
inductive type! Let's do a small proof above "pred" and learn another tactic that's
very handy for dealing with equalities: "congruence".
*)

Lemma pred_None_inv :
  forall n,
    pred n = None ->
    n = 0.
Proof.
  (* We want to prove that, for any nat "n", if "pred n" is "None", then
     it must have been the case that "n" was "0". This flavor of backward reasoning
     is generally known as "inversion". *)

  intros n Heq.
  destruct n as [| m].
  - reflexivity.
  - (* Here our goal is impossible BUT we also have an impossibly hypothesis!

          Heq : pred (S m) = None

      But pred returns Some for any argument that isn't 0!
    *) 
    simpl in Heq.
    (* Now Heq is even more ridiculous:

        Heq : Some m = None

      But all constructors are distinct and injective! Fortunately, the
      "congruence" tactic knows how to exploit this fact and finish our goal.
    *)
    congruence.
Qed.

End Options.

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