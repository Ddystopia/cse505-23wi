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
