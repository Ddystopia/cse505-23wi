(*

  _   _    ___    __  __   _____  __        __   ___    ____    _  __     __
 | | | |  / _ \  |  \/  | | ____| \ \      / /  / _ \  |  _ \  | |/ /    / /_
 | |_| | | | | | | |\/| | |  _|    \ \ /\ / /  | | | | | |_) | | ' /    | '_ \
 |  _  | | |_| | | |  | | | |___    \ V  V /   | |_| | |  _ <  | . \    | (_) |
 |_| |_|  \___/  |_|  |_| |_____|    \_/\_/     \___/  |_| \_\ |_|\_\    \___/


Welcome back! This is our very last homework! It covers System F and is mostly
not in Coq.

There are 12 problems worth a total of 120 core points and
30 challenge points.

*)


Require Import Arith Lia List String.
Require Import ListSet.
Open Scope string.
Import ListNotations.

Set Implicit Arguments.

(*
 * PROBLEM 1 [0 points, ~0 tactics]
 *
 * Fake problem to make Gradescope numbers match problem numbers.
 *)
(* Nothing to do here. *)

(* Generic copied stuff *)
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
(* End of generic copied stuff *)

(*
               ____                  _     _                     _
              / ___|    ___    ___  | |_  (_)   ___    _ __     / |
              \___ \   / _ \  / __| | __| | |  / _ \  | '_ \    | |
               ___) | |  __/ | (__  | |_  | | | (_) | | | | |   | |
              |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |_|

         SECTION 1 : Simply-typed Lambda Calculus with Type Annotations
*)

Module STLC_with_annotations.

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
| Abs : var -> type -> expr -> expr
| App : expr -> expr -> expr.

Declare Scope stlc_scope.
Coercion Var : var >-> expr.
Notation "'\' x ':::' t ',' y" := (Abs x t y) (left associativity, at level 75).
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
  | Abs x t e1 => Abs x t (if var_eq from x then e1 else subst from to e1)
  | App e1 e2 => App (subst from to e1) (subst from to e2)
  | If c Then e1 Else e2 =>
    If (subst from to c) Then (subst from to e1) Else (subst from to e2)
  end.

Inductive value : expr -> Prop :=
| value_abs : forall x t e, value (\x ::: t, e)
| value_T   : value T
| value_F   : value F.
Local Hint Constructors value : core.

Inductive step : expr -> expr -> Prop :=
| step_beta :
  forall x t e v,
    value v ->
    step (App (\x ::: t, e) v) (subst x v e)
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
Local Hint Constructors step : core.

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
                    (G |- \x ::: t1, e : (t1 ==> t2))
where "G |- x : t" := (hasty G x t).
Local Hint Constructors hasty : core.

Fixpoint is_free_var (e : expr) (y : var) : Prop :=
  match e with
  | T | F => False
  | Var x => x = y
  | Abs x t e => x <> y /\ is_free_var e y
  | App e1 e2 => is_free_var e1 y \/ is_free_var e2 y
  | If c Then e1 Else e2 =>
    is_free_var c y \/ is_free_var e1 y \/ is_free_var e2 y
  end.

(* PROBLEM 2 [20 points, ~30 tactics]
 *
 * Prove the following lemma that closed expressions have unique types.
 *
 * Hint: Generalize the lemma so that you can proceed by induction (on what?).
 *)
Lemma type_uniqueness :
  forall e t1 t2,
    [] |- e : t1 ->
    [] |- e : t2 ->
    t1 = t2.
Proof.
  (* YOUR CODE HERE *)
Admitted.

End STLC_with_annotations.

(*
             ____                  _     _                     ____
            / ___|    ___    ___  | |_  (_)   ___    _ __     |___ \
            \___ \   / _ \  / __| | __| | |  / _ \  | '_ \      __) |
             ___) | |  __/ | (__  | |_  | | | (_) | | | | |    / __/
            |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |_____|

                       SECTION 2 : Programming in System F
*)

(* In this section, we will program in System F using the IDE at
   https://courses.cs.washington.edu/courses/cse505/23wi/f/index.html

   When you open that page for the first time, you will see the following code:

   Id = forall A. A -> A;       # type abbreviation
   id = /\A. \x:A. x;           # term abbreviation
   id Id id;                    # evaluating a term to normal form
   test id Id id = id;          # passing test
   test id Id id = \x:bool. x;  # failing test
   id2 : Id = /\A. \x. x;       # another term abbreviation, but with a type
                                # annotation, which allows inference on the RHS
   Nat = forall A. (A -> A) -> A -> A;
   zero : Nat = /\A. \s. \z. z;
   succ : Nat -> Nat = \n. /\A. \s. \z. s (n A s z);
   one = succ zero;
   two = succ one;
   test succ one = two;

   Start by deleting the failing test.
*)

(*
Syntax

The syntax of types and terms is similar to what is used in the slides and in
Week08.v.

Syntax of types
  - built-in boolean type is written "bool"
  - function types are written with "->", as in "bool -> bool"
  - type variables *must* be capitalized, as in "A"
  - polymorphic types are written with "forall", as in "forall A. A -> A"

Again, type variables must be capitalized.

The editor also supports a shorthand for types that quantify over multiple type
variables: "forall A B. A -> B" expands to "forall A. forall B. A -> B".

You can declare type abbreviations to avoid having to write out long types over
and over. The starter code above defines type abbreviations "Id" and "Nat". Note
that the name of a type abbreviation also must be capitalized.

Syntax of expressions
  - built-in boolean constants "true" and "false"
  - conditional expression "if ... then ... else ..."
  - lambda functions are written with "\" as in "\x:bool. x"
  - function application is written with a space between the function and
    argument, as in "(\x:bool. x) true"
  - big lambdas (bambdas) are written "/\", as in "/\A. \x:A. x".
  - type application is also written with a space, as in "id Id"

Term variables like "x" must be lowercase to distinguish them from type
variables.

You can declare term abbreviations to avoid having to write out long terms over
and over. The starter code above defines term abbreviations such as
"id = /\A. \x:A. x".  and "id2 : Id = /\A. \x. x".

Syntax of statements
  - all statements must end with a semicolon ";"
  - type abbreviation, as in "Id = forall A. A -> A;"
  - term abbreviation, as in "id = /\A. \x:A. x;" or with a type annotation, as
    in "id2 : Id = /\A. \x. x;"
  - normalize an expression by just writing the expression followed by a ";", as
    in "id Id id;"
  - a test statement starts with the keyword "test" and then takes two
    expressions, separated by an "=", and checks that they evaluate to the same
    thing, as in "test id Id id = id;"

In a term abbreviation, if you give a type annotation on the LHS of the "=", it
often allows you to leave off type annotations on lambdas on the RHS.
*)

(*

The following problems as you to write several programs in System F. We
recommend working in the editor and then copy-pasting your final code into this
file to turn it in.

*)

(* PROBLEM 3 [30 points, ~20 LOC]
 *
 * Programming with typed Church numerals
 *
 * a. Define "add" that takes two "Nat"s and computes their sum. Write at least
 *    one "test" to demonstrate that "add" works as intended.
 *
 * b. Define "mul" that takes two "Nat"s and computes their product. Write at
 *    least one "test" for "mul".
 *
 * c. Define "exp" that takes two "Nat"s base and exp and computes base to the
 *    power of exp. For instance, "exp two three" should give back "eight".
 *    Write at least one "test" for "exp".
 *
 * Hint: Some of these were done in class on Thursday. Others can be found in
 * the slides.
 *)
(*
# Paste your code here
*)

(* PROBLEM 4 [30 points, ~15 LOC]
 *
 * Pairs
 *
 * a. Copy this definition of pairs into your file:
 *
 *        Pair A B = forall C. (A -> B -> C) -> C;
 *
 * b. Define "mkpair" with type "forall A B. A -> B -> Pair A B".
 *
 * c. Define "fst" to project out the first element of a pair. It should have
 *    type "forall A. forall B. Pair A B -> A".
 *
 * d. Define "snd" to project out the second element of a pair. It should have
 *    type "forall A. forall B. Pair A B -> B".
 *
 * e. Define an abbreviation with a name of your choice that stores a pair of
 *    two numbers of your choice. Use this abbreviation to write testsf for
 *    "fst" and "snd".
 *
 *    Hint: Your abbreviation should have type "Pair Nat Nat".
 *)
(*
# Paste your code here
*)

(* PROBLEM 5 [15 points, ~10 LOC]
 *
 * a. Define a function "pred" that takes a "Nat" x and computes the predecessor
 *    of x. Note that "pred zero" should be "zero" by definition. Write a test
 *    to show "pred" is working.
 *
 *    Hint: Use the same "pair trick" we used in UTLC. See slide 55 from Week 8.
 *
 *    Hint: The type "Pair Nat Nat" will be useful.
 *)
(*
# Paste your code here
*)

(* CHALLENGE 6 [10 points, ~35 LOC]
 *
 * Unlike UTLC, we cannot define arbitrary recursive functions in System F.
 * However, we can still write structurally recursive functions over Nats by
 * calling them. "Nat" is encoded such that function "s" is applied to "z" some
 * number of times, which behaves like a loop that executes the "body" n times.
 *
 * By default, calling a "Nat" gives you access to the "recursive call" as the
 * argument to "s", but it doesn't give "s" access to the Nat itself. We can use
 * the pair trick to keep track of the Nat, though.
 *
 * b. Define a function "natrec" that takes four arguments:
 *      - a type "A"
 *      - a function "f" of type "Nat -> A -> A",
 *      - a base case "x", and
 *      - a "Nat" "n"
 *    and computes the result of applying "f" to "x" "n" times, but where each
 *    call to "f" also gets "the current number" as its first argument.
 *
 *    For instance, "natrec f x 3" computes "f 2 (f 1 (f 0 x))".
 *
 *    Ensure the following test passes:
 *
 *        # you may need to define "three = succ two;" if you haven't already
 *        test natrec Nat (\x. \rec. mul (succ x) rec) one three = six;
 *
 *    Hint: Use the pair trick and keep track of the "current number" as well as
 *    the "recursive result".
 *
 * c. Use "natrec" to define a function "factorial" that takes a "Nat" "n" and
 *    computes the factorial of "n". (factorial of x is 1 * 2 * ... * x).
 *    Use "test" to show "factorial" works as intended.
 *
 * d. Define "natcase" to implement "pattern matching" on "Nat" without access
 *    to a recursive answer. (Similar to Definition vs Fixpoint in Coq.)
 *
 *    Ensure the following tests pass:
 *
 *        is_zero : Nat -> bool = natcase bool (\_. false) true;
 *        test is_zero zero = true;
 *        test is_zero one = false;
 *        pred_again : Nat -> Nat = natcase Nat (\p. p) zero;
 *        test pred_again zero = zero;
 *        test pred_again one = zero;
 *        test pred_again two = one;
 *
 *    Hint: use "natrec" and ignore the recursive answer
 *
 * e. Write a function "le" that takes two "Nat"s x and y and returns a boolean
 *    indicating whether x <= y.
 *
 *    Ensure at least the following tests pass:
 *
 *        test le zero one = true;
 *        test le one zero = false;
 *
 *    Hint: There are several ways to implement it. One approach is to do
 *    structural recursion on x (i.e. call x as a function), and in the
 *    recursive case, do pattern matching on y (i.e. use "natcase").
 *)
(*
# Paste your code here
*)

(* CHALLENGE 7 [10 points, ~35 LOC]
 *
 * Church lists
 *
 * We can encode lists whose elements have type "A" using the type
 *
 *     List A = forall B. (A -> B -> B) -> B -> B
 *
 * Why does this type represent lists? It is similar to how we represented
 * "Nat" as a function that applied "s" n times to "z". A list is represented
 * by calling "c" (for "cons") with each element of the list as its first
 * argument and the recursive answer as its second argument, with the base case
 * "n" (for "nil").
 *
 * For example, the list [1; 2; 3] would be represented by
 *
 *     /\B. \c. \n.
 *       c 1 (c 2 (c 3 n))
 *
 * (Of course, we also need to encode the numbers.)
 *
 * Here are a few helper functions you can copy-paste into your solution.
 *
 *     # analogous to zero for Nat
 *     nil : forall A. List A =
 *       /\A B. \c n. n;
 *
 *     # analogous to succ for Nat
 *     cons : forall A.
 *         A ->  # the element to put on the front
 *         List A ->  # the rest of the list
 *         List A =
 *       /\A. \a l. /\B. \c n.
 *         c a (l B c n);
 *
 *     # length is a structurally recursive function on lists, which means it
 *     # *calls the list* to do the recursion, just like with Nats.
 *     length : forall A. List A -> Nat =
 *       /\A. \l.
 *         l Nat (\_. succ) zero;
 *
 *     # some basic tests for length/cons/nil
 *     test length Nat (nil Nat) = zero;
 *     test length Nat (cons Nat zero (nil Nat)) = one;
 *     test length Nat (cons Nat zero (cons Nat one (nil Nat))) = two;
 *
 * In the problems below, we focus specifically on lists of "Nat", so we often
 * use the type "List Nat".
 *
 * a. Implement a function "seq" that takes a "Nat" "n" and computes a list
 *    of "Nat" "[zero; one; ...; n - 1]". Ensure that at least the following
 *    test passes:
 *
 *    # you may need to define "three = succ two;" if you haven't already
 *    test seq three = cons Nat zero (cons Nat one (cons Nat two (nil Nat)));
 *
 *    Hint: This one is a bit tricky. The easiest way is probably to use a
 *    modified pair trick that counts down instead of up.
 *
 * b. Implement a function "insert" that inserts a "Nat" into a "List Nat" such
 *    that if the second argument is sorted (in ascending order), then the
 *    resulting "List Nat" is also sorted in ascending order. Here is a test:
 *
 *    test insert one (cons Nat zero (cons Nat two (nil Nat))) = seq three;
 *
 * c. Use "insert" to implement "insertion_sort" that takes a "List Nat" and
 *    returns a sorted (in ascending order) "List Nat". Here is a test:
 *
 *    one_zero_two = cons Nat one (cons Nat zero (cons Nat two (nil Nat)));
 *    test insertion_sort one_zero_two = seq three;
 *)
(*
# Paste your code here
*)

(* CHALLENGE 8 [5 points, ~15 LOC]
 *
 * a. Implement "append" that takes two "List A" and returns a "List A" which
 *    connects the second argument to the back of the first one.
 *
 *    Hint: Proceed by structural recursion on the first argument (i.e., call it
 *    as a function).
 *
 * b. Use "append" to implement "reverse" that reverses a "List A". Here is a
 *    test:
 *
 *        test reverse Nat (reverse Nat (seq four)) = seq four;
 *
 *    Hint: Proceed by structural recursion.
 *)
(*
# Paste your code here
*)

(*
             ____                  _     _                     _____
            / ___|    ___    ___  | |_  (_)   ___    _ __     |___ /
            \___ \   / _ \  / __| | __| | |  / _ \  | '_ \      |_ \
             ___) | |  __/ | (__  | |_  | | | (_) | | | | |    ___) |
            |____/   \___|  \___|  \__| |_|  \___/  |_| |_|   |____/

                       SECTION 3 : Metatheory of System F
*)

(* PROBLEM 9 [10 points, ~20 LOC]
 *
 * Prove that
 *
 *     fst t1 t2 (mkpair t1 t2 v1 v2) -->* v1
 *
 * Hint: The definitions of fst and mkpair are on slide 55 of the Week 8 slides.
 *
 * Hint: Treat the definitions of fst and mkpair as "abbreviations", which you
 * expand to their right-hand sides before starting to step.
 *)
(* YOUR ASCII PROOF HERE *)

(*
            ____                  _     _                     _  _
           / ___|    ___    ___  | |_  (_)   ___    _ __     | || |
           \___ \   / _ \  / __| | __| | |  / _ \  | '_ \    | || |_
            ___) | |  __/ | (__  | |_  | | | (_) | | | | |   |__   _|
           |____/   \___|  \___|  \__| |_|  \___/  |_| |_|      |_|

                            SECTION 4 : Parametricity
*)

(* PROBLEM 10 [10 points, ~20 LOC]
 *
 * How many closed values of type
 *     forall A. A -> A -> Pair A A
 * are there (up to equivalence)?
 *
 * Justify your answer briefly and informally using your intuition about
 * parametricity.
 *
 *)
(* YOUR ANSWER HERE *)

(* CHALLENGE 11 [5 points, ~25 LOC]
 *
 * Suppose
 *     p : forall A. forall B. A -> B -> Pair A B
 * and
 *     f : forall A. forall B. Pair A B -> A
 * are *arbitrary* closed values with those respective types.
 *
 * Use your intuition about parametricity to informally argue that for all types
 * t1 and t2, and all values v1 and v2,
 *     f t1 t2 (p t1 t2 v1 v2) -->* v1
 *
 *)
(* YOUR ANSWER HERE *)

(* Feedback question *)
(*
 * PROBLEM 12 [5 points, ~3 sentences]
 *
 * Please take a moment to let us know how the homework went for you by
 * answering the following three questions:
 *    1. How long did the homework take you?
 *    2. Which parts were most interesting or helpful for you?
 *    3. Which parts were especially frustrating, confusing, or tedious?
 *       What should we do better next time?
 *
 * It's fine if your answers are short if you don't have much to say!
 *)

(* Your feedback here! *)


(*
 * This is the end of Homework 6.
 *
 * To submit your homework, please follow the instructions at the end of the
 * README.md file in this directory.
 *
 * Please also see the README.md file to read about how we will grade this
 * homework assignment.
 *)
