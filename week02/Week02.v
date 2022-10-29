(* include libraries and notations *)
Require Import Arith Lia List String.
Import ListNotations.
Open Scope string.

(* enable type inference *)
Set Implicit Arguments.

(*
"eq_dec A" is the type of a function that 'decides equality' over values
of type "A".
*)
Definition eq_dec (A : Type) :=
  forall (x : A),
    forall (y : A),
      {x = y} + {x <> y}.

(*
The type "forall x y, {x = y} + {x <> y}" is a bit fancy. Essentially it says
that for any arguments "x" and "y", the function will either return a proof that
"x = y" OR it will return a proof that "x <> y". This later case is how we write
'"x" does not equal "y"' in Coq, and it expands to "x = y -> False".

For now, you can think of a function whose type is "eq_dec A" roughly as
producing two case: a 'true' case where the arguments are equal and a 'false'
case where they are not equal. In fact, that is exactly how we will use such
functions in Coq code. The only added advantage of doing things this way is that
we will additionally get (dis)equality proofs when we reason by case analysis
about calls to 'eq_dec style' function.
*)

(*
We won't cover this module in lecture, but it contains more details about
deciding equality.
*)
Module DecidingEquality.
  (* Here is a recursive function that returns a boolean indicating whether its
     two nat arguments are equal. *)
  Fixpoint eqb_nat (n1 n2 : nat) : bool :=
    match n1, n2 with
    | 0, 0 => true
    | S m1, S m2 => eqb_nat m1 m2
    | _, _ => false
    end.
  Print eqb_nat.
  (* Notice that this style of pattern matching expands to nested matches. Also,
     note that Coq picked n1 as the structural argument, even though both
     arguments decrease on every recursive call. This is useful to know, so that
     we know what to expect in terms of simplification behavior, and so we know
     what to induct on in proofs about eqb_nat.

     eqb_nat =
       fix eqb_nat (n1 n2 : nat) {struct n1} : bool :=
         match n1 with
         | 0 => match n2 with
       	     | 0 => true
                | S _ => false
                end
         | S m1 => match n2 with
                   | 0 => false
                   | S m2 => eqb_nat m1 m2
                   end
         end
            : nat -> nat -> bool
  *)

  (* Let's prove a few lemmas about eqb_nat. First, it is reflexive, in the
     sense that it returns true if you give it the same value for both
     arguments. *)
  Lemma eqb_nat_reflexive :
    forall n,
      eqb_nat n n = true.
  Proof.
    (* Since eqb_nat is recursive, our proof is inductive. Coq finds it easy. *)
    induction n; simpl; auto.
  Qed.

  (* Second, it is "sound" in the sense that it implies "real" equality. *)
  Lemma eqb_nat_implies_eq :
    forall n1 n2,
      eqb_nat n1 n2 = true ->
      n1 = n2.
  Proof.
    (* Since eqb_nat is structurally recursive on its first argument, we induct
       on n1. Then, since eqb_nat also pattern matches on its second argument,
       we destruct n2. *)
    induction n1; destruct n2; simpl; intros.
    - reflexivity.
    - (* In these middle two cases, we have contradictions in our context like
         "false = true". congruence can dispatch these. *)
      congruence.
    - congruence.
    - (* In the last case, we just use the induction hypothesis. *)
      f_equal. apply IHn1.
      (* assumption is a less powerful auto that just looks to see if the
         goal is exactly one of our hypotheses. Nothing wrong with using auto
         here instead. *)
      assumption.
  Qed.

  (* Finally, if eqb_nat returns false, then its arguments are *not* equal,
     which in Coq is written "<>". *)
  Lemma eqb_nat_false_implies_neq :
    forall n1 n2,
      eqb_nat n1 n2 = false ->
      n1 <> n2.
  Proof.
    (* We could proceed by induction here, but actually this lemma already
       follows from the reflexivity lemma. *)
    intros n1 n2 Heqb.
    intro Heq.
    (* subst gets rid of a variable using an equation in the context. *)
    subst n1.
    rewrite eqb_nat_reflexive in Heqb.
    (* contradiction in our hypotheses: true = false *)
    congruence.
  Qed.

  (* What we've done so far in this module is to first define a function
     returning a boolean, and then separately proved that this boolean had some
     meaning, in this case that the arguments were equal or not.

     The idea with "eq_dec" is to combine these two steps into a single function
     that returns not just a boolean, but a boolean "tagged" with the lemmas
     above to prove that it returned the right answer.

     We can define equality deciders in more than one way, but here is one way
     to do it with tactics! (Yes, you can write "programs" with tactics, too!
  *)

  Definition eq_dec_nat (n1 n2 : nat) : {n1 = n2} + {n1 <> n2}.
    (* We branch on whether eqb_nat returns true or false. "eqn:Heqb" means:
           In each branch, give me an equality remembering where I came from.
       So in the first branch, we will have "eqb_nat n1 n2 = true" as a
       hypothesis, and similarly in the second branch for "false".
    *)
    destruct (eqb_nat n1 n2) eqn:Heqb.
    - (* eqb_nat returned true, so we want to prove n1 = n2. The tactic "left"
         chooses that "branch" of our return type. *)
      left.
      (* Now we use our lemma. *)
      apply eqb_nat_implies_eq.
      (* And we take advantage of the hypothesis we got from "eqn:Heqb". *)
      apply Heqb.
    - (* This case is similar, but for the other branch. *)
      right.
      apply eqb_nat_false_implies_neq.
      apply Heqb.
  (* We use "Defined" instead of "Qed" here. They are the same except that
     "Defined" let's you compute with the definition, where as "Qed" marks it as
     "opaque", meaning it is not available for computation. *)
  Defined.

  Check eq_dec_nat.
  Print eq_dec_nat.

  Compute eq_dec_nat (2 + 2) 4. (* returns left *)
  Compute eq_dec_nat (1 + 1) 1. (* returns right *)

  (* Below, we will use the standard library's equality decider for strings. It
     is defined in a similar way as we did for nats above. *)
End DecidingEquality.

Module Interpreters.

(*
In our programming languages, we'll usually model variables as strings.
This "Notation" command just makes "var" a 'macro' that expands to "string".
*)
Notation var := string.

(*
When we reason about programming languages and programs in them, it will be very
helpful to use decidable equality between variables. Lucky for us the String
library already provides one. Here we just define a synonym for it, which helps
make the code more readable.
*)
Definition var_eq : eq_dec var := string_dec.

(*
When we start to formalize a programming language, we first need to say
what programs even *are* in our language. We do that by specifying the
"abstract syntax" of our language using an inductive type.

Suppose we want to formalize a language of arithmetic expressions with
natural number constants, variables, addition, subtraction, and
multiplication. We might write the grammar for such a language as:

    e ::= n | x | e + e | e - e | e * e

Where "n" is understand to mean any natural number and "x" is understood
to mean any variable. This grammar specifies all the possible syntax trees
for expressions in our language.

Some example concrete expressions in our language and their corresponding
abstract syntax trees:

   Concrete Syntax             Abstract Syntax Tree
    "x + y"                              +
                                        / \
                                       x   y

    "(2 * (x + y)) - 1"                  -
                                        / \
                                       *   1
                                      / \
                                     2   +
                                        / \
                                       x   y

The process of transforming "concrete syntax" (the stuff we type into
our editor) into an "abstract syntax tree" is known as "parsing":
  https://en.wikipedia.org/wiki/Parsing

We won't study parsing in these notes, though it is certainly a rich
and interesting topic! Instead we will use "Notation" commands which
are sort of like fancy macros that will make it 'convenient enough'
to specify the abstract syntax trees we want.

As you may have guessed, we can express our grammar for arithmetic
expressions in Coq using an inductive type. If we used the style of
inductive definitions we've seen so far in class, we might write it as:

        Inductive arith : Set :=
        | Const : nat -> arith
        | Var : var -> arith
        | Plus : arith -> arith -> arith
        | Minus : arith -> arith -> arith
        | Times : arith -> arith -> arith.

That definition totally works, but here's another style of inductive
definition that means exactly the same thing, but also happens to help
Coq pick better names for us when we use tactics like "destruct" or
"induction":
*)
Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

(*
The "arith" type just models the *syntax* of our language. We haven't
said anything about expressions (programs) in our language *mean*.

For example, we prove that "1 + 1" does NOT equal "2"!
*)
Lemma syntax_is_not_semantics :
  Plus (Const 1) (Const 1) <> Const 2.
Proof.
  (* first, let's unfold the definition of 'not' *)
  unfold not.

  (* now we can introduce an equality as a hypothesis *)
  intro Heq.

  (* Uh oh, now our goal is "False"! We all know that its impossible
     to prove "False" in Coq, so what's going on? It turns out that
     you CAN prove "False" if you assume something that is "False".

     Our "Heq" hypothesis is actually IMPOSSIBLE, i.e., "False"!

     It is saying that the *trees*

            +             and           2
           / \
          1   1

     are the *same*. But those are *different* trees!!

     Values built with different constructors are always
     different, so there is no way that anyone could have
     proved Heq. We can "call Coq's bluff" by doing a fancy
     form of case analysis known as "inversion".
  *)
  inversion Heq.
  (*
    In this case, inversion knows that inductive values built
    with different constructors can never be equal. If you'd
    like to understand more about how "inversion" constructs
    such proofs, we have text on this topic in the Coq Fundamentals:
      https://docs.google.com/document/d/1V22TC-vf6b7ciBquR5-IK3wJ1WCPhrBLWIP1Tf18z0Y/edit#bookmark=id.f8q7fn4zzutb
  *)

  (* The "inversion" will be useful later in more complex
     situations, so we introduce it here. But it turns out in
     this case there is another tactic which can also easily
     handle these kinds of contradictions due to equalities
     that claim values built with different constructors
     are equal.
  *)
  Restart.
  congruence.
Qed.

(*
Although we haven't defined the meaning of our arithmetic expressions yet,
we can write recursive functions over their syntax to analyze them. For
example, suppose we wanted to check whether the syntax of a program contains
the constant 0.
*)
Fixpoint has_zero (e : arith) : bool :=
  match e with
  | Const n => Nat.eqb n 0
  | Var x => false
  | Plus e1 e2  => has_zero e1 || has_zero e2
  | Minus e1 e2 => has_zero e1 || has_zero e2
  | Times e1 e2 => has_zero e1 || has_zero e2
  end.

(*
Let's test out our "has_zero" function on a couple of small expressions
to see how it works.
*)

Compute has_zero (Const 0). (* true *)
Compute has_zero (Const 1). (* false *)
Compute has_zero (Plus (Var "x") (Var "y")). (* false *)
Compute has_zero (Minus (Plus (Var "x") (Var "y")) (Const 0)). (* true *)

(*
OK, so that works as expected, but writing out abstract syntax trees
for expressions gets very old very fast. Let's use Coq's "Notation"
and "Coercion" commands to make it a bit easier to write expressions.
*)

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

(*
We use the "%arith" annotation on some Coq code to control how notations
are interpreted. When we have an something like "("x" + "y")%arith",
Coq will use OUR notation for "+" in between the parentheses "( )" rather
than the default (which is addition for natural numbers).
*)

(*
Let's write another 'analysis', in this case one that tests whether an
expression is just a variable minus itself.
*)
Definition is_var_minus_self (e : arith) : bool :=
  match e with
  | Minus (Var x) (Var y) =>
      if var_eq x y
      then true
      else false
  | _ => false
  end.

(*
Though a bit silly, we can prove this analysis 'correct' using a sort of
inversion lemma:
*)
Lemma is_var_minus_self_inv :
  forall e,
    is_var_minus_self e = true ->
    exists x, e = Minus (Var x) (Var x).
Proof.
  intros.
  destruct e; inversion H.
  destruct e1, e2; try congruence.
  destruct (var_eq x x0); subst; try congruence.
  exists x0; auto.
Qed.

(*
In addition to simple 'analyses' like "has_zero" and "is_var_minus_self", we can
also write functions that *transform* arithmetic expressions. For example, we
can replace all instances of a variable minus itself with 0.
*)
Fixpoint xform_var_minus_self_0 (e : arith) : arith :=
  if is_var_minus_self e then
    Const 0
  else
    (* otherwise, just recursively transform *)
    match e with
    | Const _ => e
    | Var   _ => e
    | Plus  e1 e2 => Plus  (xform_var_minus_self_0 e1) (xform_var_minus_self_0 e2)
    | Minus e1 e2 => Minus (xform_var_minus_self_0 e1) (xform_var_minus_self_0 e2)
    | Times e1 e2 => Times (xform_var_minus_self_0 e1) (xform_var_minus_self_0 e2)
    end.

Compute xform_var_minus_self_0 (Minus (Var "x") (Var "x")). (* 0 *)
Compute xform_var_minus_self_0 (Minus (Var "x") (Var "y")). (* x - y *)


(*
Usually, our intention of transformations like "xform_var_minus_self_0" is
that they preserve the *meaning* of an expression (program), that is, both
the original program and its transformed version should have the same
behavior. If we want to prove a transformation correct, we first need to say
what our expressions (programs) mean!

Since our language has variables, we will need to have some model
of 'memory' for looking up the values of variables. We'll use an
"association list" which is just a list of pairs:
  https://en.wikipedia.org/wiki/Association_list

There is more about association lists at the bottom of the Coq code
from last week's materials:
  https://gitlab.cs.washington.edu/cse-505-21sp/cse-505-21sp/-/blob/main/week01/Week01.v#L1400

We'll call the association lists we use to model the memory "valuations".
In our arithmetic expression language, values are just natural numbers,
so our valuation 'map variables to nats':
*)
Definition valuation := list (var * nat).

(*
To retrieve the value of a variable "x" from a valuation, we just scan
through the valuation till we find a pair "(x, n)" and then return
"Some n". If we get to the end of the list and never find such a pair,
then we return "None".
*)
Fixpoint lookup (x : var) (v : valuation) : option nat :=
  match v with
  | [] => None
  | (y, n) :: v' =>
    if var_eq x y
    then Some n
    else lookup x v'
  end.
(*
"Some" and "None" are constructions for the "option" type, which is
basically just an inductive type for lists that are either empty or
have exactly one element. There's some more detail about options from
last week's material's at:
  https://gitlab.cs.washington.edu/cse-505-21sp/cse-505-21sp/-/blob/main/week01/Week01.v#L649
*)

(*
Once we have valuations to model memory for variable lookups, we can
give semantics to our language of arithmetic expression by simply
writing a little recursive interpreter for it:
*)
Fixpoint eval_arith (e : arith) (v : valuation) : nat :=
  match e with
  | Const n =>
    (* constants just evaluate to themselves *)
    n
  | Var x =>
    (* to evaluate a variable expression, we look it up in the valuation *)
    match lookup x v with
    | None =>
      (* if the valuation doesn't have anything for this variable,
         then we'll say it just evaluates to a default value of zero
         (other design choices are definitely possible!) *)
      0
    | Some n =>
      (* otherwise, the variable expression just evaluates to whatever
         the valuation has for this variable *)
      n
    end
  (* all the binary operators follow the same recipe :
        1. recursively evaluate the LHS subexpression to a nat value "n1"
        2. recursively evaluate the RHS subexpression to a nat value "n2"
        3. apply the corresponding nat operator on "n1" and "n2" *)
  | Plus  e1 e2 => eval_arith e1 v + eval_arith e2 v
  | Minus e1 e2 => eval_arith e1 v - eval_arith e2 v
  | Times e1 e2 => eval_arith e1 v * eval_arith e2 v
  end.

(*
Now, it's still the case that the syntax "1 + 1" is different from the
syntax "2", but *evaluating* the syntax "1 + 1" gives the same result
as *evaluating* the syntax "2". We can compute these evaluations in the
empty valuation:
*)
Compute eval_arith (1 + 1)%arith [].  (* 2 *)
Compute eval_arith (2)%arith [].      (* also 2 *)

(*
We can also prove that these expressions evaluate to 2 under *any* valuation.
*)
Lemma eval_one_plus_one_is_eval_two :
  forall v,
    eval_arith (1 + 1)%arith v = eval_arith 2 v.
Proof.
  intros. simpl. reflexivity.
Qed.

(*
Now we can prove that our 'var minus self to zero' transformation
is correct in the sense that it "preserves evaluation":
*)
Lemma xform_var_minus_self_0_correct :
  forall e v,
    eval_arith (xform_var_minus_self_0 e) v = eval_arith e v.
Proof.
  induction e; intros.
  - (* const case *)
    simpl. reflexivity.
  - (* var case *)
    simpl. reflexivity.
  - (* plus case *)
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  - (* minus case -- need to see if expression is "x - x"! *)
    remember (xform_var_minus_self_0 (Minus e1 e2)) as LHS.
    cbn [xform_var_minus_self_0 eval_arith] in HeqLHS.
    remember (is_var_minus_self (Minus e1 e2)) as SameVar.
    destruct SameVar.
    + symmetry in HeqSameVar.
      apply is_var_minus_self_inv in HeqSameVar.
      inversion HeqSameVar; subst. rewrite H.
      simpl. lia.
    + subst.
      simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  - (* times case *)
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.

  (* in practice, would prove more like *)
  Restart.
  induction e; simpl; intros; auto.
  destruct e1, e2; simpl in *; auto.
  destruct (var_eq x x0); subst; simpl; auto.
  lia.
Qed.


(*
Building on expressions, we can formalize a small imperative language with
variable assignment and loops. As always, we start with the syntax:
*)
Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| Repeat (e : arith) (body : cmd).

(*
Moving on to the semantics, to describe the execution of the "Repeat" command,
we will want some way to 'call a function on an argument N times':
*)
Fixpoint do_n_times {A} (f : A -> A) (n : nat) (x : A) : A :=
  match n with
  | O => x
  | S n' => do_n_times f n' (f x)
  end.
(* For example, we could "cons true" onto a list n times: *)
Compute do_n_times (cons true) 7 [false; false]. (* 7 "true"s followed by 2 "false"s *)

(*
Notice that do_n_times takes is structurally recursive on n, the number of times
to call the function.
*)

(*
With "do_n_times" in hand, we can give semantics for our command language with
an interpreter. Unlike expressions, commands do not return values, but instead
return a new valuation.
*)
Fixpoint eval_cmd (c : cmd) (v : valuation) : valuation :=
  match c with
  | Skip => v
  | Assign x e => (x, eval_arith e v) :: v
  | Sequence c1 c2 => eval_cmd c2 (eval_cmd c1 v)
  | Repeat e body => do_n_times (eval_cmd body) (eval_arith e v) v
  end.

(*
It's important to note that the only reason we could give this 'cmd' language a
semantics via an interpreter is because all loops in the 'cmd' ALWAYS terminate
for 'obvious' reasons. Once we get to languages with arbitrary loops, we won't
be able to use interpreters any more -- we won't be able to prove that the
interpreter always terminates and all functions in Coq must always terminate!
*)

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

(* Here's a command to compute the factorial of the "input" variable.
   It returns its answer in the "output" variable. *)
Definition factorial : cmd :=
  "output" <- 1;
  repeat "input" doing
    "output" <- "output" * "input";
    "input" <- "input" - 1
  done.

Theorem factorial_ok :
  forall v input,
    lookup "input" v = Some input ->
    lookup "output" (eval_cmd factorial v) = Some (factorial_tailrec input).
Proof.
  intros v input Hinput.
  simpl.  (* Yikes! That's hard to read. I guess we better think about it... *)
Restart.
  intros v input Hinput.
  (* Let's use the motto. "factorial" is a command that is not a loop.
     Similarly, factorial_tailrec is non-recursive. So the motto tells us the
     proof of this theorem should not be inductive, and we should just unfold
     definitions. *)
  unfold factorial, factorial_tailrec.
  (* The command starts by assigning 1 to "output". This corresponds to
     initializing the accumulator of factorial_tr to 1. Then the command enters
     a loop, which corresponds to the recursive computation of factorial_tr.
     So let's prove a lemma about the loop body and factorial_tr. *)
Abort.

(* First, let's give a name to the body of the loop. *)
Definition factorial_loop_body : cmd :=
  "output" <- "output" * "input";
  "input" <- "input" - 1.

(*
Now let's state a lemma about executing the body n times. After the body
executes n times, what valuation will be returned? It will be the same as the
initial valuation, except that "input" will have been decremented all the way
to 0, and "output" will have the result of `factorial_tr` in it. All other
variables besides these two will be unchanged.

To make statements about all variables ("input", "output", and everything else),
we can use a notion of "valuation equivalence", which we call "map_equiv". Two
valuations are equivalent if looking up all variables return the same answers.
*)

Definition map_equiv m1 m2 := forall v, lookup v m1 = lookup v m2.

(*
Here's a quick example of two equivalent maps. Note that the maps are different
*as lists* but equivalent in terms of lookup. (This is kind of similar to how
"1 + 1" is a different syntax tree than "2", but they have the same meaning.)
*)
Example map_equiv_example :
  forall m,
    map_equiv (("x", 0) :: ("y", 1) :: m) (("y", 1) :: ("x", 0) :: m).
Proof.
  unfold map_equiv.
  intros m z.
  simpl.
  (* Now there a bunch of cases depending on whether the variable is "x" or "y"
     or something else. *)
  destruct (var_eq z "x").
  - destruct (var_eq z "y"); congruence.
  - destruct (var_eq z "y"); congruence.
  Restart.
  (* We can do that much more quickly using the "repeat" tactic combinator. *)
  unfold map_equiv.
  intros m z.
  simpl.
  repeat destruct (var_eq _ _); congruence.
Qed.

Ltac solve_map_cases :=
  unfold map_equiv; intros; simpl;
  repeat destruct (var_eq _ _); try congruence.

(*
Using map_equiv, we can state our characterization of executing the factorial
loop body n times.
*)
Lemma factorial_loop_body_ok :
  forall n acc v,
    lookup "input" v = Some n ->
    lookup "output" v = Some acc ->
    map_equiv
      (do_n_times (eval_cmd factorial_loop_body) n v)
      (("input", 0) :: ("output", factorial_tr n acc) :: v).
(* The output valuation is equivalent to the input valuation but with input
   updated to 0 and output updated to "factorial_tr n acc". *)
Proof.
  (* do_n_times is recursive on n. So is factorial_tr. Let's induct on n. *)
  induction n; intros acc v Hinput Houtput x.
  - simpl. solve_map_cases.
  - (* Unroll the loop and factorial_tr once each. *)
    cbn [do_n_times factorial_tr].
    (* We want to use the induction hypothesis to rewrite. Need to unfold. *)
    unfold map_equiv in *. (* "in *" means "in the goal and all hypotheses" *)
    Fail rewrite IHn. (* "unable to find an instance for the variable acc " *)
    (* Tell Coq what value to use for the accumulator. *)
    rewrite IHn with (acc := S n * acc); solve_map_cases.
    + rewrite Hinput. f_equal. lia.
    + rewrite Hinput, Houtput. f_equal. lia.
Qed.

(* Now we're ready to prove our main theorem about factorial! *)
Theorem factorial_ok :
  forall v input,
    lookup "input" v = Some input ->
    lookup "output" (eval_cmd factorial v) = Some (factorial_tailrec input).
Proof.
  (* We start out like before. *)
  intros v input Hinput.
  unfold factorial, factorial_tailrec.

  (* We want to evaluate the program up to but not including the loop body.
     First, we "fold" the definition of the loop body. ("fold" is the opposite
     of "unfold"; it replaces a definition with its shorter name.) *)
  fold factorial_loop_body.
  (* Next, we use "cbn" to simplify but *without* unfolding the loop body. *)
  cbn -[factorial_loop_body].
  (* There's an occurrence of looking up the "input" variable. *)
  rewrite Hinput.
  (* Now use our lemma about executing the body n times and finish up with map
    reasoning. *)
  rewrite factorial_loop_body_ok with (acc := 1); solve_map_cases.
Qed.

End Interpreters.

Module CurryHoward.

(* We use "->" to build function types. *)

Check (fun (x : nat) => x). (* has type "nat -> nat" *)

Check (fun (x : bool) => x). (* has type "bool -> bool" *)

(*
But what if we want a polymorphic identity function that works for ANY type?
We can use "forall" to write such a function in Coq:
*)

Check (fun (T : Type) => fun (x : T) => x). (* has type "forall T, T -> T" *)

(*
The above (curried) function takes two arguments:
  1. an argument T whose type is Type
  2. an argument x whose type is T

So the *type* of the second argument *depends on* the *value* of the first
argument! That's why we need "forall" to write the type above: when we get
to specifying the *type* of the second argument, we need some way to refer to
the *value* of the first argument:

  "forall T, T -> T"
   --------  ^    ^
      |      |    |
      |      +----+--- Use name "T" bound by the "forall" to 1st arg value
      |
      +---------------- Binds the name "T" to the *value* of the 1st arg

But wait a second... "forall" is another way to write function types?
Don't we use "forall" when we're specifying *theorems*?!

YES.

In Coq, "theorems ARE types" and "proofs ARE programs"!

This design philosophy is known as the "Curry Howard Correspondence":
  https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence

What it really means for us: whenever we prove something via

  Theorem some_fact :
    "SOME CLAIM".
  Proof.
    "BIG SOUP OF TACTICS"
  Qed.

The "SOME CLAIM" part is just a type and the "BIG SOUP OF TACTICS" is
just building a functional program that has that type!

Let's look back at a familiar example: commutativity of "andb".
*)

Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Theorem andb_comm :
  forall b1 b2,
    andb b1 b2 = andb b2 b1.
Proof.
  destruct b1, b2; auto.
Qed.

Print andb_comm.

(*
Check it out, "andb_comm" is just a function!

  andb_comm =
    fun b1 : bool =>
      if b1 as b return (forall b2 : bool, andb b b2 = andb b2 b) then
        fun b2 : bool =>
          if b2 as b return (andb true b = andb b true) then
            eq_refl
          else
            eq_refl
      else
        fun b2 : bool =>
          if b2 as b return (andb false b = andb b false) then
            eq_refl
          else
            eq_refl
  : forall b1 b2 : bool, andb b1 b2 = andb b2 b1

While it's 'just a function', it's a kind of weird and confusing
function -- that's exactly why we use tactics to help us write
"programs" which we really think of as proofs.

OK, so all that may seem a bit weird... what's the intuition?

Well, let's take a step back and think about the type "A -> B" from
both a programming and a proving perspective:

    Programming view of "A -> B":

      The type of a function which, if you give it a value of type "A"
      will give you back a value of type "B". Thus, a function that
      has type "A -> B" shows how to 'transform an "A" value into
      a "B" value'.

    Proving view of "A -> B":

      An implication which says that, if "A" is true, then "B" must
      also be true. A proof of "A -> B" typically begins by 'assuming
      "A"' and then showing how, from that assumption, "B" logically
      follows. Thus, a proof of "A -> B" shows how to 'transform
      evidence for "A" into evidence for "B"'.

See the symmetry? So did the mathematician Haskell Curry and the logician
William Alvin Howard!

So: "forall" is just a generalization of regular function types and
a proof of a "forall" is just a function. That's why "andb_comm" is a
function!

But how is it that tactics end up generating functions? In fact, what
the heck are tactics doing under the hood?

We can dig into that too using the "Show Proof" command:
*)
Theorem andb_comm_in_slow_motion :
  forall b1 b2,
    andb b1 b2 = andb b2 b1.
Proof.
  (* Here at the beginning, our partial proof is just a "hole". *)
  Show Proof.
    (*
        "?Goal"
    *)

  (* As we run tactics we start to 'push' the "hole" down. *)
  intro b1.
  (* That "intro" tactic generates a function in our proof
     whose body becomes the next "hole". *)
  Show Proof.
    (*
      "(fun b1 : bool => ?Goal)"
    *)

  (* If we "intro" again, we'll generate another function
     to replace the current "hole", but the body of THAT
     (inner) function will now be the new "hole". *)
  intro b2.
  Show Proof.
    (*
      "(fun b1 : bool => fun b2 : bool => ?Goal)"
    *)

  (* Now, if we "destruct b1", we'll generate a pattern
     match in our proof.*)
  destruct b1.
  Show Proof.
    (*
      "(fun b1 : bool => fun b2 : bool =>
          match b1 as b return (@eq bool (andb b b2) (andb b2 b)) with
          | true => ?Goal@{b2:=b2}     (* <== first subgoal!  *)
          | false => ?Goal0@{b2:=b2}   (* <== second subgoal! *)
          end)"
    *)

  (* OK, so that's now a bit of a mess -- but that's just because
     of how the definition of equality (which is just another
     inductive type!) works out. We'll talk about equality more
     later, but there's a detailed walk through in the Coq Fundamentals
     doc at:
        https://docs.google.com/document/d/1V22TC-vf6b7ciBquR5-IK3wJ1WCPhrBLWIP1Tf18z0Y/edit#heading=h.g9tzd72axe4p

     The key point: now we have a match with two cases. One case for
     when "b1 is true" and another case for when "b2 is false".
     Each of those cases became new "hole"s in our proof which is
     why we now have two subgoals! *)

  (* We'll continue to follow same 'proof by truth table' strategy
     we've used before, so the next step is to also "destruct b2". *)
  destruct b2.
  Show Proof.
    (*
        "(fun b1 : bool => fun b2 : bool =>
            match b1 as b return (@eq bool (andb b b2) (andb b2 b)) with
            | true =>
                match b2 as b return (@eq bool (andb true b) (andb b true)) with
                | true => ?Goal0   (* <== new nested subgoal!  *)
                | false => ?Goal1  (* <== another new nested subgoal!  *)
                end
            | false => ?Goal0@{b2:=b2}
            end)"
    *)

  (* At this point, we can just evaluate the goal because there
     are no variables left. *)
  simpl.
  (* But notice: calling "simpl" didn't change our partial proof at all! *)
  Show Proof.
    (*
        "(fun b1 : bool => fun b2 : bool =>
            match b1 as b return (@eq bool (andb b b2) (andb b2 b)) with
            | true =>
                match b2 as b return (@eq bool (andb true b) (andb b true)) with
                | true => ?Goal0
                | false => ?Goal1
                end
            | false => ?Goal0@{b2:=b2}
            end)"
    *)

  (* If we use the "reflexivity" tactic to finish this subgoal,
     then we'll see the first case in the nested match gets filled in. *)
  reflexivity.
  Show Proof.
    (*
        "(fun b1 : bool => fun b2 : bool =>
            match b1 as b return (@eq bool (andb b b2) (andb b2 b)) with
            | true =>
                match b2 as b return (@eq bool (andb true b) (andb b true)) with
                | true =>
                    @eq_refl bool true : @eq bool (andb true true) (andb true true)
                    (* ^^^^ this case now complete! *)
                | false => ?Goal1
                end
            | false => ?Goal0@{b2:=b2}
            end)"
    *)

  (* Again, the actual code getting filled in for that case has to
     do with the definition of equality, which we'll cover later. *)

  (* Let's finish the next case with another "simpl" (which won't change
     our partial proof) and a "reflexivity" (which will fill in the second
     case of the nested match). *)
  simpl. reflexivity.
  Show Proof.
    (*
        "(fun b1 : bool => fun b2 : bool =>
            match b1 as b return (@eq bool (andb b b2) (andb b2 b)) with
            | true =>
                match b2 as b return (@eq bool (andb true b) (andb b true)) with
                | true =>
                    @eq_refl bool true : @eq bool (andb true true) (andb true true)
                | false =>
                    @eq_refl bool false : @eq bool (andb true false) (andb false true)
                    (* ^^^^ now this case completed too! *)
                end
            | false => ?Goal0@{b2:=b2}
            end)"
    *)

  (* Now we just need to basically repeat the above process, but
     for the cases where "b1 is false". We won't show each step,
     but instead will run "Show Proof" again once there aren't
     any remaining subgoals. *)
  destruct b2.
  simpl. reflexivity.
  simpl. reflexivity.

  (* The final proof term generated by all our tactics above. *)
  Show Proof.
    (*
        "(fun b1 : bool => fun b2 : bool =>
            match b1 as b return (@eq bool (andb b b2) (andb b2 b)) with
            | true =>
                match b2 as b return (@eq bool (andb true b) (andb b true)) with
                | true =>
                    @eq_refl bool true : @eq bool (andb true true) (andb true true)
                | false =>
                    @eq_refl bool false : @eq bool (andb true false) (andb false true)
                end
            | false =>
                match b2 as b return (@eq bool (andb false b) (andb b false)) with
                | true =>
                    @eq_refl bool false : @eq bool (andb false true) (andb true false)
                | false =>
                    @eq_refl bool false : @eq bool (andb false false) (andb false false)
                end
            end)"
    *)

  (* Since there are no "hole"s left, the proof is complete!
     Running "Qed." type checks the term generated by all our
     tactics. This is a great design choice, because it means
     that tactics can do ANYTHING they want to come up with
     proof -- even if they were buggy, the "Qed." would catch
     any mistakes :) *)
Qed.

(*
OK, so if tactics are just generating programs, then what is
going on with a fancy tactic like "induction"?

Well, we already know one way to figure it out, use "Show Proof"!
*)
Lemma add_n_O :
  forall n,
    Nat.add n 0 = n.
Proof.
  induction n.
  Show Proof.
    (*
      "(fun n : nat =>
          nat_ind (fun n0 : nat => n0 + 0 = n0)
            ?Goal (* <== BASE CASE! *)
            (fun (n0 : nat) (IHn : n0 + 0 = n0) =>
              ?Goal0@{n:=n0}) (* <== INDUCTIVE CASE! *)
            n)"
    *)

  (* Aha! So when we do "induction" the tactic generates a call
     to the induction principle for the relevant type. In this
     situation, we were doing induction on a nat, so we generated
     a call to "nat_ind".

     Let's back out of this proof and look more into that. *)
Abort.

(* What is "nat_ind" anyway? *)
Print nat_ind.

(*
  "nat_ind =
    fun (P : nat -> Prop) (f : P 0) (f0 : forall n : nat, P n -> P (S n)) =>
      fix F (n : nat) : P n :=
          match n as n0 return (P n0) with
          | 0 => f
          | S n0 => f0 n0 (F n0)
          end
     : forall P : nat -> Prop,
         P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n"
*)

(*
Oh! It just seems to be a very confusing function... great :(

OK, but it's really only like 5 lines of code. We could puzzle
through it, but let's try to just rederive it for ourselves
from first principles. How hard could it be?

What does "induction" on natural numbers really do?

Well, for some property "P" over nats, induction takes:
  1) A proof that "P" is true for 0, and
  2) A proof that, if "P" is true for "n", then
     "P" must also be true for "S n".

Given those two pieces, induction gives you back a function
which, for ANY natural number "x" gives you proof that "P"
is true for "x".

So at least we know the types now. "nat_ind" must be a function like:

    "Definition nat_ind
      (P : nat -> Prop)              (* <== for a given property P *)
      (B : P 0)                      (* <== proof of P 0 as base case *)
      (I : forall n, P n -> P (S n)) (* <== proof of inductive case *)
      : forall n, P n                (* <== result type *)
      :=
          (* WHAT TO PUT HERE?? *)"

Well, inspired a bit by the '505 Motto', we should have some idea of how to
finish this function: "nat" is recursive type so we should probably
use recursion somehow to build its induction principle! That means we
need to use "Fixpoint"!
*)
Fixpoint my_nat_ind
  (P : nat -> Prop)              (* <== for a given property P *)
  (B : P 0)                      (* <== proof of P 0 as base case *)
  (I : forall n, P n -> P (S n)) (* <== proof of inductive case *)
  (x : nat)                      (* <== a nat "x" we want a proof of "P x" *)
  : P x                          (* <== result type *)
  :=
    match x with
    | O => B (* if we need to prove P for 0, we already have it! *)
    | S y =>
      let pfY := my_nat_ind P B I y in (* first recursively prove P y *)
      I y pfY (* then use proof of inductive case to get proof for P x! *)
    end.

(*
And that's it! We just *proved* an induction principle for "nat" on our
own from scratch :)
*)

(*
Whew. That was a bit of brain bender. If you are reading offline, this may
be a good time to take a break ;)

Up next, let's start digging into a major mechanism that will come in handy
next week and starts to shed light on the mystery of how equality is defined
as an inductive type in Coq: "inductive propositions".


*)


End CurryHoward.

Module InductiveProp.

(*
Just like we can use Inductive to declare a type of trees for use in
programming, we can also use Inductive to declare a type of "tree shaped
evidence", as a way to define a proposition.
*)

Inductive le (n : nat) : nat -> Prop :=
| le_n : le n n
| le_S : forall m, le n m -> le n (S m).

(* There's a lot going on here. First, what's the type of le? *)
Check le.  (* le : nat -> nat -> Prop *)
(* le is a function that takes two nats and returns a Prop *)

(*
In the declaration of le, why is one nat "before the colon" and one nat "after
the colon"? The short non-answer is that we put n before the colon because n
doesn't change in any of the calls to le. We call things before the colon
"parameters", similar to how you can parameterize a type on another type. On the
other hand, the second nat changes. In the base case the second nat is also n.
But in the second constructor, the second nat is changed from m to S m. We call
things after the colon "indices".
*)

Lemma le_O_n :
  forall n,
    le 0 n.
Proof.
  (* The proof of le 0 n consists of n applications of le_S. Need induction! *)
  (* Only choice for what to induct on is n, which makes sense. *)
  induction n.
  - apply le_n.
  - apply le_S. apply IHn.
Qed.

Lemma le_transitive :
  forall n m k,
    le n m ->
    le m k ->
    le n k.
Proof.
  (* what could we induct on...? *)
  (* by my count, we have 5 choices: n, m, k, and the two le hypotheses *)
  (* I believe all 5 can be made to work, but some are easier than others *)
  (* The easiest way is actually to induct on the last hypothesis. *)
  intros n m k Hnm Hmk.
  induction Hmk.
  - apply Hnm.
  - apply le_S. apply IHHmk.
  Restart.
  (* Here's what happens if you try to induct on the first hypothesis. *)
  intros n m k Hnm Hmk.
  induction Hnm.
  - assumption.
  - apply IHHnm.
    (* need helper lemma about "le (S m) k -> le m k", but it would work out *)
  Restart.
  (* Yet another way, inducting on k. Need lots of inversion. *)
  intros n m k Hnm Hmk.
  revert n m Hnm Hmk.
  induction k; intros n m Hnm Hmk.
  - inversion Hmk. subst. inversion Hnm. apply le_n.
  - inversion Hmk; subst.
    + assumption.
    + apply le_S. apply IHk with (m := m); auto.
Qed.
End InductiveProp.