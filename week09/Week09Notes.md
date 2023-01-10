+++
title = "Week 09 - System F: Polymorphism"
+++

# Week 09 - System F: Polymorphism

_These notes were written by primarily by Prof. James Bornholt for his course at
UT Austin. James is a PhD alum of UW and "friend of the channel", and we thank
him for permission to reuse and adapt these notes back at UW!_

In [Week 08](@/notes/week08/_index.md) we saw how the simply typed lambda calculus,
and type systems in general,
can be powerful tools for guaranteeing safety properties about programs.
Robin Milner tells us that "well typed programs cannot go wrong",
and in the case of the lambda calculus,
that meant that we could *statically* guarantee that a program could evaluate successfully.

While the simply typed lambda calculus is powerful,
its type system—and the generalization of it to a real functional programming language—can often be inconvenient.
Consider this combinator that applies a function to an argument twice:
```
double = λf. λx. f (f x)
```
What type should `double` have?
In some sense, `double` is "generic";
as long as `f` is an abstraction that both takes as input and returns the same type that `x` has,
`double` will be well typed.
But our type systems thus far have had no way to express this idea of being "generic".

In this lecture we'll introduce the idea of *polymorphism*,
a type system feature that allows a single piece of code to be used with multiple types.
We'll see a few ad-hoc examples to build some intuition,
and then introduce a particular polymorphic type system called *System F*
for the lambda calculus.

## Type variables

Let's consider `double` more concretely:
```
double = λf. λx. f (f x)
```
We can copy and paste this definition each time we want to use it with a different type, like this
(imagining that we've extended the simply typed lambda calculus with `Nat`s,
which we didn't cover in [Week 08](@/notes/week08/_index.md) but follows the same idea as with `Bool`):
```
doubleBool = λf:(Bool -> Bool). λx:Bool. f (f x)
doubleNat = λf:(Nat -> Nat). λx:Nat. f (f x)
```
But this is a bit frustrating!
It's also not great as a software engineering practice:
it's just one piece of code,
but repeated multiple times,
which suggests we are missing some kind of abstraction.

One intuitive idea for solving this problem
is to have some notion of a *type variable*.
We could then define `double` like this:
```
double = λf:(T -> T). λx:T. f (f x)
```
But this doesn't quite work either. Consider this code:
```
if (double not true) then (double succ 1) else (double succ 2)
```
Is this expression well typed?
Certainly it appears that way on the surface:
`not` has type `Bool -> Bool` and `true` has type `Bool`,
while `succ` has type `Nat -> Nat` and `1` and `2` have type `Nat`.
But the two uses of `double` *conflict*:
the first one requires that `T` must be `Bool`,
while the second requires that `T` must be `Nat`.

What's missing from our idea of type variables
is some way to *separate* them—to soundly instantiate them multiple times
within the same program.
Now, intuitively, this is not really a difficult idea:
we somehow want "each use" of `T` to be allowed to be different,
and as long as they are "locally" correct
it's fine to give `T` a different value at each position.
But implementing this idea turns out to be extremely challenging.
In fact, people have gotten it wrong:
Java's type system was [recently discovered to be incorrect](https://io.livecode.ch/learn/namin/unsound)
in exactly this way.

As PL people, we know that the answer to getting these sorts of problems right
is to formalize what seems "obvious".
Rather than this hand-waving notion of "type variables",
we need a formal notion of *polymorphism*.

## Varieties of polymorphism

There are actually quite a few different ideas bottled up into the same word "polymorphism":
* The idea we're going to study today is *parametric polymorphism*.
  This allows a single piece of code to have a "generic" type using type variables.
  The key feature of parametric polymorphism is that all instances of the generic piece of code
  have the *same* behavior, regardless of type.
  In the case of `double`, the function always does the same thing,
  it just does it to different types of values.
  You've seen parametric polymorphism before
  as *generic functions* in Java (also ML).
    * In particular, in this lecture we'll see a style of parametric polymorphism
      known as *impredicative* or *first-class* polymorphism.
    * There is also a more limited style of parametric polymorphism
      known as *let-polymorphism* or *ML-style* polymorphism.
      These restrict *where* type variables and generic functions can appear in a term,
      and in return get a simpler and decidable algorithm for type inference.
* Another form of polymorphism is *ad-hoc polymorphism*,
  which allows the same *name* to be used to refer to different functions.
  This *appears* to be polymorphism to the programmer,
  but in reality,
  it's just a dispatch mechanism:
  the types are used to select (either at compile time or run time)
  which of the different functions to invoke.
  An example of ad-hoc polymorphism you've probably seen before 
  is *operator overloading* in C++ or Python:
  the `+` operator, for example, is just one "name",
  but there can be many different implementations of it,
  and the types are used to decide which implementation to execute.
* Object-oriented languages often have a notion of *subtype polymorphism*,
  which allows a single term to masquerade as multiple different types
  that are related by some kind of *subtyping* relation.
  Subtype polymorphism is what allows us to talk about "subclasses" (like `Cat`s)
  and pass them around as if they were their superclass (like `Animal`).

These notions are easy to confuse with each other,
and often we (somewhat inaccurately) say "polymorphism" to mean any or all of these ideas.
For example, Java has always had subtype polymorphism (through classes and inheritance),
and ad-hoc polymorphism (through method overloading),
but did not have parametric polymorphism (generics) at release;
those came later.

In the `double` example above,
what we were really looking for was *parametric* polymorphism—we wanted to be able to use the *same*
`double` code with multiple different (unrelated) types.
So that's what we'll study today.

## System F

System F is a parametrically polymorphic type system for the lambda calculus,
first discovered by Jean-Yves Girard in 1972,
and somewhat contemporaneously by John Reynolds in 1974.
In the same way that the lambda calculus is the essence of computation,
and the simply typed lambda calculus is the essence of type systems,
so to is System F the essence of parametric polymorphism.
It's a convenient vehicle for studying more complex polymorphism,
and also the basis for numerous programming language designs.

The big idea is to *abstract out* the type of a term,
and then *instantiate* the abstract term with concrete type annotations once we have them.
We're going to bake this abstraction and instantiation *into the language itself*—we will be
adding new constructs not just to the type system but to the lambda calculus itself.
We'll do this in three parts:
first, we'll add new polymorphic types to the type system syntax,
then we'll add new polymorphic terms to the lambda calculus syntax and semantics,
and then finally we'll add polymorphic typing rules to the type system semantics.

### Polymorphic types

We can start by defining some new *polymorphic types* in our type system.
We'll keep the same `Bool` and `->` constructors from [Week 08](@/notes/week08/_index.md),
but add two new constructors:
```
T := bool
   | T -> T
   | α
   | ∀α. T
```
Here, `α` is a *type variable*.
The two new constructors give us a way to talk about *generic types*.
For example, here's (almost; see the next section) the type of a generic identity function:
```
∀α. α -> α
```
We can read this as saying that for any type `α`, we can get a function that takes as input
something of type α and returns something of type α.
Similarly, here's (almost) a generic type for our `double` function from before:
```
∀α. (α -> α) -> α -> α
```
For any type `α`, it takes as input a function on `α`s
and a base `α` and returns another `α`.

### Type abstractions and applications

Recall that in the lambda calculus we called functions like `λx. t` *abstractions*.
The idea was that the function *abstracts* a term `t` to work for *any* `x`,
and we can get back the term `t` for a specific `x` by *applying* it.
In parametric polymorphism, we similarly want some idea of *abstracting* out the type of a term,
and *applying* the resulting abstraction to get back the concrete term.
We're therefore going to add *type abstractions* and *type applications* to our lambda calculus.

Let's start with the syntax, which adds two new constructors for lambda calculus terms:
```
t := x
   | λx:T. t
   | t t
   | true
   | false
   | if t then t else t
   | Λα. t
   | t T
```
The first new constructor is the *type abstraction* `Λα. t`.
Type abstractions take as input a *type*
and have a *term* as their body.
The second constructor is *type application* or *type instantiation*,
which *applies* a type abstraction
to get back a concrete term `t` in which
the type variable has been instantiated with the given type `T`.

With this syntax,
we can *actually* write generic functions.
For example, this term is the generic identity function:
```
id = Λα. λx:α. x
```
To *use* this identity function,
we first have to *instantiate* it with a concrete type.
For example, the identity function for `Bool`s is `id Bool`.
The term `id` has type `∀α. α -> α`,
while the term `id Bool` has type `Bool -> Bool`.
Similarly, we can now write the generic `double` function:
```
double = Λα. λf. λx. f (f x)
```
which has type `∀α. (α -> α) -> α -> α`.
As a concrete instantiation,
`double Nat` has type `(Nat -> Nat) -> Nat -> Nat`.

Of course, since we've added new syntax,
we need to add new semantics too.
There is nothing too surprising here:
the rules are the same as for abstractions and applications,
except that the right-hand side `T` of an application can't step
because it needs to be a literal type.
That means that, in some sense, this semantics is automatically "call by value".
$$
\frac{t_1 \rightarrow t_1'}{t_1 \\: T \rightarrow t_1' \\: T} \\: \textrm{STAppLeft}
$$
$$
\frac{}{(\Lambda\alpha. \\: t) \\: T \rightarrow t[\alpha \mapsto T]} \\: \textrm{STApp}
$$

One point to note here is that our substitution notion is slightly different,
and we're being lazy with syntax.
In $\textrm{STApp}$ we're substituting a *type* into a *term*,
which is different to the *term*-into-*term* substitution we've been doing before.
The only place this *type*-into-*term* substitution happens is in the *type annotations* of abstractions:
for an abstraction `λx:α. x`, if `α` is the type variable we are substituting for,
then we need to replace it with the concrete type `T`.

### Polymorphic typing rules

Finally, how do we decide when a term in our new language
has a type in our new type system?
We need to extend our *typing judgment* to include rules for the type abstraction and type application terms.
Here's the judgment for type abstractions:
$$
\frac{\Gamma, \alpha \\: \vdash \\: t \\: : \\:  T}
{\Gamma \vdash \Lambda \alpha. \\: t \\: : \\: \forall \alpha. T}  \\: \textrm{TTAbs}
$$
One little thing to note here is that we need to extend our typing context $\Gamma$
to include the type variable $\alpha$ that is newly in scope.
But unlike the rule for typing regular abstractions,
we don't need to remember anything about $\alpha$,
because type variables are only used in System F for *universal types* `∀α. T`.
In other words, the actual type assigned to $\alpha$ is irrelevant to the typing judgment.
We're remembering $\alpha$ in the context
only to do capture-avoiding substitution
if type variables are reused.

Finally, here's the judgment for type applications:
$$
\frac{\Gamma \\: \vdash \\: t_1 \\: : \\:  \forall \alpha. T_{12}}
{\Gamma \\: \vdash \\: t_1 \\: T_2 \\: : \\: T_{12}[\alpha \mapsto T_2]}  \\: \textrm{TTApp}
$$
Here we have yet another form of substitution in the conclusion!
$T_{12}[\alpha \mapsto T_2]$ is doing *type*-in-*type* substitution:
in the type $T_{12}$, replace any instances of type variable $\alpha$
with the type $T_2$.
Hopefully it now makes sense why we spent so much time talking about substitution in [Week 07](@/notes/week07/_index.md)—it comes up everywhere!

## Programming with System F

As we've hinted at a few times,
System F lets us write truly generic types for some of the functions we've seen before.
For example,
let's validate that `id Bool` has type `Bool -> Bool`,
as we hoped for,
where `id = Λα. λx:α. x`:
$$
\dfrac{
    \dfrac{
        \dfrac{
            \dfrac{ x:\alpha \\, \in \\, \alpha, x:\alpha}
            { \alpha, x:\alpha \\: \vdash \\: x \\: : \\: \alpha} \textrm{TVar}
        }{ \alpha \\: \vdash \\: \lambda x:\alpha. \\: x \\: : \\: \alpha \rightarrow \alpha} \\: { \textrm{TAbs}}
    }{ \vdash \\: \texttt{id} \\: : \\: \forall \alpha. \\: \alpha \rightarrow \alpha} \\: {\textrm{TTAbs}}
}
{ \vdash \\: \texttt{id Bool} \\: : \\: \texttt{Bool} \rightarrow \texttt{Bool}} \\: \textrm{TTApp}
$$
The same proof structure will tell us that `id Nat` will have type `Nat -> Nat`, and so on for any other type.

One thing we can do with our new polymorphism
is give types to the Church encodings we saw before.
The type `CBool` of Church booleans (to distinguish them from the `Bool` we've baked into our calculus)
is `∀α. α -> α -> α`:
A Church boolean takes two arguments of the same type and returns one of them.
As another example,
`CNat` is really just the type
`∀α. (α -> α) -> α -> α`:
a `Nat` in the Church encoding
takes as input a function and a base term,
and returns the same type.
Then, for example,
`1` is the term `Λα. λf:α->α. λx:α. f x`.

A natural question might be:
can we give a type to the Y combinator for general recursion?
Unfortunately, the answer is no:
all well-typed programs in System F terminate.
This property of a type system—that well-typed programs terminate—is called *normalization*.
The proof of this is very difficult—it was one of the major parts of Girard's PhD thesis.

### Properties

As with the simply typed lambda calculus,
we can prove that System F is sound,
in the sense that well-typed programs cannot get stuck.
The proof via syntactic type safety
is very close to the one we saw last lecture:
we prove progress and preservation,
and those compose to give type safety.

## Type erasure

One thing you might find unusual or inelegant about System F
is that it extends the syntax of *the base language* itself.
There are two ways to look at this quirk.
One is that it's not too different to how generics make their way into other languages you've seen:
those show up in the syntax too, when we write things like `LinkedList<T>`.
Under the hood, we have some idea that the compiler or runtime is "instantiating"
these type abstractions with the right concrete types when we try to use them.
This isn't too different to the type abstractions and applications we have in System F.

Another way to look at it is that all these type annotations and abstractions
can be *erased* from the program if we want to—they don't really have any effect
on the behavior of the program;
they exist only to extend the strength of our well-typed guarantees.

The type erasure $\operatorname{erase}(t)$ of a term `t` just replaces any type abstraction `Λα. t`
with its body `t`, and deletes the type annotation `T` from any abstraction `λx:T. t`.
We're left with a lambda calculus term that is functionally equivalent,
which we can capture in an *adequacy* theorem:

**Theorem** (adequacy): $t \rightarrow t'$ if and only if $\operatorname{erase}(t) \rightarrow \operatorname{erase}(t')$.

A natural question to ask about type erasure is:
if we can *delete* the types from a typed term,
is there also a way to *add* the types to an untyped term?
We say that an untyped term $m$ is *typable*
if there exists some well-typed term $t$
such that $\operatorname{erase}(t) = m$.
The question of deciding whether a term is typable
is the *type reconstruction* problem.
We'll study this problem in more detail in a later lecture,
but for now,
the answer for System F is not quite:
type reconstruction for System F is *undecidable*,
although this was an open problem until 1994.
This is the motivation for various restrictions of System F,
such as let polymorphism.

## Parametricity

Finally, let's take a brief look at a surprising and interesting property
of programs that are parametrically polymorphic.

There are many different functions that have type `Bool -> Bool`. Here are a few:
```
λx:Bool. x 
λx:Bool. true
λx:Bool. false
λx:Bool. if x then false else true
...
```
These are (mostly) all *different functions*, in the sense that they evaluate to (two) different values.
More generally, there are many functions of type `Bool -> (Bool -> Bool)`, etc.

By contrast, try to write down a list of all the functions that have type `∀α. α -> α`.
*There is only one*: `Λα. λx:α. x`.
*Every* program of type `∀α. α -> α` must behave *identically* to this one.
This is very surprising!
Informally, it says that
if you give me only a parametrically polymorphic type,
I can tell you quite a bit about the behavior of *any* term of that type.
Intuitively, the idea is that because the term with type `∀α. α -> α`
is polymorphic in `α`,
it can't *do anything interesting* with its argument:
whatever it wants to do
needs to work for *every possible type `α`*,
and the lambda calculus is so simple that the
only such thing it can do is *return the argument*.

This phenomenon is called *parametricity*:
the idea that polymorphic terms behave uniformly on their type variables.
Note that it depends very centrally on how *simple* the lambda calculus is:
language features like reflection break parametricity.

As another example, consider the type `CBool = ∀α. α -> α -> α` we saw before.
There are *only two terms* that have this type (up to $\alpha$-equivalence):
`Λα. λx:α. λy:α. x` and `Λα. λx:α. λy:α. y`.
We can figure this out rather mechanically,
again because any term with this type can't do anything except return one of the two `α`s it has access to:
it has no way to "invent" another `α` because it has no idea what `α` is.
These two terms are exactly the terms `true` and `false`.

