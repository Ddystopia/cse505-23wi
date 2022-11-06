+++
title = "Week 07 - Simply Typed Lambda Calculus (STLC): Type Safety"
+++

# Week 07 - Simply Typed Lambda Calculus (STLC): Type Safety

_These notes were written by primarily by Prof. James Bornholt for his course at
UT Austin. James is a PhD alum of UW and "friend of the channel", and we thank
him for permission to reuse and adapt these notes back at UW!_

At the end of [Week 06](@/notes/week06/_index.md) we tried our hand at "baking in"
booleans into the lambda calculus, to try to ease the pain of writing everything using Church encodings.
This seemed like a natural evolution of the pure calculus,
but in fact created a big problem:
we were able to write well-formed terms that "got stuck",
in the sense that they were not values but could not be reduced further.
For example, this term:
```
true (λx. x)
```
is not a value—it's an application—but cannot step further, as none of the (call-by-value) reduction rules apply.
The same problem would appear if we tried to bake natural numbers into the core calculus;
a term like:
```
7 + (λx. x)
```
is syntactically well-formed but cannot step and is not a value.

You might recognize this sort of problem from your prior programming experience.
It's the sort of thing we'd call a "type error".
Informally, a term like `7 + (λx. x)` is trying to add things "of the wrong type",
and that should be considered an error in the program,
ideally an error we detect at compile time.
In other words, this program should somehow be "invalid".

In this lecture, we'll formalize this idea of only some programs being "valid"
by designing a *type system* for the (extended) lambda calculus.
A type system will assign a *type* to terms in the lambda calculus,
and we'll aim to design our type system to satisfy a simple *safety* property
that [Robin Milner](https://en.wikipedia.org/wiki/Robin_Milner) phrased better than I could:

> Well-typed programs cannot "go wrong".

In other words, if we can assign a type to a lambda calculus term,
that is a guarantee that the term will not get stuck.
Terms like the ones we've written above will be untypable—there will be no type we can assign them.

## Some first attempts at types

Our goal is to write down a type system that prevents programs from getting stuck;
in other words, our type system should ensure programs eventually reduce to a value.
Moreover, we'd like our type system to do this *statically*—it should be able to
rule out stuck programs *without running them*.
One of the key takeaways from the simply typed lambda calculus
is that we can define a type system using the same tools we've been using all semester—we'll
essentially write down a *syntax* of types, and a *semantics* of those types.

Let's start with the syntax of types—what types will our system have?
Roughly speaking, our lambda calculus (extended with booleans) has two kinds of values:
`bool`s (`true` or `false`) and abstractions.
So a first rough attempt at defining the possible types for lambda calculus terms
might just assign every value one of two types:
```
T := bool
   | ->
```
In other words, a type is either `bool` or `->`, with the understanding that we'd use `->` for any
abstraction and `bool` for any boolean. But this analysis is too conservative and not super helpful;
for example, it assigns the same type `->` to the two terms:
```
λx. true
λx. λy. false
```
even though they're clearly quite different—the first takes any input and immediately returns a boolean,
while the second takes any input and returns *another function*. So just by looking at these types,
we can't tell what the result of applying these two functions will be!

To give a useful type to an application, then,
we need some way oto know what type the function being applied returns.
We also need to know that the function will do the right thing with the argument we pass in,
so somehow we also need to talk about the type of the argument.
These requirements hint at a slightly richer type system that is inductive:
```
T := bool
   | T -> T
```
Here, the function type `T -> T` records both the type of the input (before the arrow)
and the type of the result (after the arrow).
The lambda calculus only has single-argument abstractions,
so this is all we need,
but we can compose the `->` constructor to get more complex functions.
For example, `T1 -> (T2 -> T3)` is the type of a function that takes as input a `T1`
and returns *a function* that takes as input a `T2` and returns a `T3`.

That's the syntax of our type system,
so let's turn to the "semantics".
How do we know when a term `t` has a type `T`?
We'll formalize this idea by writing down a *typing relation*
or *typing judgment* that relates terms to their types.
Let's try writing this relation as a binary relation $t : T$,
pronounced "term $t$ has type $T$".
For example, $\texttt{true} : \texttt{bool}$
is (axiomatically) a member of the typing relation.

While this simple relation works for booleans,
we'll run into trouble if we try it for functions.
Here's the problem: consider the term `λx. x`.
What type does this function have?
Intuitively, its type depends on the input we pass it—if the input has type `bool`,
then the output also has type `bool`;
if the input has type `bool -> bool` then so does the output.
Your programmer brain might be shouting "generics!" at this point;
we'll talk in a couple of lectures about how to give this function a generic type.
For now, though, we need to give this function a *concrete* type,
and that concrete type is going to depend on what the type of the input is.

So first, we need to somehow know the type of the argument to a function.
In general, there are two approaches here—either we explicitly annotate the abstraction
with the type of its argument,
or else somehow we analyze the abstraction to deduce what type its input must have.
For now, we'll choose the first approach,
although we'll study the second later in the semester.
We're going to start writing abstractions as `λx:T. t`
where `T` is the *type* of the input.

With this in mind,
our typing process needs to look inside the body `t` of the abstraction,
and give it a type.
But along the way, we need to *remember* the type of the argument we passed in.
So for the term `λx:T. t`,
we roughly want a typing *rule* that looks like this:
$$
\frac{x : T_1 \\: \vdash \\: t \\: : \\:  T_2}{\vdash \lambda x:T_1. t \\: : \\: T_1 \rightarrow T_2}
$$
Here, we've changed the typing relation from a binary $t:T$
to a ternary relation $a \vdash t: T$,
which we read as "under assumption $a$, term $t$ has type $T$".
Let's read this rule in two steps.
Above the line (the premise),
we're saying "assuming that $x$ has type $T_1$, $t$ has type $T_2$".
This is us giving a type to the body of the abstraction,
*under the assumption* that we know the type of the input.
For example, in the term `λx. x` we looked at above,
if we know the type $T_1$ of the input is `bool`,
then we will be able to know that the type $T_2$ of the body is also `bool`.
Given this premise,
the typing rule says we can conclude that (with *no* assumptions)
the term $\lambda x:T_1. t$ has type $T_1 \rightarrow T_2$;
in other words, it's a function that takes as input a $T_1$ and returns a $T_2$.
We don't need any assumptions in this conclusion because the type of $x$ is included in the *syntax* of the abstraction.

## The simply typed lambda calculus

We''ve just about finished defining our type system,
but there's one more thing to notice.
In general, we might need more than one assumption to type a term with nested abstractions.
To keep track of these assumptions, we introduce a *typing context*,
conventionally written $\Gamma$,
that maps variables to their types.
(We have to be careful about capture avoidance again here;
we assume that variables will be renamed as necessary to avoid capturing).
To extend a typing context $\Gamma$ with an additional assumption we use a comma:
$\Gamma, x : T$.

Then the general version of our typing rule for abstractions looks like this:
$$
\frac{\Gamma, x : T_1 \\: \vdash \\: t \\: : \\:  T_2}
{\Gamma \vdash \lambda x:T_1. t \\: : \\: T_1 \rightarrow T_2}  \\: \textrm{TAbs}
$$

With this framework in mind, the typing rules for the other terms in our lambda calculus
are fairly administrative.
To type a variable we just look it up in the current typing context:
$$
\frac{x:T \in \Gamma}
{\Gamma \vdash x : T}  \\: \textrm{TVar}
$$
And to type an application,
we just recurse on both sides:
$$
\frac{\Gamma \vdash t_1 : T_1 \rightarrow T_2 \quad \Gamma \vdash t_2 : T_1}
{\Gamma \vdash t_1 \\: t_2 : T_2}  \\: \textrm{TApp}
$$
Remember that we've added booleans to our calculus now,
so we need typing rules for those too.
The rules for boolean literals are axiomatic:
$$
\frac{}
{\Gamma \vdash \texttt{true} : \texttt{bool}}  \\: \textrm{TTrue}
$$
$$
\frac{}
{\Gamma \vdash \texttt{false} : \texttt{bool}}  \\: \textrm{TFalse}
$$
The rule for `if` is not too surprising—the condition must be a boolean,
and both sides of the branch must have the same type:
$$
\frac{\Gamma \vdash t_1 : \texttt{bool} \quad \Gamma \vdash t_2 : T \quad \Gamma \vdash t_3 : T}
{\Gamma \vdash \texttt{if } t_1 \texttt{ then } t_2 \texttt{ else } t_3 : T}  \\: \textrm{TIf}
$$

### Examples of typed and untypable terms

Let's see this type system in action.
We're able to give the type `bool` to the term `(λx:Bool. x) true`,
which we can see by building the derivation tree:
$$
\frac{
    \frac{
        \frac{\huge  x \\: : \\: \texttt{bool} \\: \in \\:  x \\: : \\: \texttt{bool}}
        {\huge x \\: : \\: \texttt{bool} \\: \vdash \\: x \\: : \\: \texttt{bool}} \\: {\large \textrm{TVar}}
    }
    {\Large \vdash (\lambda x: \texttt{bool}. \\: x) \\: : \\: \texttt{bool} \rightarrow \texttt{bool}} \\: \textrm{TAbs}
    \quad
    \frac{}{\Large \vdash \texttt{true} : \texttt{bool}} \\: \textrm{TTrue}
}
{\vdash (\lambda x: \texttt{bool}. \\: x ) \\: \texttt{true} \\: : \\: \texttt{bool}} \\: \textrm{TApp}
$$
Notice an important property here:
the type of this term is the type of *the value it reduces to*;
it's not "obviously" (syntactically) a boolean, but will eventually become a boolean by evaluation.

But more importantly, the goal we set out for was to be *unable* to give types to terms that are stuck.
For example, the term `true (λx. x)` was stuck.
It's also untypable: by $\textrm{TApp}$, the only way to give this term a type
is for the left-hand side `true` to have an arrow type $T_1 \rightarrow T_2$,
but the only way to give a type to `true` is the rule $\textrm{TTrue}$, which gives `bool`.
Similarly, the term `if (λx. x) then true else false` is stuck,
and is untypable: the rule $\textrm{TIf}$ requires the condition to have type `bool`,
but the only way to give a type to an abstraction is $\textrm{TAbs}$,
which forces an arrow type $T_1 \rightarrow T_2$.

## Type safety

But how do we know we *really* got this type system right—how do we know that any term we can assign a type to cannot get stuck?
We say that a term is *well-typed* if there exists a $T$ such that $\vdash t:T$;
in other words, a term is well-typed if it can be assigned a type in the empty type context.
Then the property we're interested in is that well-typed programs do not get stuck.
This fundamental property of type systems is called *type safety* or *type soundness*.

Surprisingly, while type systems are quite old and well understood,
the ways to prove type safety have evolved over the years.
The way we're going to do it—probably the most common and practical approach today—is a relatively modern approach called *syntactic* type safety,
advanced (separately) by Bob Harper and by Andrew Wright and Matthias Felleisen in the 90s.
We will prove type safety in two steps:
1. **Progress**: A well-typed term is never stuck—either it is a value, or it can take a step.
2. **Preservation**: If a well-typed term can step, the resulting term is also well-typed.

Notice that preservation is quite a weak property.
In the simply typed lambda calculus, a stronger property holds:
stepping preserves not only well-typedness but also the exact type itself.
We will prove the stronger version of preservation,
because it's a little easier (no existential),
but in general the weaker form suffices for type safety.

Let's formalize this a bit more precisely.
First, as always, we'll assume we are discussing only *closed* terms.
Type safety, the idea that well-typed programs never go wrong,
looks like this:

**Theorem** (safety): If $\vdash t: T$ and $t \rightarrow^* t'$ and $t'$ cannot step, then $t'$ is a value and $\vdash t' : T$.

The two lemmas we'll prove look like this:

**Lemma** (progress): If $\vdash t: T$ then either $t$ is a value or there exists a $t'$ such that $t \rightarrow t'$.

**Lemma** (preservation): If $\vdash t: T$ and $t \rightarrow t'$ then $\vdash t' : T$.

It's not too hard to see how these two lemmas combine to prove type safety:
preservation tells us that any $t'$ such that $t \rightarrow^* t'$ will have type $T$,
and progress tells us that when we can no longer step we'll have reached a value.
So all the hard work for proving type safety is in proving these two lemmas.
Let's see how those proofs go.

### Progress

**Lemma** (progress): If $\vdash t: T$ then either $t$ is a value or there exists a $t'$ such that $t \rightarrow t'$.

**Proof**: By induction on the derivation of the typing relation $\vdash t: T$:
* $\textrm{TVar}$: this case is impossible, because we assume closed terms, and closed terms are untypable in the empty context.
* $\textrm{TTrue}$, $\textrm{TFalse}$, $\textrm{TAbs}$: in all these cases, $t$ is a value.
* $\textrm{TIf}$: suppose $t = \texttt{if } t_1 \texttt{ then } t_2 \texttt{ else } t_3$, and that $t$ is well typed.
  Then by $\textrm{TIf}$ we know that $t_1$ has type `bool`.
  By the inductive hypothesis, we know $t_1$ is either a value or can step to some $t_1'$.
  We can consider those two cases separately:
  * If $t_1$ is a value, then it must be either `true` or `false`, because those are the only values of type `bool`
    (this is called a *canonical forms* lemma, and strictly speaking, we need to prove this fact).
    In either case one of the step rules will apply ($\textrm{LIfTrue}$ or $\textrm{LIfFalse}$, respectively),
    and so $t$ can step.
  * If $t_1$ can step to some $t_1'$, then by $\textrm{LIf}$ $t$ can step.
* $\textrm{TApp}$: suppose that $t = t_1 \\: t_2$, with $\vdash t_1 : T_1 \rightarrow T_2$ and $\vdash t_2 : T_1$ by $\textrm{TApp}$.
  By the inductive hypothesis, either $t_1$ is a value or it can step to some $t_1'$,
  and likewise for $t_2$.
  Consider these cases:
  * If $t_1$ can step, then rule $\textrm{LAppLeft}$ applies, so $t$ can step.
  * If $t_1$ is a value and $t_2$ can step, then rule $\textrm{LAppRight}$ applies, so $t$ can step.
  * Otherwise both $t_1$ and $t_2$ are values. Then $t_1$ must have the form $\lambda x: T_1. t_2$,
    since that is the only value that has type $T_1 \rightarrow T_2$ (again by canonical forms),
    and so $t$ can step by beta reduction.

### Preservation

Preservation is a little trickier.
Informally, the trouble is with beta reduction:
we need to prove that the substitution we perform during beta reduction
preserves types.
We call that a *substitution lemma*, and it's helpful to prove it separately:

**Lemma** (substitution): if $\Gamma, x:T' \\: \vdash \\: t \\: : \\: T$ and $\Gamma \\: \vdash \\: t' : T'$, then $\Gamma \\: \vdash \\: t[t'/x] \\: : \\: T$.

**Proof**: By induction on the derivation of $\Gamma, x:T' \\: \vdash \\: t \\: : \\: T$. The proof is a bit fiddly, so I won't write it out here,
but you can see it as lemma 9.3.8 in [*Types and Programming Languages*](https://ebookcentral.proquest.com/lib/washington/reader.action?docID=3338823&ppg=129)
or in [*Software Foundations*](https://softwarefoundations.cis.upenn.edu/plf-current/StlcProp.html#lab236).

The substitution lemma gives us what we need to prove preservation:

**Lemma** (preservation): If $\vdash t: T$ and $t \rightarrow t'$ then $\vdash t' : T$.

**Proof**: By induction on the derivation of $t \rightarrow t'$ (although inducting on the typing judgment works too). Again,
the proof is in the textbook if you want to see it.

## Consequences of the simply typed lambda calculus

We've proved type safety—every well-typed program cannot get stuck.
It's a great win for convenience. We no longer have to use Church encodings for everything;
instead we can "bake in" the important features,
which is all that real (functional) programming languages are doing above the lambda calculus.

However, not all is well in the world.
One problem with our type system is that it *rejects* some programs that don't get stuck.
The first obvious example is the identity function `λx. x`.
In our type system, there's no way to type this function without knowing the type of the input;
that means there's no longer just one identity function
but actually one *for each input type*,
which is less than ideal.
In the next lecture we'll study polymorphism as a solution to this problem.

But even ignoring polymorphism,
there are valid terms we can't give types to.
Consider `if true then (λx. x) else false`.
This term never gets stuck, and evaluates to the value `λx. x`,
but we cannot give it a type in our type system:
the $\textrm{TIf}$ rule requires both sides of the branch to have the same type,
even though we can clearly see that the type of the `else` case "doesn't matter" for this program.

This is a somewhat fundamental trade off of type systems:
in pursuit of ruling out bad programs,
we often unjustly rule out some valid programs too.
This is what makes designing a type system a bit of an art;
we want a system strong enough to reject all the bad programs,
but it also needs to allow us to write lots of valid programs.
In some sense this tension is fundamental:
the untyped lambda calculus was Turing complete,
so if we had managed to write a *complete* type system
(one that assigned a type to *every* term that doesn't get stuck),
we would have solved the halting program.

