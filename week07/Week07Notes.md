+++
title = "Week 07 - Lambda Calculus: Scope, Church Encodings"
+++

# Week 07 - Lambda Calculus: Scope, Church Encodings

_These notes were written primarily by Prof. James Bornholt for his course at
UT Austin. James is a PhD alum of UW and "friend of the channel", and we thank
him for permission to reuse and adapt these notes back at UW!_

For the last few lectures, we've been studing the semantics of IMP,
a fairly simple imperative language we created because it roughly emulated what we think a "normal"
language looks like—it has arithmetic, conditionals and loops baked in.
We claimed (but did not prove) that IMP is Turing complete,
which gave us some more confidence that it was a "real" language.
But it wasn't the most convenient language to study;
it led to relatively complex semantics
like two small- and big- step rules for `if` and `while`
or the confusing "backwards" assignment rule for Hoare logic.

Was all of this complexity really necessary?
As "PL people" we're often in search of minimalism,
and so we should ask if there is a simpler way to get "real" computation.
One potential answer,
which comes to us from Alonzo Church in the 1920s,
via John McCarthy in the 1950s and Peter Landin in the 1960s,
is the *lambda calculus*.
As the name suggests, it's a core *calculus* for computation.
It's dead simple—just three syntactic forms
and three small-step rules or two big-step rules.
And yet despite this simplicity,
the lambda calculus is Turing complete!

In this lecture we'll study the *untyped* (or "pure") lambda calculus.
We have two motivations here.
First, the lambda calculus distills the essence of programming,
and in particular of *functional* programming,
which we've seen a lot of this semester through Coq and Racket.
Second, the untyped lambda calculus prepares us (as the name suggests)
to study *typed* lambda calculi,
which will be our vehicle for studying type systems for the remainder of this semester.

## Untyped lambda calculus

Just like any programming language we define in this class,
we need to define two things about the lambda calculus:
its *syntax* and its *semantics*.

The syntax is simple enough: a term `t` in the lambda calculus is one of just three forms:
```
t := x
   | λx. t
   | t t
```

Here, `x` is a *variable*, which for our purposes we can just consider to be a string
(like the `var` constructor we've had in our expression languages before).
`λx. t` is an *anonymous function* that takes as input one argument and, when called,
replaces `x` in `t` with that argument.
We sometimes call these anonymous functions *(lambda) abstractions*.
(Aside: now you know why languages like Python, Java, and Racket call anonymous functions "lambdas",
lest you thought this class was too abstract).
Finally, `t t` is a function call,
where the first term is an abstraction and the second is the argument.
We'll mostly call these *applications* instead of calls.

### Small-step semantics and subtleties

The syntax of the untyped lambda calculus is simple,
and the description of it is almost enough to just write down the small-step semantics directly.
As always, let's go one constructor at a time, but—spoiler alert—only one case is interesting.

The *variable* constructor `x` can't step at all.

The *abstraction* constructor `λx. t` *also* can't step. We just say it's a *function* or *abstraction*.

We say that these constructors that can't step are *values*; the final result of evaluating a term in the lambda calculus.

The *only* way to step a lambda calculus term is via application.
Let's think about how we want this to work.
Given a term `t1 t2`, if `t1` is an abstraction `λx. t`,
we step it by "doing the call";
roughly, we want the call to return `t` but after replacing all occurrences of `x` in `t` with `t2`.
You might remember from [Week 06](@/notes/week06/_index.md) that we have a syntax for this "substitution",
and we can use that to just write down the rule directly:
$$
\frac{}{(\lambda x. \\: t) \\; t_2 \rightarrow t[t_2/x]} \\: \beta\textrm{-reduction}
$$
This rule, which does the substitution we just discussed, is called *β-reduction*.
β-reduction is the *workhorse* of the lambda calculus,
and really of all functional languages.
It also gives rise to a notion of *equivalence* between lambda-calculus terms called *β-equivalence*:
we say that terms $(\lambda x. \\: t) \\; t_2$ and $t[t_2/x]$ are β-equivalent.

Unfortunately, this β-reduction rule is deceptively complex.
It's hiding two important subtleties that we'll need to think about
in order to finish defining our semantics:

1. The rule is non-deterministic—does the order in which we apply it to terms matter?
2. Substitution is tricky in the presence of abstractions, and our notion from previous lectures doesn't quite work.

Let's tackle each of these in turn.

### Evaluation strategies

The β-reduction rule is non-deterministic.
To see why, let's look at a term.
First, let's define a little short-hand:
we'll write `id` for the abstraction $\lambda x. \\; x$
(i.e., the *identity* function).
Now consider this term:
$$
\texttt{id} \\: (\texttt{id} \\: (\lambda z. \\: \texttt{id} \\: z))
$$

Here are two different ways we could reduce this term by repeated application of the β-reduction rule,
where in each step I've underlined the term to which we're about to apply the rule:
$$
\begin{align}
&\texttt{id} \\: \underline{(\texttt{id} \\: (\lambda z. \\: \texttt{id} \\: z))} \\\\
&\rightarrow \texttt{id} \\: \underline{(\lambda z. \\: \texttt{id} \\: z)} \\\\
&\rightarrow \lambda z. \\: \texttt{id} \\: z
\end{align}
$$

$$
\begin{align}
&\underline{\texttt{id} \\: (\texttt{id} \\: (\lambda z. \\: \texttt{id} \\: z))} \\\\
&\rightarrow \underline{\texttt{id} \\: (\lambda z. \\: \texttt{id} \\: z)} \\\\
&\rightarrow \lambda z. \\: \texttt{id} \\: z
\end{align}
$$

These two strategies are different—we call them *call by value* and *call by name*, respectively.
Call by value only applies the β-reduction rule once the right-hand side has reduces to a value
(in other words, once it can not step any further).
This means that we have to reduce the inner terms before we can reduce the outermost application.
In contrast, call by name applies β-reduction *as soon as possible*.
For this example, that means reducing the outermost applications first.
In both strategies, we stop reducing as soon as the outermost term is a value (an abstraction or variable); we do not allow reductions *inside* top-level abstractions.

Notice that both cases result in the same final term,
even though the evaluation order is different.
This isn't a coincidence:
the untyped lambda calculus enjoys a property called *confluence*
(sometimes also called the *Church–Rosser theorem*),
which says that the order of applications of β-reduction does not affect the final result.
More formally, if $t \rightarrow^* t_a$ and $t \rightarrow^* t_b$,
then there exists a $t'$ such that $t_a \rightarrow^* t'$ and $t_b \rightarrow^* t'$.

Most programming languages use a call-by-value strategy for function application,
but there are a few exceptions.
Haskell uses a variant of call-by-name,
which is what gives Haskell its laziness property:
arguments to functions are only evaluated if they are actually needed during function evaluation,
rather than being eagerly evaluated.

We'll stick to call-by-value for our lambda calculus, though,
which means that our actual small-step rules will look like this:
$$
\frac{}{(\lambda x. \\: t) \\; v \rightarrow t[v/x]} \\: \beta\textrm{-reduction-CBV}
$$
$$
\frac{t_1 \rightarrow t_1'}{t_1 \\: t_2 \rightarrow t_1' \\: t_2}
$$
$$
\frac{t_2 \rightarrow t_2'}{v \\: t_2 \rightarrow v \\: t_2'}
$$
Here, we write $v$ for a value (an abstraction)
that cannot be reduced any further.
Restricting the β-reduction rule to only apply when the right-hand side is a value
is what gives us the call-by-value semantics;
the other rules just let us reduce the terms in an application to values to enable β-reduction.

### Substitution and scope

The second problem with our semantics is the substitution part of the β-reduction rule.
Informally, we said that $t[v/x]$ means "$t$ but with all occurrences of $x$ replaced by $v$".
That was mostly fine when we studied Hoare logic, but it's problematic here.
Consider reducing this term, where $v$ is some arbitrary *value*:
$$
(\lambda x. \\: \lambda x. \\: x) \\: v
$$
According to the β-reduction rule, this should reduce to:
$$
(\lambda x. \\: x)[v/x] = \lambda x. \\: v
$$
But this is not quite right,
because we've confused two *different* $x$s here (from the outer and inner abstractions).
Watch what happens if we use a different variable name for the outer abstraction:
$$
(\lambda z. \\: \lambda x. \\: x) \\: v \rightarrow (\lambda x. \\: x)[v/z] = \lambda x. \\: x
$$
Now we have two different results depending upon our choice of variable names—the first version
takes any input and always returns $v$, while the second is the identity function.
That's not great.

What we are tripping over here is the notion of the *scope* of a variable.
We say that a variable $x$ is *bound* when it occurs in the body $t$ of the term $\lambda x. \\: t$,
and we sometimes call $\lambda x$ a *binder* whose scope is $t$.
Conversely, we say that a variable $x$ is *free* is it appears in a position where is is not bound by any enclosing abstractions.

Now we have the words for what went wrong in our substitution:
in the body of the inner abstraction,
$x$ is *bound*, and so it's not correct to replace it during substitution.
In other words, the substitution $t[v/x]$ should only replace all *free* occurrences of $x$ in the body $t$.
Formally, we can define it like this, with a case for each term constructor:
$$
\begin{align}
x[t/y] &= \begin{cases} t & \textrm{if } x = y, \\\\
                        x & \textrm{otherwise}
          \end{cases} \\\\
(\lambda x. \\: t')[t/y] &= \begin{cases} \lambda x. \\: t' & \textrm{if } x = y, \\\\
                                          \lambda x. \\: t'[t/y] & \textrm{otherwise}
                            \end{cases} \\\\
(t_1 \\: t_2)[t/y] &= t_1[t/y] \\: t_2[t/y]
\end{align}
$$
Now, when we go to reduce the example above, we get the right result,
because the first case of the abstraction rule prevents us looking inside the body of the inner abstraction.

#### Capture-avoiding substitution

This new definition *almost* works, and will be the definition we'll use in this class.
However, there's still one problem. Consider this term:
$$
(\lambda x. \\: \lambda y. \\: x) \\: y
$$
To reduce this term, we compute:
$$
(\lambda y. \\: x)[y/x] = \lambda y. \\: y
$$
But again, watch what happens if we change a binder, in this case the inner one:
$$
(\lambda x. \\: \lambda z. \\: x) \\: y \rightarrow (\lambda z. \\: x)[y/x] = \lambda z. \\: y
$$
These two results aren't the same! Here, our new substitution rule didn't quite save us,
because the problem was not that $x$ collided with a bound variable
but instead that $y$ was *free* in the original term.
In the first substitution, we say that we have unintentionally *captured* the variable $y$.

What we need here is a notion of *capture-avoiding substitution*.
In essence, we want to be able to somehow *rename* binders (in this case, $\lambda y$) to avoid captures.
Renaming binders is OK because the lambda calculus enjoys another Greek-letter-named property
called *α-equivalence*.
This is just the fancy PL way of saying that $\lambda x. \\: x$ and $\lambda y. \\: y$ are equivalent terms;
in other words, bound variable names do not matter in the lambda calculus.

It turns out that, while capture-avoiding substitution is pretty easy to write down on paper
(see, for example, [these lecture notes from Cornell](https://www.cs.cornell.edu/courses/cs4110/2021fa/lectures/lecture14.pdf)),
it is *surprisingly difficult* to mechanize in a proof assistant like Coq.
Getting this encoding right is still an active research area.
Instead of dealing with that mess,
in this class we'll work around the problem a different way.
Variable capture is only an issue when reducing what we call *open terms*,
which are terms that contain free variables;
a term that contains no free variables is a *closed term*.
In the example above, $y$ was a free variable in the term $(\lambda x. \\: \lambda y. \\: x) \\: y$,
and so the term was open.
We will restrict ourselves to considering only closed terms,
which avoids the issue entirely,
and is still sufficient to see everything we want to see about the lambda calculus.

Restricting to closed terms has another advantage:
it simplifies our notion of "values" to be *only* abstractions,
rather than abstractions *and* variables.

## Programming in the untyped lambda calculus

The lambda calculus is Turing complete,
a fact originally proved by Turing himself in the 1930s.
That's pretty surprising—all we have are functions and function applications!
Rather than try to prove it ourselves,
which would involve the somewhat tedious act of building a Turing machine in the lambda calculus,
let's handwave it a bit by adding some "real" programming language features to the lambda calculus.
We'll add three things:
booleans and conditionals;
natural numbers;
and recursion.
Together these should get us close enough to declare the lambda calculus a real language.

Before we start, I want to point to a super useful tool called [λab](https://capra.cs.cornell.edu/lambdalab/)
for interactively playing with terms in the untyped lambda calculus.
It's way nicer than manipulating these terms on paper, which quickly gets out of hand.

### Booleans and conditionals

First, we'll define values `true` and `false` as terms:
```
true  := λt. λf. t
false := λt. λf. f
```
In other words, `true` is effectively a two-argument function that returns its first argument,
and `false` a two-argument function that returns its second argument.
Here, we're just giving *names* to otherwise-anonymous lambda terms.

The obvious question at this point is: *why these definitions?*.
To start to see it,
let's implement some boolean logic:
```
not := λb. b false true
```
Let's see this definition in action; again, I'm underlining the terms we reduce at each step under the call-by-value strategy:
$$
\begin{align}
\texttt{not true} &= \underline{(\lambda b. \\: b \\:\\: \texttt{false} \\:\\: \texttt{true}) \\:\\: \texttt{true}} \\\\
&\rightarrow \texttt{true} \\:\\: \texttt{false} \\:\\: \texttt{true} \\\\
&= \texttt{true} \\:\\: \underline{(\lambda t. \\: \lambda f. \\: f) \\:\\: (\lambda t. \\: \lambda f. \\: t)} \\\\
&\rightarrow \texttt{true} \\:\\: (\lambda f. \\: f) \\\\
&= \underline{(\lambda t. \\: \lambda f. \\: t) \\:\\: (\lambda f. \\: f)} \\\\
&\rightarrow (\lambda f. \\: \lambda f. \\: f) \\\\
&= \texttt{false} &\textrm{(by }\alpha\textrm{-equivalence)}
\end{align}
$$
Notice that in the last step we used α-equivalence to justify saying that the term $\lambda f. \\: \lambda f. \\: f$
is equivalent to `false`—the $f$ here is bound by the *inner* binder, and so we're free to rename the outer binder however we like.

Now let's try our hand at conditionals:
```
if := λc. λt. λe. c t e
```
Here, we kind of see how the pieces will fit together:
`c` will be a boolean, a two-argument function that returns its first argument if true or its second if false.
Then we pass in the *then* and *else* terms to `c`.
If it's true it returns the *then* term, otherwise it returns the *else* term.
For example, where $v$ and $w$ are values:
$$
\begin{align}
\texttt{if true v w} &= \underline{(\lambda c. \\: \lambda t. \\: \lambda e. \\: c \\:\\: t \\:\\: e) \\:\\: \texttt{true}} \\:\\: \texttt{v} \\:\\: \texttt{w} \\\\
&\rightarrow \underline{(\lambda t. \\: \lambda e. \\: \texttt{true} \\:\\: t \\:\\: e)} \\:\\: \texttt{v} \\:\\: \texttt{w} \\\\
&\rightarrow \underline{(\lambda e. \\: \texttt{true} \\:\\: \texttt{v} \\:\\: e) \\:\\: \texttt{w}} \\\\
&\rightarrow \texttt{true} \\:\\: \texttt{v} \\:\\: \texttt{w} \\\\
&= \underline{(\lambda t. \\: \lambda f. \\: t) \\:\\: \texttt{v}} \\:\\: \texttt{w} \\\\
&\rightarrow \underline{(\lambda f. \\: \texttt{v}) \\:\\: \texttt{w}} \\\\
&\rightarrow \texttt{v}
\end{align}
$$

This definition is *almost* right, but it does have one problem:
it's not *short-circuiting*,
and under the call-by-value strategy,
it will evaluate *both* sides of the `if` expression before returning the correct one
(see [this example](https://capra.cs.cornell.edu/lambdalab/#%7B%22code%22%3A%22IF%20TRUE%20(PLUS%20ONE%20ZERO)%20(PLUS%20ONE%20ONE)%22%2C%22strategy%22%3A1%2C%22macros%22%3A%22ID%20%E2%89%9C%20%CE%BBx.%20x%5CnSUCC%20%E2%89%9C%20%CE%BBn.%20%CE%BBf.%20%CE%BBx.%20f%20(n%20f%20x)%5CnZERO%20%E2%89%9C%20%CE%BBf.%20%CE%BBx.%20x%5CnONE%20%E2%89%9C%20%CE%BBf.%20%CE%BBx.%20f%20x%5CnPLUS%20%E2%89%9C%20%CE%BBm.%20%CE%BBn.%20n%20SUCC%20m%5CnMULT%20%E2%89%9C%20%CE%BBm.%20%CE%BBn.%20m%20((%CE%BBm.%20%CE%BBn.%20n%20SUCC%20m)%20n)%20(%CE%BBf.%20%CE%BBx.%20x)%5CnPRED%20%E2%89%9C%20%CE%BBn.%20%CE%BBf.%20%CE%BBx.%20n%20(%CE%BBg.%20%CE%BBh.%20h%20(g%20f))%20(%CE%BBu.%20x)%20(%CE%BBx.%20x)%5CnSUB%20%E2%89%9C%20%CE%BBm.%20%CE%BBn.%20n%20PRED%20m%5CnTRUE%20%E2%89%9C%20%CE%BBa.%20%CE%BBb.%20a%5CnFALSE%20%E2%89%9C%20%CE%BBa.%20%CE%BBb.%20b%5CnIF%20%E2%89%9C%20%CE%BBb.%20%CE%BBt.%20%CE%BBf.%20b%20t%20f%22%7D) on λab).
That isn't going to matter much for our purposes,
but it's worth pondering a little.
Under call-by-name semantics,
that wouldn't happen
(see [this example](https://capra.cs.cornell.edu/lambdalab/#%7B%22code%22%3A%22IF%20TRUE%20(PLUS%20ONE%20ZERO)%20(PLUS%20ONE%20ONE)%22%2C%22strategy%22%3A2%2C%22macros%22%3A%22ID%20%E2%89%9C%20%CE%BBx.%20x%5CnSUCC%20%E2%89%9C%20%CE%BBn.%20%CE%BBf.%20%CE%BBx.%20f%20(n%20f%20x)%5CnZERO%20%E2%89%9C%20%CE%BBf.%20%CE%BBx.%20x%5CnONE%20%E2%89%9C%20%CE%BBf.%20%CE%BBx.%20f%20x%5CnPLUS%20%E2%89%9C%20%CE%BBm.%20%CE%BBn.%20n%20SUCC%20m%5CnMULT%20%E2%89%9C%20%CE%BBm.%20%CE%BBn.%20m%20((%CE%BBm.%20%CE%BBn.%20n%20SUCC%20m)%20n)%20(%CE%BBf.%20%CE%BBx.%20x)%5CnPRED%20%E2%89%9C%20%CE%BBn.%20%CE%BBf.%20%CE%BBx.%20n%20(%CE%BBg.%20%CE%BBh.%20h%20(g%20f))%20(%CE%BBu.%20x)%20(%CE%BBx.%20x)%5CnSUB%20%E2%89%9C%20%CE%BBm.%20%CE%BBn.%20n%20PRED%20m%5CnTRUE%20%E2%89%9C%20%CE%BBa.%20%CE%BBb.%20a%5CnFALSE%20%E2%89%9C%20%CE%BBa.%20%CE%BBb.%20b%5CnIF%20%E2%89%9C%20%CE%BBb.%20%CE%BBt.%20%CE%BBf.%20b%20t%20f%22%7D)).
None of this is a violation of the confluence principle we discussed earlier:
both evaluation strategies end up in the same final result,
they just take different paths to get there.
The problem is that in most languages
the path we take actually matters,
perhaps because of *side effects* of evaluating a term,
and so we really want the short-circuiting effect.
But lambda calculus doesn't have side effects!

### Natural numbers

We can also add the natural numbers to the lambda calculus
through the *Church encoding*.
We've actually already seen something very similar to this
when we defined the natural numbers as an inductive set in [Week 01](@/notes/week01/_index.md).
We define the natural numbers like this:
```
0 := λf. λx. x
1 := λf. λx. f x
2 := λf. λx. f (f x)
3 := λf. λx. f (f (f x))
...
```
If we wanted to try explaining this definition,
we might say that a number `n` is a term that takes as input two arguments,
a function `f` and a base term `x`, and applies `f` to `x` `n` times.
In some sense, a number is a term that applies a function that many times to some base term.

A more useful way to see this is to go back to how we defined the natural numbers earlier,
by definition a *successor function*:
```
succ := λn. λf. λx. f (n f x)
```

Let's see that in practice:
$$
\begin{align}
\texttt{succ 1} &= \underline{(\lambda n. \\: \lambda f. \\: \lambda x. \\: f \\:\\: (n \\:\\: f \\:\\: x)) \\:\\: (\lambda f. \\: \lambda x. \\: f \\:\\: x)} \\\\
&\rightarrow \lambda f. \\: \lambda x. \\: f \\: ((\lambda f. \\: \lambda x. \\: f \\:\\: x) \\: f \\: x) \\\\
&= \lambda f. \\: \lambda x. \\: f \\: (\texttt{one} \\: f \\: x) \\\\
\end{align}
$$
This term says "apply the function `f` to `x` `one` times, and then apply `f` one more time",
which is equivalent to `two`.
But if we're being precise,
we're actually stuck in the reduction here,
because call-by-value stops reducing once the head term is an abstraction.
This fine—once we go to actually *apply* the result `succ 1` to something, we'll be able to continue,
and get the same result as if we applied `2`.
If we go beyond call-by-value and allow ourselves to reduce inside the abstraction,
we can see where we end up without needing more arguments:
$$
\begin{align}
&\lambda f. \\: \lambda x. \\: f \\: (\texttt{one} \\: f \\: x) \\\\
&= \lambda f. \\: \lambda x. \\: f \\: (\underline{(\lambda f. \\: \lambda x. \\: f \\:\\: x) \\: f} \\: x) \\\\
&\rightarrow \lambda f. \\: \lambda x. \\: f \\: \underline{((\lambda x. \\: f \\:\\: x) \\: x)} \\\\
&\rightarrow \lambda f. \\: \lambda x. \\: f \\: (f \\: x) \\\\
&= \texttt{2}
\end{align}
$$

Finally, addition is just applying `succ` multiple times:
```
add := λm. λn. n succ m
```
We can also define all the other usual arithmetic stuff,
like `mul` and `pred` and `isZero`.

This is a very *tedious* encoding,
but it is a correct encoding.
In fact,
there's a proof in Section 11.2 of [*Formal Reasoning About Programs*](http://adam.chlipala.net/frap/)
that this encoding is equivalent to the inductive version we've been using in Coq.

### Recursion and loops

Finally, we'd expect a Turing-complete language to have some notion of (potentially infinite) recursion.
Recursive functions are a bit tricky in the lambda calculus—we saw in both Racket and Coq
that recursive functions needed to be able to refer to *their own name*,
but there is no notion of names inside the lambda calculus.
Instead, to define recursion we use *combinators*
(actually, the "macros" or "names" we've been using so far are just combinators too).

First, can we write a program in the lambda calculus that loops forever?
Here's the omega combinator:
```
omega := (λx. x x) (λx. x x)
```
Watch what happens when we β-reduce it once:
$$
\begin{align}
&\underline{(\lambda x. \\: x \\: x) \\: (\lambda x. \\: x \\: x)} \\\\
&\rightarrow (\lambda x. \\: x \\: x) \\: (\lambda x. \\: x \\: x)
\end{align}
$$
We just end up back in the same place! This should give us a little more confidence about how expressive the lambda calculus is:
it allows non-terminating programs.

The omega combinator's not very useful, though.
What we really want is a way to write a *recursive* abstraction
that refers to itself.
We get that by means of a *fixed-point combinator*.
There are multiple ways to write such a combinator, but one popular one
is called the *(call-by-value) Y-combinator*.
(Aside: now you know why that orange website is called what it is).
The version for call-by-name evaluation is simpler,
but the ugly call-by-value version looks like this:
```
Y := λF. (λf. (λx. f (λv. x x v)) (λx. f (λv. x x v))) F
```
This is intricate and not really possible to understand just by looking at its definition.
Let's attack it with a couple of examples.
First, why is `Y` called a "fixed-point" combinator?
Because of the way it evaluates:
$$
\begin{align}
Y \\: F &= \underline{(\lambda f. \\: (\lambda x. \\: f \\: (\lambda v. \\: x \\: x \\: v)) \\: (\lambda x. \\: f \\: (\lambda v. \\: x \\: x \\: v))) \\: F} \\\\
&\rightarrow \underline{(\lambda x. \\: F \\: (\lambda v. \\: x \\: x \\: v)) \\: (\lambda x. \\: F \\: (\lambda v. \\: x \\: x \\: v))} \\\\
&\rightarrow F \\: (\lambda v. \\: \underline{(\lambda x. \\: F \\: (\lambda v. \\: x \\: x \\: v)) \\: (\lambda x. \\: F \\: (\lambda v. \\: x \\: x \\: v))} \\: v) \\\\
&\approx F \\: (\lambda v. \\: (Y \\: F) \\: v) \\\\
&\approx F \\: (Y \\: F)
\end{align}
$$
Here I'm handwaving the last two steps a bit,
because we're not really allowed to simplify like this:
first we notice that the underlined term is the same one we already stepped `Y F` to on the second line,
and second we're handwaving how function application works since we don't yet have a `v` to apply onto.
The point is that this is computing a *fixed point* of `F`.

Now, how do we use a fixed-point combinator like `Y`?
The idea is that we can now write a function like this one, for the factorial function:
```
g := λfact'. λn. if (isZero n) 1 (mul n (fact' (pred n)))
factorial := λn. Y g n
```
What we've managed to do is write a recursive function
that refers to itself, `fact'`,
by hiding it behind an abstraction `g`
and then invoking the Y combinator on `g`.

This combinator stuff hurts my head a whole bunch,
and it's not super critical to understand exactly how it works
(although it's fun to play around with!).
The takeaway is that we can implement recursive functions in the pure lambda calculus.
Once we add booleans and numbers to the mix,
hopefully you're convinced that
this looks a lot like any other programming language,
just a bit more inconvenient.

## Baking things in and getting stuck

Everything we've just done "works",
in the sense that we can encode any Turing machine using these primitives.
But the encodings are incredibly tedious to work with.
Let's try extending our lambda calculus
by "baking in" some of the features we were adding manually.
In particular, I want to extend the lambda calculus with booleans.

As always, we'll need both a syntactic and semantic extension.
The syntax just adds `true`, `false`, and conditionals:
```
t := x
   | λx. t
   | t t
   | true
   | false
   | if t then t else t
```

When doing β-reduction, we had a notion of "values",
and said that applications could only step when the right-hand side is a value.
We need to remember that we now have some new values `true` and `false` in our language.

The semantics is not too tricky, either.
It looks a lot like it did for IMP,
by adding three rules:
$$
\frac{e_1 \rightarrow e_1'}{\texttt{if } e_1 \texttt{ then } e_2 \texttt{ else } e_3 \rightarrow \texttt{if } e_1' \texttt{ then } e_2 \texttt{ else } e_3}
$$
$$
\frac{}{\texttt{if true then } e_2 \texttt{ else } e_3 \rightarrow e_2}
$$
$$
\frac{}{\texttt{if false then } e_2 \texttt{ else } e_3 \rightarrow e_2}
$$
The first rule reduces the condition until it's either `true` or `false`,
and then the third rule chooses which side of the expression to run.

This all seems reasonable enough,
but we've just accidentally created a huge problem in our language.
Look at these two terms:
```
if (λx. x) then true else false
true (λx. x)
```
They can't step at all! None of the `if` rules we just added apply to the first term,
and although the second term has the shape of an application,
the left-hand side isn't an abstraction,
so we can't β-reduce it further.
But neither of these terms are *values*.
They are *stuck*!

You might recognize problems like this one
from real programming languages as a "type error".
The idea is that some programs,
although they are *syntactically* well-formed,
are not actually valid programs.

Ruling out these invalid programs is the role of a *type system*,
and in the next lecture,
we'll see how to build a type system for this extended lambda calculus
and *prove* that it prevents programs getting stuck.


