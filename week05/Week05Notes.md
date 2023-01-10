+++
title = "Week 05 - Imp: Operational Semantics"
+++

# Week 05 - Imp: Operational Semantics

_These notes were written by primarily by Prof. James Bornholt for his course at
UT Austin. James is a PhD alum of UW and "friend of the channel", and we thank
him for permission to reuse and adapt these notes back at UW!_

In [Week 03](@/notes/week03/_index.md) we foreshadowed the need
for a different style of semantics that could handle non-terminating programs.
In [Week 04](@/notes/week04/_index.md)
we started building some infrastructure that could deal with non-termination
using *transition systems*,
which allowed us to talk about intermediate *states* of a program
and the *steps* between them.
We saw that we could use this infrastructure to prove invariants about programs
even if they didn't terminate.

However, when we were building transition systems for programs,
we were doing a lot of manual work.
For each program, we had to manually define the "states" of the program.
The choice of states was critical—make the wrong choice and we'd be able
to prove invariants that weren't really invariant,
or we wouldn't be able to prove anything at all.

In this lecture, we'll see how to *automate*
converting a program into a transition system.
This approach to modeling programs is known as *operational semantics*,
and gives us a more general way to talk about intermediate states of any program
in some language.

## The IMP language

We're going to illustate operational semantics using a language called IMP.
IMP is often used as an example of a simple but realistic programming language
because it has most of the features you'd expect—loops, conditionals, and assignment.
You'll see a version of IMP in most PL textbooks;
they vary in minor ways, but the idea is the same.

As always, to define a programming language, we need two things: syntax and semantics.
Here's the syntax for IMP:

```
cmd := skip
     | var <- expr
     | cmd; cmd
     | if expr then cmd else cmd
     | while expr do cmd
```

Here, we're reusing the `expr` language we saw at the end of [Week 03](@/notes/week03/_index.md), whose syntax looked like this:
```
expr := Const nat
      | Var var
      | Plus expr expr
      | Times expr expr
```

What about semantics? Well, we saw in Lecture 2 that denotational semantics
wouldn't work easily here, because we have loops that might not terminate.
Instead, we're going to define IMP's semantics *operationally*
as a transition system.

## Small-step operational semantics

In Lecture 3, we had to redefine a transition system *for every program*,
because the way we defined states and steps was by staring at the program
and handwaving about "iterations of the loop".
How can we instead define a transition system *for the entire language* once and for all,
rather than inventing one for each program?

We know we're defining a transition system,
so we need to define three things:
1. The set of states $S$. We saw at the end of Lecture 3 that, in addition to tracking variables, our states need some way to remember where we are in executing the program. We're going to do this by making our states be *pairs* $(v, c)$, where $v$ is a valuation (a variable map) assigning values to each variable, and $c$ is a `cmd` reflecting the "rest" of the program that still needs to be executed. Informally, we can think of $c$ as analogous to the *program counter* most computer architectures have—it lets us track where we are in the program so that we know what the next step(s) will be.
2. The set of initial states $S_0 \subseteq S$. Knowing how we define states, we can define the initial state as just an initial valuation $v_0$ and the program to execute $c_0$. Again the analogy to architectures: when a program states, the program counter is at the start of the program (the entire program remains to be executed), and the memory is either empty or all-zeros, depending on how you think about it.
3. The transition relation $\rightarrow$. From our definition of states, we know this relation needs to tell us when we can step $(v, c) \rightarrow (v', c')$. Clearly, this is going to depend on $v$ and $c$, but it *no longer depends on the actual program* we're trying to model, unlike in Lecture 3.

So the big remaining task is to define the transition relation $\rightarrow$.
We could try to write it down as a set, like we did in the last lecture,
but that would be pretty tedious.
Instead, let's use the idea of an inductively defined proposition from last lecture
and define $\rightarrow$ as a set of *inference rules*.
As usual with an inductive definition like `cmd`,
we need to consider cases for each constructor.

First, let's deal with assignments `x <- e`.
Informally we know how this works:
we evaluate `e` and then update the valuation to map `x` to that value.
Here it is as an inference rule:
$$
\frac{v' = v[x \mapsto \[\\!\[ e \]\\!\]_v]}
{(v, \texttt{x <- e}) \rightarrow (v', \texttt{skip})} \\: \textrm{Assign}
$$
What we've said is that, to step an assignment statement,
we evaluate $e$ with its denotational semantics,
and then update the current valuation $v$ to map $x$ to that new value.
Notice that, when we had to choose a command `c` to step *to*,
we used `skip`.
The idea is that `skip` in this position means "terminated";
if we ever reach a state $(v, \texttt{skip})$
then there's nowhere left to go and $v$ is the final state of the program.
So if our program is just a single assignment statement,
we execute this rule once and then the program is done.
We've also given this rule a name $\textrm{Assign}$ by writing it next to the rule.
Naming our inference rules is going to be very helpful later
(and we'll do it in Coq as well),
so it's a good habit to get into.

Now let's look at sequence commands `c1; c2`.
The intuition is that to execute two commands in sequence,
you first fully execute the left-hand side,
and then fully execute the right-hand side
starting from the state the left side ended in.
So we'll need a rule like this for the first case:
$$
\frac{(v, c_1) \rightarrow (v', c_1')}
{(v, c_1 \texttt{; } c_2) \rightarrow (v', c_1' \texttt{; } c_2)} \\: \textrm{SeqL}
$$
But how do we know we're "done"?
Above, we said that `skip` means "terminated",
so the idea is that we're done with the left-hand side
when the $\textrm{SeqL}$ steps us to $c_1' = \texttt{skip}$.
At that point, we can start stepping the right-hand side
using a second rule:
$$
\frac{}
{(v, \texttt{skip; } c_2) \rightarrow (v, c_2)} \\: \textrm{SeqR}
$$
In words, once we're done with the left hand side,
we can just get rid of it and make $c_2$ our remaining program.
The other inference rules will then let us start executing $c_2$.

How about conditionals `if e then c1 else c2`?
Our intuition is that conditionals can go two ways:
if `e` is non-zero, then we want to execute `c1`,
otherwise we want to execute `c2`.
This structure suggests two inference rules,
one for each side of the conditional:
$$
\frac{\[\\!\[ e \]\\!\]_v \neq 0}
{(v, \texttt{if} \\; e \\; \texttt{then} \\; c_1 \\; \texttt{else} \\; c_2) \rightarrow (v, c_1)} \\: \textrm{IfTrue}
$$
$$
\frac{\[\\!\[ e \]\\!\]_v = 0}
{(v, \texttt{if} \\; e \\; \texttt{then} \\; c_1 \\; \texttt{else} \\; c_2) \rightarrow (v, c_2)} \\: \textrm{IfFalse}
$$
Just like for $\textrm{SeqR}$, these two rules are essentially telling us which
part of the `if` statement we can "get rid of".
If we want to enter the `then` branch,
we throw away everything except $c_1$ and just start executing that;
otherwise we throw away everything except $c_2$ and do the same.

While loops `while e do c` are conceptually similar to `if`—we need
a rule for entering the loop and a rule for not entering the loop.
The big difference is that, when we enter the loop,
we need to retain the loop as code that needs to be executed in the future
because we want the whole loop to be evaluated again once the body has run once.
Luckily, the sequence operation `;` gives us what we need to pull this off.
We end up with this rule for entering the loop:
$$
\frac{\[\\!\[ e \]\\!\]_v \neq 0}
{(v, \texttt{while} \\; e \\; \texttt{do} \\; c) \rightarrow (v, c \texttt{; } \texttt{while} \\; e \\; \texttt{do} \\; c)} \\: \textrm{WhileTrue}
$$
In words, if `e` evaluates to non-zero, then we know we need to execute the body of the loop `c` one time,
and then re-execute the entire loop.
The case fot not entering the loop just lets us throw the whole thing away:
$$
\frac{\[\\!\[ e \]\\!\]_v = 0}
{(v, \texttt{while} \\; e \\; \texttt{do} \\; c) \rightarrow (v, \texttt{skip})} \\: \textrm{WhileFalse}
$$

Finally, what about `skip`?
We've been using `skip` to mean termination.
Termination means the program can't step any more.
So that means *there's no rule with `skip` on the left-hand side*!
If we ever reach a state $(v, \texttt{skip})$,
the program will therefore no longer be able to step,
as there are no matching rules,
so this state reflects termination.

We're done! We've defined the entire transition relation for IMP
as an inductively defined proposition (a set of inference rules whose conclusions are propositions about $\rightarrow$).
In PL, we call the transition system defined the way we just did a *small-step operational semantics* for the language.
It's *operational* because it talks about *how* to execute the program rather than *what* value the program has (denotational semantics).
We'll see a little later why we call it *small step*. But first, let's see it in action.

### An example execution

Last lecture we studied this program:
```
x = 5
while True:
    x = x + 1
```
which we can translate into our IMP syntax like this:
```
x <- 5; while 1 do (x <- x + 1)
```

Let's see how this program executes under our small-step operational semantics.
We start from the state $(\emptyset, x \texttt{ <- } 5 \texttt{; while } 1 \texttt{ do } (x \texttt{ <- } x + 1))$,
where we write $\emptyset$ for the valuation with no variables set
and are starting from a state where we have the entire program left to execute.
Then we step like this:
$$
\begin{align}
&(\emptyset, x \texttt{ <- } 5 \texttt{; while } 1 \texttt{ do } (x \texttt{ <- } x + 1)) \\\\
&\quad\quad\rightarrow (\\{ x \mapsto 5\\}, \texttt{skip; while } 1 \texttt{ do } (x \texttt{ <- } x + 1)) &\textrm{by SeqL and Assign} \\\\
&\quad\quad\rightarrow (\\{ x \mapsto 5\\}, \texttt{while } 1 \texttt{ do } (x \texttt{ <- } x + 1)) &\textrm{by SeqR} \\\\
&\quad\quad\rightarrow (\\{ x \mapsto 5\\}, x \texttt{ <- } x + 1 \texttt{; while } 1 \texttt{ do } (x \texttt{ <- } x + 1)) &\textrm{by WhileTrue} \\\\
&\quad\quad\rightarrow (\\{ x \mapsto 6\\}, \texttt{skip; while } 1 \texttt{ do } (x \texttt{ <- } x + 1)) &\textrm{by SeqL and Assign} \\\\
&\quad\quad\rightarrow (\\{ x \mapsto 6\\}, \texttt{while } 1 \texttt{ do } (x \texttt{ <- } x + 1)) &\textrm{by SeqR} \\\\
&\quad\quad\rightarrow (\\{ x \mapsto 6\\}, x \texttt{ <- } x + 1 \texttt{; while } 1 \texttt{ do } (x \texttt{ <- } x + 1)) &\textrm{by WhileTrue} \\\\
&\quad\quad\rightarrow (\\{ x \mapsto 7\\}, \texttt{skip; while } 1 \texttt{ do } (x \texttt{ <- } x + 1)) &\textrm{by SeqL and Assign} \\\\
&\quad\quad\rightarrow (\\{ x \mapsto 7\\}, \texttt{while } 1 \texttt{ do } (x \texttt{ <- } x + 1)) &\textrm{by SeqR} \\\\
&\quad\quad\dots
\end{align}
$$

### Small-step semantics for concurrency

Our small-step semantics lets us talk about non-terminating and non-deterministic executions,
which is a big step up over the denotational semantics we saw before.
This is especially useful for concurrency,
where we often talk about *interleavings* of concurrent tasks.
We can reflect this idea in a small-step operational semantics.
I'm not going to do the full development here—both *Software Foundations* and *Formal Reasoning About Programs*
give good treatments of operational semantics for concurrency—but I can give the general idea.

Let's add a new *parallel composition* construct `c1 || c2` to our IMP language.
The idea is that `c1 || c2` represents two commands executing *concurrently*.
At each step of the program,
we can *choose* which of `c1` and `c2` is the next one to step,
and in this way we're able to reach states that reflect interleavings of `c1` and `c2`.
Operationally, this is just two simple rules:
$$
\frac{(v, c_1) \rightarrow (v', c_1')}
{(v, c_1 \texttt{ || } c_2) \rightarrow (v', c_1' \texttt{ || } c_2)} \\: \textrm{ParL}
$$
$$
\frac{(v, c_2) \rightarrow (v', c_2')}
{(v, c_1 \texttt{ || } c_2) \rightarrow (v', c_1 \texttt{ || } c_2')} \\: \textrm{ParR}
$$
We also need a rule to "clean up" a terminated concurrent task and allow us to keep executing:
$$
\frac{}
{(v, \texttt{skip || } c_2) \rightarrow (v, c_2)} \\: \textrm{ParSkipL}
$$

Notice that $\textrm{ParL}$ and $\textrm{ParR}$ introduce *non-determinism* into our semantics—they
can both be "enabled" at the same time.
This is OK! When we talked about the step-star relation last lecture
we were a little bit loose about what it meant.
If $(v, c) \rightarrow^* (v', c')$,
that means the program *can* step to the state $(v', c')$;
it doesn't mean that the program *must* step to that state.
In other words,
it's possible for $(v, c) \rightarrow^* (v_1, c_1)$
and $(v, c) \rightarrow^* (v_2, c_2)$ to hold,
with $c_1 = c_2 = \texttt{skip}$ (i.e., both executions terminated),
but $v_1 \neq v_2$.

## Big-step operational semantics

Small-step operational semantics give us a powerful and general purpose way to talk about the behavior of a program.
Every step makes only a small change to the "state" of the program,
and so we can talk about fine grained invariants of the program.
This was especially great because it let us talk about the steps taken by non-terminating programs,
and so prove interesting things about them even in the face of non-termination.
The fine-grained steps also gave us a convenient way to model non-determinism,
and especially concurrency—non-determinism is just having multiple rules that might apply to any individual state.

But small-step semantics are pretty tedious.
Most of the energy we spent on small-step proofs was not very interesting:
it was just crunching through transitions of the step-star relation,
and then every once in a while we'd get to actually "execute" a small piece of the program
(roughly speaking, the only interesting transitions were the ones where the valuation changed).
The `seq` rules were especially annoying:
they required us to repeatedly disassemble the program into smaller pieces (the $c_1$s in $\textrm{StepSeqLeft}$),
only to put them back together again into the resulting `seq` operation
(this style of rule is known as a _congruence_ rule, because it relates smaller steps to larger ones).
Is there a middle ground between tedious-but-powerful small-step operational semantics
and simple-but-inexpressive denotational semantics?

The answer is _big-step_ operational semantics.
As the name suggests, big-step semantics take big steps,
and in particular,
a big step semantics relates any $(v, c)$ state to its _final_ valuation $v$ in just one step.
In the same style as the $\rightarrow$ of small-step semantics,
we write big-step semantics as a relation $(v, c) \Downarrow v'$,
and say that $(v, c)$ _evaluates to_ (or sometimes _reduces to_) final state $v'$.

### Big-step semantics for IMP

Just like small-step semantics, we can define the big-step semantics relation $\Downarrow$ for a language
inductively as a set of inference rules.

The first rule is already somewhat surprising, remembering what we said about `skip` in the small-step case:
$$
\frac{}
{(v, \texttt{skip}) \Downarrow v} \\: \textrm{SSkip}
$$
Here we're saying that `skip` _can_ (big-)step,
whereas in the small-step semantics we said that any state where $c = \texttt{skip}$ is considered terminated and could no longer step.
This rule is really just the realization of that idea
in a world where we have to "return" the final value of the program:
if you start from a state $(v, \texttt{skip})$,
the final value of the program evaluated from that state is just $v$,
because it does no more work.

The assignment rule isn't too different from its small-step version:
$$
\frac{}
{(v, x \texttt{ <- } e) \Downarrow v[x \mapsto \[\\!\[ e \]\\!\]_v  ]} \\: \textrm{SAssign}
$$
Just like $\textrm{Assign}$, we're saying that if the whole program is just an assignment statement,
its final value is just the initial valuation but with $x$ pointing to the result of evaluating $e$.

Here's another big difference from the small-step world: we only need one rule for `seq`, like this:
$$
\frac{(v, c_1) \Downarrow v' \quad (v', c_2) \Downarrow v''}
{(v, c_1 \texttt{; } c_2) \Downarrow v''} \\: \textrm{SSeq}
$$
We get away with only needing one rule because we "run" both parts of the `seq` as premises to the rule.
First, we reduce $c_1$ to its final state $v'$.
Then, _starting from_ $v'$ we reduce $c_2$ to its final state $v''$.
Therefore, $v''$ is the final state of running $c_1 \texttt{; } c_2$.

The rules for `if` look similar to their small-step counterparts,
except they follow the example of `seq` in moving the "work" of evaluating $c_1$ or $c_2$ "above the line":
$$
\frac{\[\\!\[ e \]\\!\]_v \neq 0 \quad (v, c_1) \Downarrow v'}
{(v, \texttt{if} \\; e \\; \texttt{then} \\; c_1 \\; \texttt{else} \\; c_2) \Downarrow v'} \\: \textrm{SIfTrue}
$$
$$
\frac{\[\\!\[ e \]\\!\]_v = 0 \quad (v, c_2) \Downarrow v'}
{(v, \texttt{if} \\; e \\; \texttt{then} \\; c_1 \\; \texttt{else} \\; c_2) \Downarrow v'} \\: \textrm{SIfFalse}
$$
In both cases, we're first deciding which side of the `if` to run,
and then, assuming that side reduces to valuation $v'$,
so too does the entire expression.

The rules for `while` are the most complex,
because we have to somehow deal with running the remaining iterations of the loop:
$$
\frac{\[\\!\[ e \]\\!\]_v \neq 0  \quad  (v, c_1) \Downarrow v'  \quad  (v', \texttt{while} \\; e \\; \texttt{do} \\; c) \Downarrow v''}
{(v, \texttt{while} \\; e \\; \texttt{do} \\; c) \Downarrow v''} \\: \textrm{SWhileTrue}
$$
To run a `while` command when the conditional evaluates to true,
we first evalutate the body a single time to get us to valuation $v'$,
and then run the whole loop again _starting from $v'$_ to get to a final state $v''$.
The false side of the rule, meanwhile, just doesn't run anything,
kind of like $\textrm{SSkip}$:
$$
\frac{\[\\!\[ e \]\\!\]_v = 0}
{(v, \texttt{while} \\; e \\; \texttt{do} \\; c) \Downarrow v} \\: \textrm{SWhileFalse}
$$

#### An example execution

Above we illustrated small-step semantics on the program `x <- 5; while 1 do (x <- x + 1)`.
That's not going to work here, just like it didn't work with denotational semantics,
because there is no final valuation for this non-terminating program.
Instead, let's study a simpler program:
```
x <- 1;
if x then y <- 1 else y <- 0
```

A convenient way to look at big-step semantics is using a _proof tree_,
which is kind of like building an interpreter from the semantics
and illustrating it with the rules that apply each time it recurses.
Here, the tree looks like this, with apologies for the not-great online typesetting:

$$
\frac{
    {\Large
    \frac{}
    {(\emptyset, \texttt{x <- 1}) \Downarrow \\{ x \mapsto 5 \\}}} \\: \textrm{SAssign}
    \quad\quad
    {\Large
    \frac{
        \[\[ \texttt{x} \]\]_v \neq 0
        \quad\quad
        {\Large
        \frac{}
        {(\\{ x \mapsto 5 \\}, \texttt{y <- 1}) \Downarrow \\{x \mapsto 5, y \mapsto 1\\}}} \\: \textrm{SAssign}
    }
    {(\\{ x \mapsto 5 \\}, \texttt{if x then y <- 1 else y <- 0}) \Downarrow \\{x \mapsto 5, y \mapsto 1\\}}} \\: \textrm{SIfTrue}
}
{(\emptyset, \texttt{x <- 1; if x then y <- 1 else y <- 0}) \Downarrow \\{x \mapsto 5, y \mapsto 1\\}} \\: \textrm{SSeq}
$$

To conclude that our program evaluates to the final state $\\{x \mapsto 5, y \mapsto 1\\}$,
we recursively applied big-step inference rules until every rule was an axiom or a non-recursive premise.

### Big-step semantics as a relation

The idea of the big-step $\Downarrow$ relation should remind you of denotational semantics—it gives us a way to talk about
the final result of a computation directly, rather than working through a sequence of small steps to get to it.
But unlike the denotational semantics we've seen,
big step semantics can at least be *defined* for languages that might not terminate.
When we tried to define denotational semantics for (a subset of) IMP in [Week 03](@/notes/week03/_index.md),
we saw that it was very difficult to write down a well-founded definition for `while` loops,
because the function we defined might recurse infinitely.

Here, we can still define $\Downarrow$ for `while` loops
because it is a _relation_ between $(v, c)$ pairs and their final values.
It's OK for a relation not to ascribe a value to every element in the domain
(indeed, that's one side of what it means for a relation to *be* a function:
a function is a relation that maps *every* element of its domain to *exactly one* element of its codomain).
So here, we can still talk about $\Downarrow$ for `while`,
with the understanding that for non-terminating programs $c$,
there is _no_ final valuation $v'$ such that $(v, c) \Downarrow v'$.

Similarly, the big-step semantics relation also still lets us talk about non-determinism;
it's OK for a relation to ascribe *more than one* value to an element of the domain.
If $(v, c) \Downarrow v_1$ and $(v, c) \Downarrow v_2$, where $v_1 \neq v_2$,
then the program $c$ is non-deterministic.
That said, *defining* a big-step semantics for concurrency, for example,
is quite tricky.
Concretely, it's not easy to write down an equivalent to the $\textrm{ParL}$ and $\textrm{ParR}$ rules we wrote above,
because big steps don't really give us a way to *interleave* steps of each side of the `||` operator.

### Equivalence of big-step and small-step semantics

Now that we've given two different semantics for IMP,
it would be nice to know that they are "the same",
for some suitable definition of equivalence.
I'm going to elide the proofs because they're a bit tedious,
but the idea goes something like this:

**Theorem**: If $(v, c) \Downarrow v'$, then $(v, c) \rightarrow^\* (v', \texttt{skip})$.

**Proof**: By induction on the proposition $\Downarrow$.

The other direction is also by induction, but needs a strengthened lemma to go through.

**Lemma**: If $(v, c) \rightarrow^* (v', c')$ and $(v', c') \Downarrow v''$, then $(v, c) \Downarrow v''$.

**Proof**: By induction on the proposition $\rightarrow^*$.

**Theorem**: If $(v, c) \rightarrow^\* (v', \texttt{skip})$, then $(v, c) \Downarrow v'$.

**Proof**: Apply the previous lemma with $c' = \texttt{skip}$, since $(v', \texttt{skip}) \Downarrow v'$.

## Big steps or small?

Why bother with both these approaches?
My sense is that small-step operational semantics are the most common approach to modern programming language semantics,
in large part because they let us talk about concurrency and non-termination comfortably.
I also think small-step semantics is more *interesting*,
because it gives as an additional dimension to think about when formalizing a language:
how small should the steps be?
The right answer to that question might often depend on what we want to use the semantics for,
which is a Big PL Idea—we can design the semantics *for* the problem we want to solve,
making our lives much easier.

But hopefully seeing both gives a sense of the spectrum of semantics approaches we've seen so far:
big-step semantics sit somewhere between denotational and small-step in terms of both convenience and expressiveness.
They give us the ability to at least formalize a semantics for a language that allows non-terminating programs,
and to do some reasoning about programs in that language so long as they terminate.

On a less fundamental but still interesting note,
big-step semantics are more convenient that denotational semantics
from the perspective of a proof assistant like Coq,
which leans heavily into (inductively defined) propositions as the way to formalize the world.
Interpreters don't give rise to a natural definition in this style,
but big-step semantics do.
In some sense, big-step semantics are the *canonical way* to formalize interpreters in Coq,
rather than the function-oriented approach we studied in [Week 03](@/notes/week03/_index.md).

