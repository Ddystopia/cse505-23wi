+++
title = "Week 06 - Hoare Logic"
+++

# Week 06 - Hoare Logic

_These notes were written primarily by Prof. James Bornholt for his course at
UT Austin. James is a PhD alum of UW and "friend of the channel", and we thank
him for permission to reuse and adapt these notes back at UW!_

Over the last few lectures, we've been building and refining ways to *prove properties about programs*.
In [Week 04](@/notes/week04/_index.md), we saw how to manually construct a transition system for a program,
and then use that transition system to prove things about the behaviors of that program.
But constructing those transition systems was a manual process for each new program.
In [Week 05](@/notes/week05/_index.md), we remedied this with operational semantics,
which allowed us to define a transition system for a language once and for all,
and use it to prove things about the behavior of any program in that language.
But those proofs were tedious, because they required us to think about every small step of the program,
most of which were terribly uninteresting for the properties we were looking to prove.
They also required us to come up with different invariants to the ones we wanted—including
needing to somehow inline the program itself into the invariant.
It was a promising approach, and worked well for proving properties about *languages*,
but was overly tedious for proving properties about *programs*.

In this lecture, we'll further automate this pipeline for proving properties about programs
by introducing *axiomatic semantics*,
our third (and final) approach to semantics in this course.
Axiomatic semantics define the meaning of a program in terms of logical assertions,
such as *pre-* and *post-conditions* about program states.

We'll focus in particular on the most popular style of axiomatic semantics,
known as *Hoare logic* for its creator, [Sir Tony Hoare](https://en.wikipedia.org/wiki/Tony_Hoare),
or sometimes as *Floyd-Hoare logic* as it was earlier developed in a separate context by [Robert Floyd](https://en.wikipedia.org/wiki/Robert_W._Floyd).
(They both received Turing awards for this work!)
Hoare logic will give us a way to write down *proof rules* about programs,
prove those rules correct once and for all,
and then apply them to any program without appealing to the tedious operational semantics.

## Hoare triples

In [Week 05](@/notes/week05/_index.md) we introduced a few new *propositions* about programs.
One proposition $(v, c) \rightarrow^* (v', c')$ was about reachability;
if true, this proposition means that the program can reach state $(v' ,c')$ if it starts from state $(v, c)$.
Another proposition $(v, c) \Downarrow v'$ was about termination:
if true, this proposition means that the program can terminate in state $v'$ when starting from state $(v, c)$.

Hoare logic introduces another proposition about programs,
this time about *invariants* of the program.
The big idea of Hoare logic is to think about invariants
and how they *change* when a program executes.
In a sentence, a proposition in Hoare logic says:

> If property $P$ holds before program `c` runs, then property $Q$ holds after.

Here, $P$ and $Q$ are *predicates over states*, sometimes called *assertions*,
and `c` is a program in IMP.
The assertion $P$ that holds before executing `c` is called a *precondition*.
The assertion $Q$ that holds after executing `c` is called a *postcondition*.
We call a Hoare logic proposition like this one a *Hoare triple*.
Just like $\rightarrow^*$ and $\Downarrow$, Hoare triples are propositions that may be true or false,
and we'll define rules for *when* Hoare triples are true shortly.

Hoare triples are so common that, as is often the case in PL, we have a special notation for them:
$$
\\{ P \\} \\: c \\: \\{ Q \\}
$$
We sometimes say that a Hoare triple is *valid* if this proposition is actually true.

You might have noticed a subtlety in the English definition of the postcondition $Q$ above.
A Hoare triple says that property $Q$ holds after executing `c`.
But what if `c` doesn't terminate, as IMP programs are not guaranteed to do?
For now, we are going to study Hoare logic through a lens of *partial correctness*.
Our Hoare triples will actually mean something slightly weaker:

> If property $P$ holds before program `c` runs, *and `c` terminates*, then property $Q$ holds after.

There is also a variant of Hoare logic whose triples, written $\[ P \] \\: c \\: \[ Q \]$,
also promise termination:

> If property $P$ holds before program `c` runs, then `c` terminates and $Q$ holds after termination.

This is known as *total correctness*. We won't study it further,
because it's not interestingly different, but is harder.
Just remember that our focus on partial correctness will make our Hoare logic a little weaker,
because it won't allow us to draw any conclusions about programs that don't terminate.
We'll see a little later how to recover some of this ability.

### Examples of Hoare triples

Even though we haven't precisely defined the rules of Hoare logic,
we can appeal to our intuition about IMP's semantics to see when Hoare triples are valid.
Here are a few examples:
* $\\{ x = 5 \\} \\: x \texttt{ <- } x + 5 \\: \\{ x = 10 \\}$ is valid: if $x$ was 5 before executing the program,
  which just incremented $x$ by 5, then surely $x = 10$ is true afterwards.
* $\\{ x = 5 \\} \\: x \texttt{ <- } x + 5 \\: \\{ x \geq 6 \\}$ is valid: just like the previous one,
  $x \geq 6$ is just another property that is true after executing the program.
* $\\{ x \geq 5 \\} \\: x \texttt{ <- } x + 5 \\: \\{ x \geq 10 \\}$ is valid: a slightly more interesting example,
  but simple math tells us that this one holds.
* $\\{ \textrm{true} \\} \\: x \texttt{ <- } 10 \\: \\{ x = 10 \\}$ is valid: no matter what state we start from,
  if we execute this assignment, this postcondition must hold.

Let's look at conditionals:
* $\\{ x \geq 0 \\} \\: \texttt{if } x \texttt{ then } x \texttt{ <- } x - x \texttt { else skip} \\: \\{ x = 0 \\}$ is valid:
  regardless of which branch we take, the postcondition holds after execution.
* $\\{ x > 0 \\} \\: \texttt{if } x \texttt{ then } x \texttt{ <- } x - x \texttt { else } x \texttt{ <- } 1 \\: \\{ x = 0 \\}$ is valid:
  even though the `else` branch would violate our postcondition, it is unreachable,
  because the precondition says $x$ is greater than zero and the condition we test is $x$.


And here are some more extreme examples:
* For any `c`, $\\{ \textrm{true} \\} \\: \texttt{c} \\: \\{ \textrm{true} \\}$ is valid, since $\textrm{true}$ is, well, always true, regardless of program state.
* For any `c` and $Q$, $\\{ \textrm{false} \\} \\: \texttt{c} \\: \\{ Q \\}$ is valid. The precondition never holds,
  and our definition of a Hoare triple started "If the precondition holds ...", so this triple is vacuously true.
* $\\{ \textrm{true} \\} \\: \texttt{c} \\: \\{ \textrm{false} \\}$ is valid *if and only if* `c` does not terminate.
  If `c` does not terminate, then this triple clearly holds,
  as our definition of partial correctness speaks only about termination.
  Conversely, if this triple is valid, `c` must not terminate,
  as $\textrm{false}$ cannot be true of _any_ final state.



## Rules of Hoare logic

Just like the propositions we defined for operational semantics,
we can define when a Hoare triple is true inductively,
using a set of inference rules.
As a reminder, here's the syntax of IMP, the language our Hoare triples will reason about:

```
cmd := skip
     | var <- expr
     | cmd; cmd
     | if expr then cmd else cmd
     | while expr do cmd
```

As always, to define a proposition over IMP programs, we'll define what happens with each of these constructors.

### Skip is a no-op

First up, `skip`.
Here's the one Hoare logic rule for `skip` programs:
$$
\frac{}
{ \\{ P \\} \\: \texttt{skip} \\: \\{ P \\} } \\: \textrm{HSkip}
$$
This rule is an axiom, telling us something that's always true.
The intuition is that if any property $P$ holds before executing `skip`,
then it continues to hold after executing `skip`,
because `skip` is a no-op -- it doesn't change anything about the state of the program.
In fact, this rule would work for total correctness too, because `skip` always terminates.

### Assignments are substitution

Next up is assignments.
This one's a little funny looking, and probably the most puzzling of the Hoare logic rules,
so we'll spend a little time on it:
$$
\frac{P = P'[e / x]}
{ \\{ P \\} \\: x \texttt{ <- } e \\: \\{ P' \\} } \\: \textrm{HAssign}
$$

First up, we have some new syntax.
$P'[e/x]$ means *substitution*:
in the body of property $P$,
find every occurrance of $x$ and replace it with $e$.
(I always had trouble remembering in which order this substitution happened,
until someone suggested thinking of the $/$ as "falling over" onto $x$—"$e$ squashes $x$"—so $x$ is being replaced with $e$).
For example, $(x = 5)[5 / x]$ is $5 = 5$.
With that syntax in mind, this rule is saying that if we have a postcondition $P'$ that talks about $x$,
we can show that it's true by first proving a different property $P'[e / x]$,
where all the $x$s have been replaced with $e$,
and then in our program assign $e$ to $x$.

A few examples might help bed this idea down:
* $\\{ 5 = 5 \\} \\: x \texttt{ <- } 5 \\: \\{ x = 5 \\}$ is valid by $\textrm{HAssign}$
* $\\{ x+5 = 5 \\} \\: x \texttt{ <- } x+5 \\: \\{ x = 5 \\}$ is valid by $\textrm{HAssign}$
* $\\{ x + 5 > 10 \\} \\: x \texttt{ <- } x + 5 \\: \\{ x > 10 \\}$ is valid by $\textrm{HAssign}$

These might be more obvious if we do a little bit of math simplification in the preconditions:
* $\\{ \textrm{True} \\} \\: x \texttt{ <- } 5 \\: \\{ x = 5 \\}$ is valid
* $\\{ x = 0 \\} \\: x \texttt{ <- } x+5 \\: \\{ x = 5 \\}$ is valid
* $\\{ x > 5 \\} \\: x \texttt{ <- } x + 5 \\: \\{ x > 10 \\}$ is valid

One important note about the second and third examples:
$x$ appears on both sides of the assignment,
but the substitution only happens once.
That is, the result of $(x = 5)[x+5/x]$, which replaces all occurrences of $x$ by $x+5$,
is $x + 5 = 5$, which still has occurrences of $x$ in the result.

### Sequences are composition

The rule for sequences looks similar to big-step operational semantics:
$$
\frac{ \\{ P \\} \\: c_1 \\: \\{ Q \\} \quad\quad \\{ Q \\} \\: c_2 \\: \\{ R \\} }
{ \\{ P \\} \\: c_1 \texttt{; } c_2 \\: \\{ R \\} } \\: \textrm{HSeq}
$$
What we're saying is that to prove a Hoare triple of a sequence $c_1 \texttt{; } c_2$,
we first prove that we can run $c_1$ with some postcondition $Q$,
and then prove that we can run $c_2$ *with $Q$ as a precondition*.
Essentially, we've decomposed the proof into two smaller ones.

### Conditionals and branch conditions

There's only one rule for `if` now, but it has two premises,
one for each side of the branch:
$$
\frac{ \\{ P \land [\\![ e ]\\!] \neq 0 \\} \\: c_1 \\: \\{ Q \\} \quad\quad \\{ P \land [\\![ e ]\\!] = 0 \\} \\: c_2 \\: \\{ Q \\} }
{ \\{ P \\} \\: \texttt{if } e \texttt{ then } c_1 \texttt{ else } c_2 \\: \\{ Q \\} } \\: \textrm{HIf}
$$
Why only one rule?
Unlike operational semantics,
where we were talking about taking a step from a *single state*,
Hoare triples are propositions about *every state* in which the precondition holds.
That means that to prove a Hoare triple about an `if` command,
we must prove it for *both sides* of the branch,
because we don't have a single state that tells us which branch we're going to go down.

In each subproof of $\textrm{HIf}$, we get a precondition that assumes the overall precondition $P$,
but also a *branch condition* that remembers which side of the branch we're in.
These branch conditions are essential for proving interesting triples like this one:
$$
\\{ x = 0 \lor x = 1 \\} \\: \texttt{if } x \texttt{ then } x \texttt{ <- } x + 1 \texttt{ else } x \texttt{ <- } x + 2 \\: \\{ x = 2 \\}
$$
If we didn't have the branch conditions,
the first subproof would look like this:
$$
\\{ x = 0 \lor x = 1 \\} \\: x \texttt{ <- } x + 1 \\: \\{ x = 2 \\}
$$
which is clearly not true. Adding the branch conditions instead requires us to prove only:
$$
\\{ (x = 0 \lor x = 1) \land x > 0 \\} \\: x \texttt{ <- } x + 1 \\: \\{ x = 2 \\}
$$
which we can see is true after a little math (although to prove it formally, we need another rule we haven't seen yet).

### Loops and loop invariants

Finally, we come to the rule for `while` loops,
which moves branch conditions around similar to $\textrm{HIf}$,
but with a twist in terms of what properties it can use as pre- and post-conditions:
$$
\frac{ \\{ I \land [\\![ e ]\\!] \neq 0 \\} \\: c \\: \\{ I \\} }
{ \\{ I \\} \\: \texttt{while } e \texttt{ do } c \\: \\{ I \land [\\![ e ]\\!] = 0 \\} } \\: \textrm{HWhile}
$$
Unlike the other rules,
we no longer have arbitrary properties $P$ and $Q$ as pre- and post-conditions in the conclusion.
Instead, we have only a single property,
which I've suggestively named $I$ because we often call it a *loop invariant*.
$I$ is a property that holds when first reaching the loop,
*and is maintained by every iteration of the loop*.
Eventually, *if* the loop terminates,
the invariant must therefore still hold,
and we also learn the additional condition $[\\![ e ]\\!] = 0$
telling us that we have exited the loop.
In other words, $I$ is invariant no matter how often the loop body iterates (including zero times).

This rule for `while` loops lets us prove triples like this one:
$$
\\{ x \geq 0 \\} \\: \texttt{while } x \texttt{ do } x \texttt{ <- } x - 1 \\: \\{ x \geq 0 \land x = 0 \\}
$$
The subproof we have to do, applying the $\textrm{HWhile}$ rule, is:
$$
\\{ x \geq 0 \land x \neq 0 \\} \\: x \texttt{ <- } x - 1 \\: \\{ x \geq 0 \\}
$$
We actually can't quite prove this triple (more on that in a moment),
but we can prove this one, using $\textrm{HAssign}$:
$$
\\{ x - 1 \geq 0 \\} \\: x \texttt{ <- } x - 1 \\: \\{ x \geq 0 \\}
$$
and, with a little math, these two triples are the same.

### The rule of consequence

In some of the examples we've used so far,
we have taken a few liberties,
saying things like "just use a little math".
But this is a PL class, and we're defining the semantics of a new language here—we should be precise,
even if it's pedantic.
Or put another way,
if we tried to type the inductively defined proposition $\\{ P \\} \\: c \\: \\{ Q \\}$ into Coq,
we certainly can't write "just a little math" in the constructors!
What justification do we have for this handwaving we've been doing?

We need one more rule to help us meld pre- and post-conditions into the forms we want.
It's called the *rule of consequence*, and it looks like this:
$$
\frac{ P \Rightarrow A \quad \\{ A \\} \\: c \\: \\{ B \\} \quad B \Rightarrow Q}
{ \\{ P \\} \\: c \\: \\{ Q \\} } \\: \textrm{HCons}
$$
This is a fascinating rule compared to the others we've seen,
because its premise is about *any* command `c`.
What the rule of consequence does is give us some "wiggle room"
to manipulate the pre- and post-conditions
according to the rules of logic (in this case, over natural numbers).
The way it treats pre- and post-conditions are different, and opposite of each other:
* To prove a triple with precondition $P$, it is OK to *weaken* the precondition to $A$ instead.
  If we can carry out the proof with the weaker $A$ as the precondition, then this is good enough,
  as $A$ will always be true when $P$ is true.
* To prove a triple with postcondition $Q$, it is OK to *strengthen* the postcondition to $B$ instead.
  If we can carry out the proof with the stronger $B$ as the postcondition, then this is good enough,
  as $Q$ will always be true when $B$ is true.

Another way to look at this is using the definition of properties as *sets*
that we saw in [Week 04](@/notes/week04/_index.md).
*Weakening* a property $P$ *increases* the number of states contained in the set to $A \supseteq P$.
If we can prove the Hoare triple starting from all the states in $A$,
we can certainly prove it over the *subset* $P \subseteq A$ of those states.
Symmetrically, *strengthening* a property $Q$ *decreases* the number of states contained in the set to $B \subseteq Q$.
If we can prove that Hoare triple can only end in states in $B$,
we can certainly prove that it can only end in states in $Q \supseteq B$.
In other words: "weaker" means "bigger"—a weaker property is *less specific*, allowing more states;
"stronger" means "smaller"—a stronger property is *more specific*, allowing fewer states.
This is confusing and (for some people, including me) backwards from the way our simple "bigger is stronger" brain wants to think about it.
That's OK! You get more comfortable with it as you go.

A more PL-y way to talk about this,
that you might also have seen in the context of generics in some languages (Java, for example),
is that preconditions are *contra-variant* and postconditions are *co-variant*.
It's analogous to subtyping in these languages:
* Contravariance: if we need to define a method that can take a `Cat` as input,
  it's certainly enough to define one that takes any `Animal` as input—*weakening* the input type.
* Covariance: if we need to define a method that can return an `Animal` as output,
  it's certainly enough to define one that returns only a `Cat`—*strengthening* the output type.

(Personally, I don't find this variance interpretation of the rule of consequence very helpful,
and I, a professional PL researcher, can never keep these two things straight,
but this might help you connect some ideas together).

### A proof of a Hoare triple

Now we have all the rules for Hoare triples for partial correctness.
Let's see how to do a proof with them.
One style is to build a proof tree, like we did in [Week 05](@/notes/week05/_index.md)
for big-step semantics.
I prefer a different style that's a little less unwieldy to work with.
Let's try to prove this triple:
$$
\begin{align}
& \\{ x + y = n \\} \\\\
& \texttt{while y:} \\\\
& \quad\texttt{x = x + 1;} \\\\
& \quad\texttt{y = y - 1 } \\\\
& \\{ x = n \\}
\end{align}
$$

We'd like to get to a place where $\textrm{HWhile}$ applies,
but the postcondition doesn't quite match yet,
so we'll need to rule of consequence.
By a little math, we can see that $x + y = n \land y = 0 \Rightarrow x = n$,
so let's use this stronger postcondition via $\textrm{HCons}$:
$$
\begin{align}
& \\{ x + y = n \\} \\\\
& \texttt{while y:} \\\\
& \quad\texttt{x = x + 1;} \\\\
& \quad\texttt{y = y - 1 } \\\\
& \\{ x + y = n \land y = 0 \\} \\\\
& {\color{blue}\\{ x = n \\}} & {\color{blue}\textrm{by HCons}}
\end{align}
$$
In this proof style, I'll turn things we have proven $\color{blue}\textrm{blue}$,
and leave things we still need to prove $\textrm{black}$.
Our while loop now matches the while rule,
so we can apply $\textrm{HWhile}$:
$$
\begin{align}
& {\color{blue}\\{ x + y = n \\}} \\\\
& \texttt{while y:} \\\\
& \quad\\{x + y = n \land y \neq 0\\} \\\\
& \quad\texttt{x = x + 1;} \\\\
& \quad\texttt{y = y - 1 } \\\\
& \quad\\{x + y = n \\} \\\\
& {\color{blue}\\{ x + y = n \land y = 0 \\}} & {\color{blue}\textrm{by HWhile}} \\\\
& {\color{blue}\\{ x = n \\}} & {\color{blue}\textrm{by HCons}}
\end{align}
$$
The while rule has discharged the outer triple, but left us with a subproof for the body of the loop.
Here there's a couple of different ways to go;
it will be most convenient to use the rule of consequence first
to transform the precondition in a way that will work for the assignment rules:
$$
\begin{align}
& {\color{blue}\\{ x + y = n \\}} \\\\
& \texttt{while y:} \\\\
& {\color{blue}\quad\\{x + y = n \land y \neq 0\\}} & {\color{blue}\textrm{by HCons}} \\\\
& \quad\\{x + 1 + y - 1 = n \\} \\\\
& \quad\texttt{x = x + 1;} \\\\
& \quad\texttt{y = y - 1 } \\\\
& \quad\\{x + y = n \\} \\\\
& {\color{blue}\\{ x + y = n \land y = 0 \\}} & {\color{blue}\textrm{by HWhile}} \\\\
& {\color{blue}\\{ x = n \\}} & {\color{blue}\textrm{by HCons}}
\end{align}
$$
Now we can push the first assignment through the assignment rule,
since $(x + y - 1 = n)[x+1/x]$ is $x + 1 + y - 1 = n$:
$$
\begin{align}
& {\color{blue}\\{ x + y = n \\}} \\\\
& \texttt{while y:} \\\\
& {\color{blue}\quad\\{x + y = n \land y \neq 0\\}} & {\color{blue}\textrm{by HCons}} \\\\
& {\color{blue}\quad\\{x + 1 + y - 1 = n \\}} \\\\
& \quad\texttt{x = x + 1;} \\\\
& {\color{blue}\quad\\{x + y - 1 = n \\}} & {\color{blue}\textrm{by HAssign}} \\\\
& \quad\\{x + y - 1 = n \\} \\\\
& \quad\texttt{y = y - 1 } \\\\
& \quad\\{x + y = n \\} \\\\
& {\color{blue}\\{ x + y = n \land y = 0 \\}} & {\color{blue}\textrm{by HWhile}} \\\\
& {\color{blue}\\{ x = n \\}} & {\color{blue}\textrm{by HCons}}
\end{align}
$$
and similarly for the second assignment,
since $(x + y = n)[y-1/y]$ is $x + y - 1 = n$:
$$
\begin{align}
& {\color{blue}\\{ x + y = n \\}} \\\\
& \texttt{while y:} \\\\
& {\color{blue}\quad\\{x + y = n \land y \neq 0\\}} & {\color{blue}\textrm{by HCons}} \\\\
& {\color{blue}\quad\\{x + 1 + y - 1 = n \\}} \\\\
& \quad\texttt{x = x + 1;} \\\\
& {\color{blue}\quad\\{x + y - 1 = n \\}} & {\color{blue}\textrm{by HAssign}} \\\\
& {\color{blue}\quad\\{x + y - 1 = n \\}} \\\\
& \quad\texttt{y = y - 1 } \\\\
& {\color{blue}\quad\\{x + y = n \\}} & {\color{blue} \textrm{by HAssign}} \\\\
& {\color{blue}\\{ x + y = n \land y = 0 \\}} & {\color{blue}\textrm{by HWhile}} \\\\
& {\color{blue}\\{ x = n \\}} & {\color{blue}\textrm{by HCons}}
\end{align}
$$
and everything has turned blue, so we're done!

### Automated proofs and verification conditions

What's cool about this proof compared to ones we did with small-step operational semantics is that
it's entirely *syntax-guided*:
we did not have to look at the small-step semantics of IMP at all;
instead, we just kept applying whichever Hoare logic rule syntactically matched the program.

Being syntax-guided is great because it allows for *automation*.
We can build a *tool* that just looks at the program, starting from the top,
figures out which rule applies,
and applies it, doing this recursively until the whole program is verified.
If it ever reaches a point where the postcondition of a rule
doesn't match the postcondition of the triple it is trying to prove,
it uses the rule of consequence to strengthen the postcondition.
One such tool is called a *verification-condition generator*—it takes a Hoare triple as input
and return a logical assertion
that is valid if and only if the Hoare triple is valid.
Then we can use a tool like a SAT or SMT solver to validate the assertion.

There are two catches.
First, when applying the rule of consequence,
the generator needs to prove the logical implication part of the rule—that the strengthened
postcondition is indeed stronger than the original one.
The tool can remember these steps as logical assertions to track these obligations.
The second is specific to `while` loops,
for which a syntactic approach doesn't quite work,
because the precondition and postcondition are related—they contain the *loop invariant*.
Notice that most of the weakening and strengthening we did in this proof
was to meld things into the shape of the loop invariant.
This is where automated verification-condition generators most often need external help:
they need to be told what the loop invariant $I$ should be,
and once given those, they can generate the necessary logical assertions
to apply the rule of consequence until the program's pre- and post-conditions fit that shape.

Verification-condition generators are a super fascinating area of formal methods,
though we won't study them more in this class.
They underpin a bunch of cool cutting-edge programming language tools,
including [Dafny](https://github.com/dafny-lang/dafny),
which we *will* study in lecture.

## Soundness of Hoare logic

We've had a good time blasting out some Hoare logic rules,
and convinced ourselves that they *seem* right.
But as PL people we hold ourselves to a higher level of rigor.
How can we *prove* to ourselves that these rules are *sound*—that constructing a proof
using these rules is in fact sufficient to prove a property about an IMP program?

The theorem appeals to the big-step semantics of IMP
(since we care only about terminating programs for partial correctness)
and looks something like this:

**Theorem**: If $\\{ P \\} c \\{ Q \\}$, and $(v, c) \Downarrow v'$, and $P(v)$,
then $Q(v')$.

**Proof**: By induction on the derivation of $\\{ P \\} c \\{ Q \\}$.

There are six cases, one per rule. Most of them are easy and just appeal to the big-step semantics directly. For example, here's the case for $\textrm{HIf}$:

> Suppose the theorem is true for the triples $\\{ P \land [\\![ e ]\\!] \neq 0 \\} \\: c_1 \\: \\{ Q \\}$ and $\\{ P \land [\\![ e ]\\!] = 0 \\} \\: c_2 \\: \\{ Q \\}$.
> We must prove it for the triple $\\{ P \\} \\: \texttt{if } e \texttt{ then } c_1 \texttt{ else } c_2 \\: \\{ Q \\}$.
>
> Let $v$ and $v'$ be states such that $P(v)$ is true, $(v, \texttt{if } e \texttt{ then } c_1 \texttt{ else } c_2) \Downarrow v'$,
> and the triple $\\{ P \\} \\: \texttt{if } e \texttt{ then } c_1 \texttt{ else } c_2 \\: \\{ Q \\}$ is valid.
> By rule inversion, we know that $\\{ P \land [\\![ e ]\\!] \neq 0 \\} \\: c_1 \\: \\{ Q \\}$ and $\\{ P \land [\\![ e ]\\!] = 0 \\} \\: c_2 \\: \\{ Q \\}$
> are also true.
> Now consider two cases:
> * If $[\\![ e ]\\!]_v \neq 0$, then by rule inversion on the $\Downarrow$ rule $\textrm{SIfTrue}$,
>   we know that $(v, c_1) \Downarrow v'$. Then by the inductive hypothesis, we know that $Q(v')$.
> * If $[\\![ e ]\\!]_v = 0$, then by rule inversion on the $\Downarrow$ rule $\textrm{SIfFalse}$,
>   we know that $(v, c_2) \Downarrow v'$. Then by the inductive hypothesis, we know that $Q(v')$.
>
> In both cases, we found that $Q(v')$ holds, and so we are done.

The only interesting case is $\textrm{HWhile}$. 
Let $I$ be a property, and suppose the theorem holds for $\\{ I \land [\\![ e ]\\!] \neq 0 \\} \\: c \\: \\{ I \\}$.
We must prove it for the triple $\\{ I \\} \\: \texttt{while } e \texttt{ do } c \\: \\{ I \land [\\![ e ]\\!] = 0 \\}$.
By rule inversion, we know that $\\{ I \land [\\![ e ]\\!] \neq 0 \\} \\: c \\: \\{ I \\}$ holds.
By the inductive hypothesis, then,
if $v$ and $v'$ are states such that $I(v)$ is true,
$[\\![ e ]\\!] \neq 0$,
and $(v, c) \Downarrow v'$,
then $I(v')$ is also true.

Now we need a small lemma about the invariants:

> **Lemma**: If $(v, \texttt{while } e \texttt{ do } c) \Downarrow v'$ and $I(v)$ then $I(v') \land [\\![ e ]\\!]_v = 0$.
>
> **Proof**: By induction on the derivation of $\Downarrow$.

To finish the proof, suppose $v$ and $v'$ are states such that $I(v)$ is true and $(v, \texttt{while } e \texttt{ do } c) \Downarrow v'$.
Then by the lemma, we get that $I(v') \land [\\![ e ]\\!]_v = 0$,
which is exactly the postcondition of the triple that we needed to prove.
