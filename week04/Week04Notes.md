+++
title = "Week 04 - Transition Systems: Inductive Invariants"
+++

# Week 04 - Transition Systems: Inductive Invariants

_These notes were written primarily by Prof. James Bornholt for his course at
UT Austin. James is a PhD alum of UW and "friend of the channel", and we thank
him for permission to reuse and adapt these notes back at UW!_

We concluded [Week 03](@/notes/week03/_index.md) by seeing some limitations of denotational semantics,
and in particular, we saw that they struggle with non-terminating programs.
We're going to see a solution to this problem in the form of *operational semantics*,
which define the meaning of programs as *transitions* between states.
But before we get there, we need to build up some infrastructure about *transition systems*,
the foundation we'll use to define operational semantics.

## Definition of a transition system

A transition system is (for our purposes) a way to model programs in terms of small *steps* the program can take
through a space of *states* the program can be in.
We'll refine this notion shortly, but for now a rough analogy is to think of a state as "all the variables in the program".
For example, consider this program:
```
x = 5
while True:
    x = x + 1
```
We can model each iteration of this loop as a single *step*,
and the *state* of the program to be the value of variable `x`.
So this program starts in state `5`,
then steps once to state `6`,
steps again to state `7`,
and so on.
In fact, this program continues stepping like this *forever*.
This is a contrast to the challenges we had earlier with denotational semantics—even though this
program never terminates, we can still say things about its behavior at each "step".

What we just did in words is define a **transition system** for this program.
More formally, a transition system is three things:
1. A set of *states* $S$
2. A set of *initial states* $S_0$ such that $S_0 \subseteq S$
3. A *transition relation* $\rightarrow$ over $S \times S$

A quick note on notation: a (binary) *relation* is just a set of pairs of elements.
For example, inequality $a < b$ is a binary relation over the natural numbers;
the relation is the set $\\{ (a, b)\\\: |\\\: a < b \\} \subset \mathbb{N} \times \mathbb{N}$.
In our case,
a transition relation is just a subset of the set $S \times S$ that relates states to other states.
We write $s_1 \rightarrow s_2$ to mean that the pair $(s_1, s_2)$ is in this subset,
and we read this as "$s_1$ *steps to* $s_2$".

Now we can define our informal transition system for the above program a little more formally:
the set $S$ of states is $\mathbb{N}$ (all values that $x$ could take),
the set $S_0$ of initial states is the singleton $\\{ 5\\}$,
and the transition relation is $\rightarrow \\;  = \\{ (n, n+1) \\\: | \\\: n \in \mathbb{N} \\}$.
Notice that this definition is not especially precise;
we can see by inspection that the program can never reach the state `4`,
for example, but $4 \in S$.
Similarly, $(4, 5) \in \\; \rightarrow$ but we know the program can never make that step.
That's OK! Defining these problems away would be fairly easy in this case,
but for general programs it's very hard to write down precise definitions for these sets.
This imprecision doesn't affect the correctness or precision of our transition system when looked at as a whole,
which we can see by having a notion of *reachability*.

### Reachability in a transition system

What are the states that our transition system above can ever arrive at?
This is a useful idea to be able to talk about,
because we often want to state properties about all states.

First, let's extend our notation a little bit to talk about *paths* through the transition system
rather than single steps.
We defined the transition relation $s_1 \rightarrow s_2$ to mean that $s_1$ steps to $s_2$ in exactly one step.
We can introduce a new notation $s_1 \rightarrow^* s_2$ to mean that $s_1$ steps to $s_2$ in *any number of steps*.
Importantly, this *includes zero steps*: $s_1 \rightarrow^* s_1$ is *always true*, but whether $s_1 \rightarrow s_1$ is true depends on the particular transition system. 
We sometimes read $a \rightarrow^* b$ as "$a$ step stars to $b$", or as "$a$ can reach $b$".
(For the formally inclined, $\rightarrow^*$ is the *reflexive transitive closure* of the relation $\rightarrow$.)

For example, in our simple transition system above, we know that $5 \rightarrow 6$ and $6 \rightarrow 7$,
and so we know that $5 \rightarrow^* 7$ (we can step from `5` to `7` in two steps),
but $5 \not\rightarrow 7$ as we cannot reach `7` in exactly one step from `5`.
Note that we haven't yet disposed of our imprecision above:
$1 \rightarrow^* 4$ is true even though neither state is reachable in our actual program,
as all the transition system says is that *starting from state `1`* it is possible to reach `4` (in three steps, in fact).

But now we have the tools we need to define **reachability**:
a state $s$ is *reachable* if there exists an initial state $s_0 \in S_0$ such that $s_0 \rightarrow^* s$.
Now we can dispense with the "imprecise" states:
for example, the state `3` is not *reachable* in our transition system,
because even though there exist some states such that $s \rightarrow^* 3$,
there does not exist any *initial state* where this is true.
On the other hand, the state `7` is reachable in our transition system,
because $5 \rightarrow^* 7$ and $5 \in S_0$.

## Invariants in transition systems

Let's use our definitions to do something interesting.
You probably already have some informal notion of an "invariant" in a program:
a property that is *always true* while the program (or some piece of the program) executes.
Invariants are sometimes written as an assertion.
For example, let's extend our program from earlier with an invariant:
```
x = 5
while True:
    assert x >= 5
    x = x + 1
```
Hopefully it is clear that this assertion is in fact an invariant of this program.
But what does that mean formally?
A **property** of a transition system is just a *set of states* $P \subseteq S$ (equivalently, a predicate over states).
Then an **invariant** of a transition system is a property $I$ such that $R \subseteq I$,
where $R$ is the set of reachable states of the system.
In other words, an invariant is a property is that is true in every *reachable* state of the program.
It might be true in other states, too, but that doesn't matter for invariance; only the reachable states matter.
We sometimes call the set of states that satisfy an invariant the set of "safe" states,
as often invariants are propertys about something that must be true for the program to be "good".

A few examples:
* Our assertion `x >= 5` *is* an invariant of the system:
  the property is $\\{ x \in \mathbb{N} \\\; | \\\; x \geq 5 \\}$,
  and every reachable state is contained in this set.
* The property $even(x) \equiv x \\; \textrm{mod} \\; 2 = 0$ on the natural numbers is the set $\\{ 0, 2, 4, 6, ... \\} \subseteq \mathbb{N}$.
  But $even$ is *not* an invariant of our example transition system,
  as there are reachable states (e.g., 7) that do not satisfy it;
  more formally, $7 \in R$ but $7 \not\in I$.
* The assertion `x != 4` is an invariant.
  While there exists states where this property does not hold,
  none of these states are reachable by the system.

On the surface, this whole idea of invariance seems a bit silly—why not just take the set of reachable states $R$
as the only important invariant of the system?
The trick is that $R$ is often very difficult to characterize precisely.
Instead, we can write down a simpler invariant that includes some unreachable states,
but suffices to prove whatever property we care about.
(This is similar to the "strengthening the inductive hypothesis" idea we've seen before).

### Proving invariants by induction

How to we *prove* that a property is an invariant of a transition system?
As is often the case in PL, we'll do it by induction.
In particular, the trick is to induct over *paths* through the program.
Let's try it out first,
and then below we'll see why it works
and how to relate it to the formalization of induction we developed early in the semester.

**Theorem**: `x >= 5` is an invariant of the example system above.

**Proof**: By induction on $\rightarrow$. There are two cases:

* Base case: in the initial state $s_0$, `x = 5 >= 5`, so the invariant holds
* Inductive case: Suppose the invariant holds in state $s$. Then we need to prove that it holds for every
  state $s'$ such that $s \rightarrow s'$. By the definition of $\rightarrow$, there is only one such
  state for this system: $s \rightarrow s + 1$. But we know by the inductive hypothesis that $s \geq 5$, and so it must be
  that $s + 1 \geq 5$ too. Therefore the invariant holds for all states that $s$ can step to.

What we did here was induct over paths through the program,
or equivalently, induct over the set of reachable states.
The base case just required us to show that the property holds in every initial state.
The inductive hypothesis asked us to consider a state $s$ in which the property holds,
and show that every state we can *step* to from $s$ maintains the property.
Then, by induction,
the invariant holds in every reachable state,
as our proof has covered the initial state $s_0$
and every state $s'$ such that $s_0 \rightarrow^* s'$.

But there is a big catch to this approach!
Let's try do the same proof again for the property `x != 4`,
which is obviously an invariant of our program.

**Theorem**: `x != 4` is an invariant of the example system above.

**Proof attempt**: By induction on $\rightarrow$. There are two cases:

* Base case: in the initial state $s_0$, `x = 5 != 4`, so the invariant holds
* Inductive case: Suppose the invariant holds in state $s$. Then we need to prove that it holds for every
  state $s'$ such that $s \rightarrow s'$. By the definition of $\rightarrow$, there is only one such
  state for this system: $s \rightarrow s + 1$. By the inductive hypothesis, we know that $s \neq 4$.
  But we're stuck now—we can't prove that $s + 1 \neq 4$ with this inductive hypothesis.
  Indeed, $s = 3$ is a counterexample.

What gives? This invariant is obviously true,
but we cannot prove it by induction because *the inductive hypothesis is too weak*.
We call an invariant an **inductive invariant** if it can be proven by induction like this.
But **not all invariants are inductive**!

This is the same idea we've seen before about needing to strengthen the inductive hypothesis.
Here we need to strengthen the *invariant* into one that is an *inductive invariant*,
and then use that stronger invariant to prove the actual invariant we wanted.

Strengthening invariants is a skill; it's not mechanical, and while there has been some really exciting
recent work to automatically determine inductive invariants of a program, it's a difficult problem in general.
In this example, we're in luck, because we already proved an invariant `x >= 5`,
and that's strong enough to prove that `x != 4` is an invariant too,
because $x \geq 5 \Rightarrow x \neq 4$.
But in general, this is the hard part of doing PL proofs: coming up with an invariant
that is (a) strong enough to prove the thing we actually wanted, and yet
(b) is an *inductive* invariant.

### A more interesting example system

Here's another program that is a bit more complicated:
```
n = input()
x = 0
y = n
while y > 0:
    x = x + 1
    y = y - 1
assert x == n
```
where here `n` is some arbitrary input provided by the user.

Let's first translate this program into a transition system. 
Again, we'll take each iteration of the loop to be a single step of the program.
This time, let's broaden our horizons a little and model *integers* rather than just natural numbers.
Our system looks like this:
* The set of states is $S = \mathbb{Z} \times \mathbb{Z}$, where we'll use the first element of the pair for `x` and the second for `y`.
* The initial states are $S_0 = \\{ (0, n) \\\; | \\\; n \in \mathbb{Z} \\}$, since `n` is provided by the user, there are many possible initial states.
* The transition relation $\rightarrow$ is the set $\\{  ((x, y), (x + 1, y - 1)) \\\; | \\\; x, y \in \mathbb{Z} \\}$.

We'd like to prove that at the end of the program,
the assertion holds.
Be careful here: `x == n` is certainly not an invariant of this program!
We only want to check this property at the *end* of the loop.
One way to say this is to state a weaker property $y = 0 \Rightarrow x = n$.
If we can prove this property is an invariant of the system,
we will know that our assertion holds,
as it tells us what must be true *at the end of the loop*.

We can try to prove this is an inductive invariant,
but skipping ahead to the inductive case,
we will find a counterexample:
if $n = 2$, the state $(0,1)$ is in $S$,
and $(0,1) \rightarrow (1,0)$,
but $(1, 0)$ does not satisfy the property.

Again, this doesn't mean the property is not an invariant,
just that it's not an *inductive invariant*.
We will need to proceed by strengthening our invariant.
We're looking for an invariant that does two things:
(1) is inductive, and (2) can be used to prove the original invariant.
Again, strengthening invariants is a *skill* that needs practice and experimentation;
there's not really a mechanical way to look at this problem and crank out the invariant we need.

I happen to know that the invariant we're looking for is `n = x + y`.
This is certainly enough to prove our original invariant: if $n = x + y$ and $y = 0$, then it must be that $x = n$.
But can we prove it's an inductive invariant? Yes!

**Theorem**: `n = x + y` is an invariant of the system above.

**Proof**: By induction on $\rightarrow$. There are two cases:

* Base case: let $s = (0, n) \in S_0$ be an initial state. Then $x + y = 0 + n = n$, so the invariant holds.
* Inductive case: Suppose the invariant holds in state $s = (x, y)$, so we know that $x + y = n$.
  Then we need to prove that it holds for every
  state $s'$ such that $s \rightarrow s'$. By the definition of $\rightarrow$, there is only one such
  state for this system: $(x, y) \rightarrow (x + 1, y - 1)$. 
  But $(x + 1) + (y - 1) = x + y$, and by the inductive hypothesis we know that $x + y = n$,
  so we therefore know that the invariant holds for $s'$ if it holds for $s$.

Now we're done: we know that $n = x + y$ is an invariant,
and that implies that $y = 0 \Rightarrow x = n$ is an invariant,
and that in turn implies that when we exit the loop in the program,
the assertion holds!

## Inductively Defined Propositions

Let's wrap up by putting this "induction over $\rightarrow$" principle onto some more solid footing.
In [Week 01](@/notes/week01/_index.md) we talked about inductive sets,
and saw how we can use induction over inductive sets to prove a property for every member of the set.

It turns out that the induction principle we were using above is just an instance of this same pattern.
In particular, what we were doing was inducting over the *proposition* $\rightarrow^* $.
To see what that means, let's write down a definition of $\rightarrow^*$ as two inference rules,
similar to what we did for inductive sets in Lecture 1:

$$
\frac{}{s \rightarrow^* s} \textrm{ (base case)}
$$

$$
\frac{s_1 \rightarrow s_2 \quad\quad s_2 \rightarrow^* s_3}{s_1 \rightarrow^* s_3} \textrm{ (inductive case)}
$$

In words, what we're saying here is:
1. $s$ can always reach itself (the base case).
2. If $s_1$ can take one step to $s_2$ and then $s_2$ can reach $s_3$, then $s_1$ can reach $s_3$ as well.

What we've done here is define an *inductive proposition*.
A *proposition* is a statement that can be true or false;
here, the statement is "$s_1$ can reach $s_2$".
We're saying that there are two ways this proposition can be true:
either the trivial case $s_1 = s_2$,
or the inductive case where we can "add one more step" to an existing reachability proposition.

Now our induction principle should be a little more clear.
To do induction over an inductive proposition,
we first prove every base case proposition.
Then in the inductive case,
we get to assume that the proposition holds for some path,
and need to prove that it holds for every way that we can "add one more step".

This formulation of induction over transition systems is very powerful.
In particular, unlike when we were inducting over program syntax with denotational semantics,
induction over transition systems lets us prove properties of non-terminating programs.
It also makes it much simpler to prove properties even about terminating programs that involve loops
or other repetitive structures that are difficult to define denotationally.
Also, inductive propositions are a great fit for proving in Coq,
which "only knows inductive types"—we'll be able to encode inductive propositions as inductive types
just like we've done before with inductive sets.

## When manual transition systems get difficult

So far we've been defining our transition systems by hand for each program.
It hasn't been all that hard—we just declare all the variables, taken together,
to be the state. But that approach isn't always going to work. Here's an example:

```
x = 0
while x < 5:
    x = x + 1
while x > 0:
    x = x - 1
```

We could try to define a transition system for this program
where the set of states is just $\mathbb{N}$, reflecting the possible values of `x`.
But we'd be in trouble when trying to define the transition relation:
the first loop suggests a relation of $x \rightarrow x + 1$,
while the second suggests $x \rightarrow x - 1$.
This system allows executions that we know aren't possible, like this one:
```
x = 0, x = 1, x = 2, x = 1
```

The problem here is that we need to know "which loop" we're in to know
which transitions are possible. One way to fix that would be to add a boolean
to the state that tracks which loop we're in.
But in general, that's not a great solution.
In the next lecture, we'll see a more general approach that deals with this issue.

