+++
title = "Week 01 - Functional Programming and Proofs: Inductive Types and Recursive Functions"
+++

# Week 01 - Functional Programming and Proofs: Inductive Types and Recursive Functions

_These notes were written primarily by Prof. James Bornholt for his course at
UT Austin. James is a PhD alum of UW and "friend of the channel", and we thank
him for permission to reuse and adapt these notes back at UW!_

Let's start by establishing some foundations for our study of programming languages. We'll see how to define programs as mathematical objects, write functions about them, and do some small proofs about these objects.

## Induction

Reasoning by *induction* is ubiquitous in programming languages formalism, so we'll start by reviewing proofs by (structural) induction.

### Mathematical and strong induction

How do we prove statements that look like "for all natural numbers $n$, $P(n)$ is true"? They're fairly rote: mathematical induction tells us that we need to prove two things:
1. The *base case*: prove $P(0)$.
2. The *inductive case*: assuming $P(k)$ is true for some $k \in \mathbb{N}$, prove $P(k+1)$ is true. We call the assumption part of this case the *inductive hypothesis*.

Let's try this out on a simple theorem: for all natural numbers $n$, prove that $n+1 \leq 2^n$.

**Base case**: $0 + 1 = 1 \leq 2^0 = 1$

**Inductive case**: suppose that $k + 1 \leq 2^k$ for some $k \in \mathbb{N}$. Then by adding $1$ to both sides, we know $(k + 1) + 1 \leq 2^k + 1$. We also know that $2^k \geq 1$ since $k \in \mathbb{N}$. So we have that:
$$
(k + 1) + 1 \leq 2^k + 1 \leq 2^k + 2^k = 2^{k+1}.
$$

Induction is a great proof technique because it lets us prove something about *infinite* cases (*all* the natural numbers) by only inspecting *finitely many* cases. This is also what makes it a great tool for reasoning about programs — there are infinitely many programs, but we don't want to look at every single one — but we'll get to that later.

Let's try another theorem: for all positive integers $n$ greater than $1$, $n$ is a product of prime numbers.

**Base case**: $n = 2$ is a prime number.

**Inductive case**: Suppose that $k \geq 2$ can be written as $k = p_1p_2 \dots p_m$, where each $p_i$ is prime. Then there are two cases for $k+1$:

1. If $k+1$ is prime, we're obviously done (and didn't need the inductive hypothesis at all).
2. Otherwise, $k+1$ is composite, so we know that $k+1 = ab$ where $1 < a, b < k+1$. ... [we're stuck! What we need to be able to do is apply the inductive hypothesis to $a$ and $b$, but we only know it for $k$]

We can get out of this hole by generalizing mathematical induction a little to something called *strong induction* that gives us a stronger induction hypothesis. A strong induction proof looks like this:

1. The *base case*: prove $P(0)$
2. The *inductive case*: assuming $P(m)$ is true for *every* $0 \leq m \leq k$, prove $P(k+1)$ is true.

So now, to fix our proof, we can apply strong induction to get a stronger induction hypothesis.

**Inductive case**: suppose that *every* $2 \leq m \leq k$ is a product of primes. Then there are two cases for $k+1$:

1. If $k+1$ is prime, we're obviously done (no change here).
2. If $k+1$ is composite, we know that $k+1 = ab$ where $1 < a, b < k+1$. But by the inductive hypothesis, since $a, b \leq k$, we know that $a = a_1a_2\dots a_n$ and $b = b_1b_2 \dots b_l$, where all the $a_i$s and $b_i$s are primes. Therefore $k+1 = a_1a_2\dots a_n b_1b_2 \dots b_l$ is a product of primes.

### Structural induction

What's special about the natural numbers that makes induction work here? We can generalize a bit more to *structural induction* that works on any *inductive definition*.

An *inductive definition* (or a *recursive definition*, or an *inductive set*) is a set $A$ described by a finite collection of base and inductive cases:

* *Base cases* have no premise and are just universally true: $a \in A$.
* *Inductive cases* have premises and are true whenever the premises are true: if $a_0 \in A$, ..., $a_n \in A$, then $a \in A$.

In other words, an inductive definition gives us a way to build up a bigger set from a smaller one — we start with the base cases and then add more elements using the inductive cases.

This is a convenient time to introduce some common programming languages notation. An *inference rule* is a way of writing these base and inductive cases. Inference rules are written with horizontal lines: everything above the horizontal line is a *premise*, and the single thing below the line is a *conclusion*. So we can write our base and inductive cases above like this:
$$
\frac{}{a \in A} \texttt{ (base case)}
$$

$$
\frac{a_0 \in A \quad \dots \quad a_n \in A}{a \in A} \texttt{ (inductive case)}
$$
We'll sometimes call inference rules with no premises *axioms*, and others *inductive rules*.

The *structural induction principle* on a inductive set $A$ is just an induction proof that operates on each inference rule that defines $A$:
- Axioms correspond to base cases — we prove that $P$ holds for each axiom
- Inductive rules correspond to inductive cases — we assume that $P$ holds for each premise, and prove that this implies $P$ holds for the conclusion.

#### Structural induction on the natural numbers

We can tie this new definition back to our induction principles on the natural numbers by observing that *the natural numbers are an inductive set*, defined by two inference rules:

$$
\frac{}{0 \in \mathbb{N}} \quad \frac{n \in \mathbb{N}}{succ(n) \in \mathbb{N}}
$$

Here, $succ(n)$ is the *successor* of $n$ — the *next* natural number after $n$. Notice that this definition doesn't mention addition ($n + 1$) at all, because $1$ doesn't exist anywhere in the definition. The way to read this definition is: zero is a natural number, and the successor of a natural number is also a natural number. So:
- 0 is a natural number axiomatically
- $succ(0)$ is a natural number (1) by applying the inductive rule to 0
- $succ(succ(0))$ is a natural number (it's 2)
- $succ(succ(succ(0)))$ is a natural number (it's 3)
- ... and so on.
  
This axiomatization of the natural numbers is due to [Giuseppe Peano](https://en.wikipedia.org/wiki/Giuseppe_Peano), circa 1889, and so is often called the [*Peano axioms*](https://en.wikipedia.org/wiki/Peano_axioms).

Notice now that if you just apply these rules to our definition of the natural numbers, you get back exactly mathematical induction. In other words, *mathematical induction is just structural induction on the natural numbers*.

We'll try a structural induction proof on the natural numbers in just a moment, but first we need one more concept.

## Algebraic data types

So far, we've seen natural numbers in both the mathematical formulation you're used to, and in this new inductive definition style. There's one more lens we can look at them through, and that's as an *algebraic data type* (ADT).

When we defined the natural numbers with inference rules, we abandoned our usual syntax of labeling them 0, 1, 2, etc. Instead, we wrote them as 0, succ(0), succ(succ(0)), etc. There's some sort of pattern in the syntax here, and in fact we could *define* the natural numbers using this syntactic pattern.

At some high level, an algebraic data type is like defining a *grammar* for the *syntax* of an inductive definition. So for the natural numbers, we can declare an ADT called `nat` that looks like this:

```
nat := zero | succ nat
```

We call `zero` and `succ` here *constructors*. They're not exactly *functions*—these are purely syntactic constructs—but they do take arguments. `zero` takes no arguments, which tells us that it's an axiom or a base case—`zero` is always a natural number. `succ` takes one argument, which is another natural number.

In other words, we get the same idea we had from the inference rules—zero is a natural number, and the successor of a natural number is also a natural number. So:

- `zero` mean 0
- `succ zero` means 1
- `succ (succ zero)` means 2
- `succ (succ (succ zero))` means 3
- ...

(Again, these are not function applications, just syntactic objects—there is no "evaluation" going on here. We'll get to that later.)

### Functions on ADTs

ADTs are a nice way to look at inductive sets because they let us easily define functions on the set and then do proofs about those functions.

Notice how our ADT definition of `nat` (and our inference rule version, too) says nothing about addition, or about any symbols except `zero` and `succ`. Of course, the mathematical natural numbers have a rich structure attached to them. But since we're working on the ADT now, we can see how to reconstruct that structure ourselves. Peano did all the hard work for us here, so let's return to his axiomatization.

Here's a simple mathematical definition of addition over natural numbers:
$$
add(m, n) = \begin{cases}n \& m = 0 \\\\
succ(add(k, n)) & m = succ(k)\end{cases}
$$
We're defining addition as a piecewise function based on the first argument `m`. If `m` is `zero`, then `add(m, n)` is just `n`. Otherwise, `m` must be `succ(k)` for some natural number `k`, and we can add them together by first adding `k` and `n`, and then taking the `succ` of that result. In the math syntax we're used to, we're saying:
$$
m + n = \begin{cases}n \& m = 0 \\\\ (k + n) + 1 & m = k + 1\end{cases}
$$

Let's try writing this same definition again, but this time using the ADT version of natural numbers. We can write the function as a *pattern match* on the first argument:
```
add zero     n = n
add (succ k) n = succ (add k n)
```
What we've done here is define a *function* called `add`. We've written the two cases as two separate pieces of the definition. If the first argument is `zero`, we return the second argument. If the first argument is `succ k`, we return `succ (add k n)`—first computing `add k n` (which means "apply the function add to arguments `k` and `n`; you probably write this as `add(k, n)` in other languages), and then applying the `succ` constructor to it.

This same pattern works to define *any* function that takes a `nat`—we have to define what happens when the argument is `zero`, and what happens when the argument is `succ n`. In the `succ` case, that definition almost certainly refers to `n`, and it likely recurses too. We call functions like `add` "total", in that they are defined for every constructor of the `nat` ADT`.

(Aside: we skipped over any consideration of *termination*—how do we know our function is well defined and doesn't just keep recursing forever? The intuition is that the recursion is only invoked on arguments of the constructors, and so each recursive call is "getting smaller". This notion is sometimes called "primitive recursion". It's one way—but certainly not the only way—to guarantee termination.)

This is the same as our mathematical formulation, just written as a *functional program*. We're going to be seeing, and writing, a lot of these definitions in this class. We'll get more hands-on with this sort of functional programming shortly.

### Proofs on ADTs

Let's try writing a proof about our new `add` function. Again, we're reconstructing all the structure we know about for natural numbers, so even obvious things deserve a little pedantry. Let's prove this:

**Theorem**: For all `nat`s `n`, `add n zero = n`.

Just like defining functions on ADTs requires defining them for each constructor, proofs about ADTs require proofs for each constructor. If the definition involves recursion, the proof almost certainly involves induction on the ADT.

**Proof**: We'll use structural induction on `n`. There are two constructors, so two cases we need to consider:

1. (Base case) If `n = zero`, then `add zero zero` = `zero`.
2. (Inductive case) If `n = succ k`, then:
   ```
   add (succ k) zero = succ (add k zero)
                     = succ k
   ```
   where the second step follows from the inductive hypothesis on `k`.

The big takeaway is this: **if the function is defined by recursion, the proof is probably by induction**. We're going to see this *all the time*—many programming languages ideas are defined by recursion, and therefore many programming languages proofs proceed by induction. We're going to get very good at induction!

But! Note that induction is not *always* necessary for ADTs. Here's a silly example: let's define a "sign" function for natural numbers.
```
sign zero     = zero
sign (succ n) = succ zero
```
In other words, the sign of 0 is 0, and the sign of all other natural numbers is 1. Here's an equally silly theorem and proof about `sign`.

**Theorem**: for all `nat`s `n`, `sign n` is either `zero` or `succ zero`.

**Proof**: by case analysis on `n`:

1. If `n = zero` then `sign zero = zero`.
2. If `n = succ k` for some `k`, then `sign n = sign (succ k) = succ zero`.

We didn't need induction here because *the function doesn't recurse on the inductive definition*. Note that a proof by induction *would have worked* here, but it would be overkill—the inductive case would never need to use the inductive hypothesis. Instead, a simple case analysis suffices. So the corollary to our "big takeaway" is that **proofs follow the structure of the definition**—if the definition doesn't use recursion, the proof probably doesn't need induction.


#### Booleans

Let's look at one degenerate case of ADTs, the booleans. There are two constructors for booleans, both of which take no arguments:

```
bool := true | false
```

In other words, there's no recursive structure to the booleans, just two base values. We can write this same ADT as inference rules:

$$
\frac{}{true \in bool} \quad \quad \frac{}{false \in bool}
$$

Be very careful here: the conclusions of these rules are that the syntactic objects `true` and `false` are booleans. It would be wrong to write this:

$$
\frac{}{true}  \quad \quad \frac{}{false}
$$

which is trying to treat these syntactic objects as propositions. If you read inference rules as implications (a reasonable way to think about them), the first one is obviously valid, and the second one is obviously invalid.


## Wrap up

That's it for this lecture! We've reviewed structural induction and introduced algebraic data types.

The most important thing to remember is **the symmetry between definition and proof**. When trying to decide how to do a proof, follow the structure of the definitions.

