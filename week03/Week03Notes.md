+++
title = "Week 03 - Arith: Abstract Syntax; Semantics via Interpreters"
+++

# Week 03 - Arith: Abstract Syntax; Semantics via Interpreters

_These notes were written by primarily by Prof. James Bornholt for his course at
UT Austin. James is a PhD alum of UW and "friend of the channel", and we thank
him for permission to reuse and adapt these notes back at UW!_

In [Week 02](@/notes/week02/_index.md), we learned that any formalization of a programming language
has two components:
1. **Syntax** defines what programs *are*—their "shape" or "structure".
2. **Semantics** defines what programs *mean*—how they behave, how they evaluate.

We saw that we can represent the syntax of a program as an *abstract syntax tree* (AST),
an algebraic data type that reflects the shape of the program.
Syntax is, for our purposes, the "easy" part of defining a programming language—ASTs strip away
many of the complexities of modern programming language syntax and leave us with a simple essence.
Most compilers use some sort of AST or other *intermediate representation* to separate syntax from semantics.

This lecture starts our exploration of *semantics*, the "hard" part of defining a programming language.
Broadly speaking, there are three established techniques for defining the semantics of a programming language:
1. *Denotational semantics* defines a program's meaning using mathematical functions
2. *Operational semantics* defines a program's meaning using transitions between states of an abstract machine
3. *Axiomatic semantics* defines a program's meaning in terms of logical assertions satisfied during execution

None of these techniques is the "right one"; they each have pros and cons,
and often a formalization will combine more than one of these approaches. We're going to spend the
next few weeks studying each of these approaches in some detail.
The goal is for you to be able to identify when each model of semantics is useful
*and* to be able to do proofs about all three styles.

This lecture covers *denotational semantics*, which (in my opinion) is the simplest of the three approaches,
but also has the most limitations. Nonetheless, it can be a very useful tool for reasoning about programs,
especially those in functional programming languages or that are otherwise recursion-oriented.

## An interpreter for expressions

In the last lecture we defined a simple expression language as an ADT. Let's look at an even simpler
version of that expression language:

```
expr := Const nat
      | Plus expr expr
      | Times expr expr
```

We know that syntactically, these two programs are not equal:
1. `Plus (Const 1) (Const 1)`
2. `Const 2`

But any intuitive semantics for this language should have them *evaluate* to the same result.
Let's see how we can define a semantics that ensures this equivalence.

A **denotational semantics** for a programming language is a function $D: \mathrm{Syntax} \rightarrow \mathrm{Semantics}$
that takes as input a program syntax (for us, that means an AST)
and returns a value (sometimes called a *denotation*) that the program evaluates to.
In other words, a denotational semantics defines meaning as a function over the program's AST,
in the same sense as we were defining functions over ADTs in the previous lecture.

For our `expr` language, such a function might look like this:
$$
D(e) = \begin{cases}
    n        & e = \texttt{Const } n \\\\
    D(e_1) + D(e_2) & e = \texttt{Plus } e_1\ e_2 \\\\
    D(e_1) \times D(e_2) & e = \texttt{Times } e_1\ e_2 \\\\
\end{cases}
$$
As with every other function we've defined over an ADT, we define a case for each constructor.
The function recurses to evaluate sub-expressions, and then applies the mathematical $+$ and $\times$ operations when necessary.

A semantics like this one is often called an **interpreter**—it takes as input a program
and *interprets* it to evaluate its meaning. Interpreters are really handy for a bunch of reasons,
and are especially well suited to implementation in functional programming languages,
as we'll see in the next couple of lectures.

A note on notation: denotational semantics are very common in programming languages,
so common that we have a short-hand notation for them using $\[\\![ \cdot ]\\!]$ brackets, like this:
$$
\begin{align}
\[\\![ \texttt{Const } n ]\\!] &= n \\\\
\[\\![ \texttt{Plus } e_1\ e_2 ]\\!] &= \[\\![ e_1 ]\\!] + \[\\![ e_2 ]\\!] \\\\
\[\\![ \texttt{Times } e_1\ e_2 ]\\!] &= \[\\![ e_1 ]\\!] \times \[\\![ e_2 ]\\!]
\end{align}
$$

Now we can see that our two programs above, while not syntactically equal, do *evaluate* to the same thing:
$$
\begin{align}
\[\\![ \texttt{Plus (Const 1) (Const 2)} ]\\!] &= \[\\![ \texttt{Const 1} ]\\!] + \[\\![ \texttt{Const 1} ]\\!] \\\\
&= 1 + 1 \\\\
&= 2 \\\\
\[\\![ \texttt{Const 2} ]\\!] &= 2
\end{align}
$$

## Proofs with denotational semantics

Now that we know how to assign programs meaning via a denotational semantics,
we can do proofs *about* programs, rather than the proofs about program syntax we saw last time.
Let's try a simple one: we know that addition and multiplication are commutative,
so we should be able to flip the arguments to `Plus` and `Times` operations without changing how the program evaluates.

Here's a function that implements our "flip" operation:
```
flip (Const n) = Const n
flip (Plus e1 e2) = Plus (flip e2) (flip e1)
flip (Times e1 e2) = Times (flip e2) (flip e1)
```

We can use the denoational semantics to state and prove our theorem that `flip` doesn't affect evaluation:

**Theorem**: for all expressions `e`, $\[\\![ e ]\\!] = \[\\![ \texttt{flip}\ e ]\\!]$.

**Proof**: by induction on `e`. There are three cases:
1. (Base case for `Const`) By definition of `flip`, $\[\\![ \texttt{flip}\ (\texttt{Const}\ n) ]\\!] = \[\\![ \texttt{Const}\ n ]\\!]$.
2. (Inductive case for `Plus`) Suppose that $\[\\![ e_1 ]\\!] = \[\\![ \texttt{flip}\ e_1 ]\\!]$ and likewise for $e_2$. We need to show
that $\[\\![ \texttt{Plus}\ e_1\ e_2 ]\\!] = \[\\![ \texttt{flip}\ (\texttt{Plus}\ e_1\ e_2) ]\\!]$. Let's start by manipulating the RHS:
$$
\begin{align}
RHS = \[\\![ \texttt{flip}\ (\texttt{Plus}\ e_1\ e_2) ]\\!] &= \[\\![ \texttt{Plus}\ (\texttt{flip}\ e_2)\ (\texttt{flip}\ e_1) ]\\!] \\\\
&= \[\\![ \texttt{flip}\ e_2 ]\\!] + \[\\![ \texttt{flip}\ e_1 ]\\!] \\\\
&= \[\\![ e_2 ]\\!] + \[\\![ e_1 ]\\!] \\\\
&= \[\\![ e_1 ]\\!] + \[\\![ e_2 ]\\!] \\\\
&= LHS
\end{align}
$$
where the first line is by the definition of `flip`,
the second and fifth lines are by the definition of $\[\\![ \texttt{Plus}\ e_1\ e_2 ]\\!]$,
the third line is by the inductive hypotheses,
and the fourth line is by commutativity of $+$.
3. (Inductive case for `Times`) This case is identical to the `Plus` case.

This is our first real proof about *programs* and what they *mean*.
Notice how all the tools we've seen so far this semester came together here:
* We used ADTs to define program syntax, so that we didn't have to reason about programs as strings like compilers do
* We used proof by induction to prove a property for *every* program, not just a few programs
* Denotational semantics gave us a mathematical way to define the behavior of our langauge that was amenable to proofs

## Interpreters with state

Let's look at a very different programming language now:
a *stack machine* whose instructions manipulate a stack.
This one will require two ADTs, one for instructions and one for programs:
```
instr := Push nat
       | Add
       | Multiply

prog := nil 
      | cons instr prog
```
Notice that the `prog` ADT is just a list of instructions, the same as the list ADT we studied in [Week 02](@/notes/week02/_index.md).

To get a feel for how this machine works,
let's write a program `p` that adds 1 and 2 together.
We'll use list syntax to make our lives a little easier here:
```
p = [Push 1, Push 2, Add]
```
The two push instructions push constants onto a stack.
The add instruction pops the top two values off the stack,
adds them together, and pushes the result back onto the stack.
So, at the end of this program,
we should have a stack with just one value `3` on it.

To make this definition formal, let's write a denotational semantics, first for our `instr` ADT:
$$
\begin{align}
\[\\![ \texttt{Push } n ]\\!]\(s) &= \texttt{cons}\ n\ s \\\\
\[\\![ \texttt{Add} ]\\!]\(\texttt{cons}\ n_1\ \texttt{(cons}\ n_2\ s\texttt{)}) &= \texttt{cons}\ (n_1 + n_2)\ s \\\\
\[\\![ \texttt{Multiply} ]\\!]\(\texttt{cons}\ n_1\ \texttt{(cons}\ n_2\ s\texttt{)}) &= \texttt{cons}\ (n_1 \times n_2)\ s \\\\
\end{align}
$$

Here each denotation is itself a *function* that transforms a stack—it takes one stack as input and returns a stack reflecting the effect of the instruction.
We are using a list ADT to model stacks.
The `Push` semantics just pushes onto the stack using `cons`.
The `Add` and `Multiply` semantics take the top two elements from the stack,
add or multiply them together,
and push the result back onto the stack.

Notice that we only defined `Add` and `Multiply` for stacks that have at least two elements on them.
For this discussion it won't matter what we do with cases where this isn't true,
but there are several reasonable choices.

Now we can define the denotational semantics for entire programs:
$$
\begin{align}
\[\\![ \texttt{cons}\ i\ p ]\\!]\(s) &= \[\\![ p ]\\!]\(\[\\![ i ]\\!]\(s)) \\\\
\[\\![ \texttt{nil} ]\\!]\(s) &= s
\end{align}
$$
What we're doing here is taking the *composition* of each instruction's effect on the stack.
For example, to run the program `p` above, we can start from the empty stack, like this:
$$
\begin{align}
\[\\![ [\texttt{Push}\ 1, \texttt{Push}\ 2, \texttt{Add}] ]\\!]\([]) &= \[\\![ [\texttt{Push}\ 2, \texttt{Add}] ]\\!]\(\[\\![ \texttt{Push}\ 1 ]\\!]\([])) \\\\
&= \[\\![ [\texttt{Push}\ 2, \texttt{Add}] ]\\!]\([1]) \\\\
&= \[\\![ [\texttt{Add}] ]\\!]\(\[\\![ \texttt{Push}\ 2 ]\\!]\([1])) \\\\
&= \[\\![ [\texttt{Add}] ]\\!]\([2, 1]) \\\\
&= \[\\![ [] ]\\!]\(\[\\![ \texttt{Add} ]\\!]\([2, 1])) \\\\
&= \[\\![ [] ]\\!]\([3]) \\\\
&= [3]
\end{align}
$$

## Proofs about compilers

We can use the tools we've developed so far to write a simple *compiler*
that translates arithmetic `expr`s to stack machine `prog`s.
Even better: we can use our denotational semantics to *prove that compiler correct*!
Compilers are incredibly important infrastructure for modern computing,
so being able to give strong guarantess like this is a huge win,
and verified compilers like [CompCert](https://compcert.org) are a flagship example of the success of programming languages research.

As always, our compiler is just a function over an ADT,
so we define what happens to each constructor.
Remember that `prog` is just the list ADT,
so the right-hand side of our `compile` function will be returning lists of `instr`s.
```
compile (Const n) = [Push n]
compile (Plus e1 e2) = compile e1 ++ (compile e2 ++ [Add])
compile (Times e1 e2) = compile e1 ++ (compile e2 ++ [Times])
```
where here I'm writing `++` for the `append` operation on lists.
Try running this compiler on the expression `Plus (Const 1) (Const 2)`
to see that it results in the same `prog` as the `p` example we saw above.

What does it mean for `compile` to be correct?
Intuitively, we'd like it to preserve the semantics of the program it compiles.
Using our denotational semantics,
we can formalize that intuition a little:
the original and compiled programs should denote to the same value.
There's a minor catch: the stack language denotations start with and return *stacks*,
whereas the expression language denotations return *values*.
We can work around this by just declaring that the *top of the stack* is the "return value" of a stack program,
and that our execution starts with an empty stack.
In other words, here's our theorem:

**Theorem**: for all `expr`s `e`, $\[\\!\[ \texttt{compile}\ e \]\\!\]([]) = [\ \[\\![ e ]\\!]\ ]$.

**Proof**: by induction on `e`. There are three cases:
1. (Base case for `Const`)
$$
\begin{align}
\[\\![ \texttt{compile}\ (\texttt{Const}\ n) ]\\!]\([]) &= \[\\![ [\texttt{Push}\ n] ]\\!]\([]) \\\\
&= \[\\![ [] ]\\!]\(\[\\!\[ \texttt{Push}\ n \]\\!\]([]) ) \\\\
&= \[\\![ [] ]\\!]\( [n] ) \\\\
&= [n] \\\\
[\ \[\\![ \texttt{Const}\ n ]\\!]\ ] &= [n]
\end{align}
$$
2. (Inductive case for `Plus`) Suppose that $\[\\!\[ \texttt{compile}\ e_1 ]\\!]([]) = [\ \[\\![ e_1 ]\\!]\ ]$
and similar for $e_2$. We need to show that $\[\\!\[ \texttt{compile}\ (\texttt{Plus}\ e_1\ e_2) ]\\!]([]) = [\ \[\\![ \texttt{Plus}\ e_1\ e_2 ]\\!]\ ]$.
Let's start with the left-hand side:
$$
\begin{align}
LHS = \[\\![ \texttt{compile}\ (\texttt{Plus}\ e_1\ e_2) ]\\!]([]) &= \[\\![ \texttt{compile}\ e_1\ \texttt{++}\ (\texttt{compile}\ e_2\ \texttt{++}\ [\texttt{Add}]) ]\\!]([]) \\\\
&= \[\\![ \texttt{compile}\ e_1\ \texttt{++}\ (\texttt{compile}\ e_2\ \texttt{++}\ [\texttt{Add}]) ]\\!]([]) \\\\
\end{align}
$$
But here we're stuck! To make more progress here, we need to be able to apply our inductive hypothesis,
but notice that it only talks about $\[\\![ \texttt{compile}\ e_1 ]\\!]([])$,
whereas we need to talk about the semantics when `compile e1` has more stuff appended to it.
If we look further ahead, we'll see another issue:
once the program `compile e1` has executed, we'll have a non-empty stack and `compile e2` to reason about next,
but the inductive hypothesis only talks about `compile e2` running on empty stacks.

There is actually no way to make this induction work as is! To make progress, we need to **strengthen the inductive hypothesis** somehow.
This is a very common requirement in PL proofs.
In this case, we'll need to state and prove a stronger, more complicated lemma relating our two languages.
It looks like this:

**Lemma**: for all `expr`s `e`, `prog`s `p`, and stacks `s`, $\[\\![ \texttt{compile}\ e\ \texttt{++}\ p ]\\!](s) = \[\\![ p ]\\!](\texttt{cons}\ \[\\![ e ]\\!]\ s)$.

Notice this is a generalization of our original theorem.
In words, it says that running the compiled version of any single `expr` `e`
on a stack `s` and then running the rest of a program `p`
is the same as evaluating `e` and then running `p` on the stack `s` *but* with the result of the evaluation on top.

**Proof**: by induction on `e`. There are three cases:
1. (Base case for `Const`) Let `p` and `s` be arbitrary. Then:
$$
\begin{align}
\[\\![ (\texttt{compile}\ (\texttt{Const}\ n))\ \texttt{++}\ p ]\\!](s) &= \[\\![ [\texttt{Push}\ n]\ \texttt{++}\ p ]\\!](s) \\\\
&= \[\\![ p ]\\!]\(\[\\!\[ \texttt{Push}\ n \]\\!\](s) ) \\\\
&= \[\\![ p ]\\!]\( \texttt{cons}\ n\ s ) \\\\
&= \[\\![ p ]\\!]\( \texttt{cons}\ \[\\![ \texttt{Const}\ n ]\\!]\\ s )
\end{align}
$$
2. (Inductive case for `Plus`) Suppose that *for all* `p` and `s`, $\[\\![ \texttt{compile}\ e_1\ \texttt{++}\ p ]\\!](s) = \[\\![ p ]\\!](\texttt{cons}\ \[\\![ e_1 ]\\!]\ s)$,
and similar for $e_2$. (Notice already the difference from our previous attempt: our inductive hypothesis talks about every `p` and `s` now).

   We need to show that $\[\\![ \texttt{compile}\ (\texttt{Plus}\ e_1\ e_2)\ \texttt{++}\ p ]\\!](s) = \[\\![ p ]\\!](\texttt{cons}\ \[\\![ \texttt{Plus}\ e_1\ e_2 ]\\!]\ s)$.
Let's start with the left-hand side:
$$
\begin{align}
LHS &= \[\\![ \texttt{compile}\ (\texttt{Plus}\ e_1\ e_2)\ \texttt{++}\ p ]\\!](s) \\\\
&= \[\\![ (\texttt{compile}\ e_1\ \texttt{++}\ (\texttt{compile}\ e_2\ \texttt{++}\ [\texttt{Add}]))\ \texttt{++}\ p ]\\!](s) &\textrm{by definition of}\ \texttt{compile}\\\\
&= \[\\![ \texttt{compile}\ e_1\ \texttt{++}\ ((\texttt{compile}\ e_2\ \texttt{++}\ [\texttt{Add}])\ \texttt{++}\ p) ]\\!](s) &\texttt{++}\ \textrm{is associative}\\\\
\end{align}
$$
Now we can use our inductive hypothesis for $e_1$, because it talks about *any* `p`:
$$
\begin{align}
&= \[\\![ (\texttt{compile}\ e_2\ \texttt{++}\ [\texttt{Add}])\ \texttt{++}\ p ]\\!](\texttt{cons}\ \[\\![ e_1 ]\\!]\ s) &\textrm{by inductive hypothesis}\\\\
&= \[\\![ \texttt{compile}\ e_2\ \texttt{++}\ ([\texttt{Add}]\ \texttt{++}\ p) ]\\!](\texttt{cons}\ \[\\![ e_1 ]\\!]\ s) &\texttt{++}\ \textrm{is associative}\\\\
\end{align}
$$
And now we use the inductive hypothesis *again* but for $e_2$. This time it works both because it talks about any `p` and *also* about any `s`:
$$
\begin{align}
&= \[\\![ [\texttt{Add}]\ \texttt{++}\ p ]\\!](\texttt{cons}\ \[\\![ e_2 ]\\!]\ (\texttt{cons}\ \[\\![ e_1 ]\\!]\ s)) &\texttt{++}\ \textrm{is associative}\\\\
&= \[\\![ p ]\\!](\[\\![ \texttt{Add} ]\\!] (\texttt{cons}\ \[\\![ e_2 ]\\!]\ (\texttt{cons}\ \[\\![ e_1 ]\\!]\ s))) &\textrm{by semantics of}\ \texttt{prog}\\\\
&= \[\\![ p ]\\!](\texttt{cons}\ (\[\\![ e_2 ]\\!] + \[\\![ e_1 ]\\!])\ s) &\textrm{by semantics of}\ \texttt{Add}\\\\
&= \[\\![ p ]\\!](\texttt{cons}\ (\[\\![ e_1 ]\\!] + \[\\![ e_2 ]\\!])\ s) &\textrm{by commutativity of}\ +\\\\
&= \[\\![ p ]\\!](\texttt{cons}\ \[\\![ \texttt{Plus}\ e_1\ e_2 ]\\!]\ s) &\textrm{by semantics of}\ \texttt{Plus}\\\\
&= RHS
\end{align}
$$
and we're done with this case!
3. (Inductive case for `Times`) This case works the same way as for `Plus`, but using multiplication, which is also commutative.

Phew! That was a long proof for a lemma. We're not done yet, though. Let's restate our original correctness theorem for `compile`, and use our new lemma to prove it:

**Theorem**: for all `expr`s `e`, $\[\\![ \texttt{compile}\ e ]\\!]([]) = [\ \[\\![ e ]\\!]\ ]$.

**Proof**: let `e` be an arbitrary `expr`. Then:
$$
\begin{align}
LHS = \[\\![ \texttt{compile}\ e ]\\!]([]) &= \[\\![ \texttt{compile}\ e\ \texttt{++}\ [] ]\\!]([]) &\textrm{since}\ \texttt{l ++ [] = l} \\
\end{align}
$$
Now we can set $p = []$ and $s = []$, and then our lemma applies, giving us:
$$
\begin{align}
\[\\![ \texttt{compile}\ e\ \texttt{++}\ [] ]\\!]([]) &= \[\\![ [] ]\\!](\texttt{cons}\ \[\\![ e ]\\!]\ [])  &\textrm{by lemma} \\\\
&= \texttt{cons}\ \[\\![ e ]\\!]\ [] &\textrm{by semantics of}\ \texttt{prog} \\\\
&= [\ \[\\![ e ]\\!]\ ] &\textrm{syntactic sugar for lists}
\end{align}
$$
and we're done!

Notice that when proving our final theorem, we no longer needed to use induction—the helper lemma
did the induction for us, and the correctness theorem "fell out" of that lemma after a little manipulation into the right form.
This is, again, a very common pattern in PL proofs.
We proved a *stronger* property that was inductive,
and then specialized that property to the theorem we actually wanted to prove.

## Interpreters in practice

While we're studying interpreters as mathematical objects that give languages a semantics,
they are also a common way to *implement* programming languages.
For example, Python is implemented as an interpreter of a *bytecode* language
not too dissimilar from our stack machine language.

To see how this works, consider this small Python program:

```python
def foo(x, y):
    if x > 10:
        return x + y
    else:
        return x * y

foo(2, 5)
```

If we save this program as `foo.py`, we can run `python -m dis foo.py`
to see the stack language representation of the program:

```
  1           0 LOAD_CONST               0 (<code object foo at 0x100dc5bb0, file "foo.py", line 1>)
              2 LOAD_CONST               1 ('foo')
              4 MAKE_FUNCTION            0
              6 STORE_NAME               0 (foo)

  7           8 LOAD_NAME                0 (foo)
             10 LOAD_CONST               2 (2)
             12 LOAD_CONST               3 (5)
             14 CALL_FUNCTION            2
             16 POP_TOP
             18 LOAD_CONST               4 (None)
             20 RETURN_VALUE

Disassembly of <code object foo at 0x100dc5bb0, file "foo.py", line 1>:
  2           0 LOAD_FAST                0 (x)
              2 LOAD_CONST               1 (10)
              4 COMPARE_OP               4 (>)
              6 POP_JUMP_IF_FALSE        8 (to 16)

  3           8 LOAD_FAST                0 (x)
             10 LOAD_FAST                1 (y)
             12 BINARY_ADD
             14 RETURN_VALUE

  5     >>   16 LOAD_FAST                0 (x)
             18 LOAD_FAST                1 (y)
             20 BINARY_MULTIPLY
             22 RETURN_VALUE
```

The first block here creates the `foo` function as a pointer to a *code object* that is defined later in the output.
The second block makes the function call to `foo` by pushing the two arguments onto the stack,
calling the function,
and popping the return value off the stack.

The interesting stuff is in the `foo` code object.
The first block implements the comparison—the `COMPARE_OP` instruction
pushes the result of its comparison onto the stack as a boolean,
and the `POP_JUMP_IF_FALSE` instruction pops that value and, if it's false, jumps down to instruction 16.
The two later blocks implement the two sides of the branch.
In each case, we push two arguments `x` and `y` onto the stack,
and then run `BINARY_ADD` or `BINARY_MULTIPLY`,
which pop the top two elements from the stack and push the result,
just as the `Add` and `Multiply` instructions in our language did.

Obviously, Python's interpreter is far more sophisticated than ours,
and in particular,
the canonical implementation assigns *C code* to each instruction
rather than a mathematical function.
But the idea is the same:
an interpreter takes as input program syntax
and *interprets* it to produce a result.
This is the essence of a denotational semantics
as opposed to the other types of semantics we'll study in this course.

(If you're curious about how the Python interpreter works,
I like [this chapter from the book *500 Lines or Less*](http://aosabook.org/en/500L/a-python-interpreter-written-in-python.html)
that builds a small Python bytecode interpreter in Python).

## Where interpreters break down

While denotational semantics give us simple mathematical tools to reason about programs,
they sometimes lead to complex or even impossible semantics. Let's see an example of this by trying
to add two new features to our language: support for variables and for control flow via `while` loops.

We'll do this by defining a new language for *commands*, but first we need to add variables to our expression language:
```
expr := Const nat
      | Var var
      | Plus expr expr
      | Times expr expr
```
Here we're adding a base case `Var` expression that contains the variable name. For this discussion let's just say that the `var` type is `string`.

To give the semantics for this language, we now need a notion of *maps* that assign each variable name
to a value. Let's write such a map as a *function* $v(x)$ that takes a variable name $x$ as input and
returns a value. We'll assume here that every variable name has a value (i.e., $v$ is a total function),
but that's just to make our semantics a little easier.

Now we can write the denotational semantics for `expr`s like this:
$$
\begin{align}
\[\\![ \texttt{Const } n ]\\!](v) &= n \\\\
\[\\![ \texttt{Var } x ]\\!](v) &= v(x) \\\\
\[\\![ \texttt{Plus } e_1\ e_2 ]\\!](v) &= \[\\![ e_1 ]\\!](v) + \[\\![ e_2 ]\\!](v) \\\\
\[\\![ \texttt{Times } e_1\ e_2 ]\\!](v) &= \[\\![ e_1 ]\\!](v) \times \[\\![ e_2 ]\\!](v)
\end{align}
$$

Here the semantics takes as input the variable map, just like our stack language semantics took stacks as input.
This seems a bit tedious right now, as the map is always the same, but it will change when we add assignment to the language in a moment.

Now let's define a command language with this syntax:
```
cmd := skip
     | var <- expr
     | cmd; cmd
     | while expr do cmd done
```
This is language of *statements* rather than expressions.
A command can either be a `skip`, which means "do nothing",
an assignment of an expression to a variable,
the sequence of two commands `cmd; cmd`,
or a while loop that runs a `cmd` until an expression returns 0.

Let's try to write down some semantics for this command language.
The semantics will be a transformer over *variable maps*;
that is, it will both take as input and return variable maps.
The first three cases of `cmd` are easy enough:
$$
\begin{align}
\[\\![ \texttt{skip} ]\\!](v) &= v \\\\
\[\\![ x \texttt{ <- } e ]\\!](v) &= v\[x \mapsto \[\\![ e ]\\!](v)] \\\\
\[\\![ c_1 \texttt{; } c_2 ]\\!](v) &= \[\\![ c_2 ]\\!](\[\\![ c_1 ]\\!](v))
\end{align}
$$

Here, we're writing $v\[x \mapsto a]$ to mean the _map update_ operation on $v$—returning a map
where $x$ is mapped to value $a$ and otherwise returns the same value as $v$ would.

Loops are the tricky case. The semantics we want is that the loop keeps running until the expression
returns 0 (since we don't have booleans in our language). We can try to write that down like this:
$$
\begin{align}
\[\\![ \texttt{while } e \texttt{ do } c \texttt{ done} ]\\!](v) &= \begin{cases}
v & \textrm{if } \[\\![ e ]\\!](v) = 0 \\\\
\[\\![ \texttt{while } e \texttt{ do } c \texttt{ done} ]\\!](\[\\![ c ]\\!](v)) & \textrm{otherwise}
\end{cases}
\end{align}
$$
But now we have a problem—this isn't really a "definition", since it expresses the semantics of the
while loop *in terms of itself*. This is actually a recursive equation, and we know from math that
recursive equations don't always have a solution!

The core of the problem here is *termination*, and it's a fairly fundamental issue for denotational
semantics. It's not impossible to solve; the idea is to define the semantics of `while` as a *fixed point*
of the recursive equation, and then prove (via the [Kleene fixed-point theorem](https://en.wikipedia.org/wiki/Kleene_fixed-point_theorem))
that this fixed point exists for the `cmd` language. But this is incredibly tedious and makes our
semantics very difficult to use. It's especially tedious in Coq, which requires all functions to terminate.
So we aren't going to look at it any further.

The takeaway here is that, while denotational semantics are great,
they have downsides, especially when dealing with non-terminating programs
(and also with non-deterministic programs, which we won't look at much here).
To deal with these sorts of programs,
we will turn instead to *operational semantics* in the next few lectures.

