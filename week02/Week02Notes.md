+++
title = "Week 02 - More Functional Programming: Lists and Trees"
+++


# Week 02 - More Functional Programming: Lists and Trees

### Some other ADTs

Let's keep playing with these ideas, but now on some different ADTs. 

#### Lists

Another ADT we see a lot in programming is the *list*. For now, we'll focus on lists of natural numbers, and later we'll see how we can generalize this idea. A list of natural numbers is just an ADT with two constructors:

```
list_nat := nil | cons nat list_nat
```

A list of natural numbers is either "nil" (the empty list) or made by applying the `cons` constructor to a `nat` and *another* list. (The name `cons` is historical. It comes from [Lisp](https://en.wikipedia.org/wiki/Lisp_(programming_language)) ("LISt Processor"), one of the earliest programming languages, developed by Turing Award winner [John McCarthy](https://en.wikipedia.org/wiki/John_McCarthy_(computer_scientist)). It's one of my favorite languages :-)).

So, here are a few lists:

* `nil` is the list []
* `cons 1 nil` is the list [1]
* `cons 1 (cons 2 nil)` is the list [1, 2]
* ...and so on

Again, remember that ADTs are just syntactic constructs. There's no evaluation going on here; `nil` and `cons` are not functions. We can, however, define functions *over* lists. Here's one:

```
length nil        = zero
length (cons n l) = succ (length l)
```

One thing to notice about this function is that we never use the *values* of the list—the `n` in `cons n l` is never referenced on the right-hand side. That's OK! It tells us that our function only cares about the *shape* of the list.

Let's define a slightly more complicated function over *two* lists now:
```
append nil l2         = l2
append (cons n l1) l2 = cons n (append l1 l2)
```
This gives us a way to join two lists together by appending them. Check it out:
```
append (cons 1 (cons 2 nil)) (cons 3 nil) = cons 1 (append (cons 2 nil) (cons 3 nil))
                                          = cons 1 (cons 2 (append nil (cons 3 nil)))
                                          = cons 1 (cons 2 (cons 3 nil))
```
Or in other words, `[1, 2] ++ [3] = [1, 2, 3]`, if we write `++` to mean list append.

Here's a small but interesting theorem about the interaction between `append` and `length`:

**Theorem**: For all lists `l1` and `l2`, `length (append l1 l2) = add (length l1) (length l2)`.

**Proof**: As usual, we're doing a proof about a recursive ADT, so we probably want to do induction, in this case on `l1`. There's two cases:

1. (Base case) If `l1 = nil`, then:
   ```
   length (append nil l2) = length l2
   add (length nil) (length l2) = add zero (length l2) = length l2
   ```
2. (Inductive case) If `l1 = cons n l1'`, then starting from the left-hand side:
   ```
   LHS = length (append (cons n l1') l2)
       = length (cons n (append l1' l2))   (by definition of append)
       = succ (length (append l1' l2))     (by definition of length)
   ```
   Here is where we need to be very pedantic about our induction principle to make progress. Notice that our theorem is quantified over *two* lists, and we chose to do induction over the *first* list `l1`. We can rewrite our theorem like this, adding some parentheses for clarity:
   
   > For all lists `l1`, (for all lists `l2`, `length (append l1 l2) = add (length l1) (length l2)`)
   
   In other words, our inductive hypothesis is *also quantified*! It says this:
   > For all lists `l2`, `length (append l1' l2) = add (length l1') (length l2)`
   Notice that this statement is a property *only of `l1'`*.
   
   So we can continue our proof by applying the inductive hypothesis:
   ```
   LHS = succ (length (append l1' l2))
       = succ (add (length l1') (length l2))    (by inductive hypothesos)
   ```
   and now, starting from the RHS:
   ```
   RHS = add (length (cons n l1')) (length l2)
       = add (succ (length l1')) (length l2)     (by definition of length)
       = succ (add (length l1') (length l2))     (by definition of add)
       = LHS
   ```
   and we're done!

Again, the takeaway is that **the proof structure follows the data structure**, and we'll return to this idea over and over. Another important takeaway here is to **be very careful about quantifiers**. Many programming languages proofs will involve multiple objects; we need to be precise about which objects we're talking about, inducting over, etc.

#### Trees

Trees are also ADTs. Again, sticking to trees over natural numbers, a (binary) tree is an ADT with two constructors:

```
tree_nat := leaf | node tree_nat nat tree_nat
```

This definition is a little funky, so let's break it down:

* The simplest binary tree is the *empty tree*, which is just `leaf`.
* The next simplest binary tree is the single-node tree, which is `node leaf n leaf` if the node holds value `n`.
* The binary tree with a root node `a`, left child `b`, and right child `c`, is `node (node leaf b leaf) a (node leaf c leaf)`.
* ...and so on

## Programs as ADTs

So why have we trudged through all this data structures and discrete math stuff in a *programming languages* course? Here's the big reveal: **programs are just ADTs too**!

Let's consider a simple fragment of a language like C or Java. These languages probably accept expressions like these as valid (parts of) programs:
```
3
x
3 + x
y * (3 + x)
```
but reject expressions like these:
```
1 + + 2
3 x y
```

We could formalize this intuition a little (and compilers *do* formalize this idea) by writing a grammar in *Backus-Naur Form*. We can define the possible expressions `e` recursively:
```
e := n 
   | x 
   | e + e
   | e * e
```
where $n \in \mathbb{N}$ is a natural number and $x \in S$ is a variable name drawn from some set S we won't define here. What we're saying is that our expressions are either numbers, variables, or the sum or product of two other expressions.

Notice that this grammar looks extremely similar to how we were building ADTs earlier. That's not a coincidence—this language *is* an ADT! We'll return to this point in just a second.

This grammar is a definition of the syntax of our language. But it has an immediately undesirable property: it's ambiguous. Consider the expression `1 + 2 * 3`—does this mean `(1 + 2) * 3` or `1 + (2 * 3)`?

Dealing with this ambiguity is very tedious in general, and a frequent stumbling block for implementing programming languages. We're going to *completely ignore it* for this course. Instead, we're going to separate *concrete* syntax from *abstract* syntax. It's the job of a *parser* to translate concrete syntax (a string of characters) into abstract syntax like the ADT we just defined. These ADTs are referred to as *abstract syntax trees* (ASTs).

We can rewrite our language syntax to be closer to the style of ADTs we were defining earlier by using names and constructors:
```
expr := number nat
      | variable str
      | addn expr expr
      | mult expr expr
```

And then it's the job of a parser to convert *strings* of concrete syntax into ASTs. For example:

* `1 + 1` => `addn (number 1) (number 1)` (where I'm abusing notation a little by writing digits instead of `succ`/`zero` for `nat`s)
* `1 + 2 * 3` => `mult (addn (number 1) (number 2)) 3`
    * Notice that the *parser made the decision* about how to resolve the ambiguity here. It could instead have chosen `addn 1 (mult (number 2) (number 3))`.

We won't talk any more about parsing in this course. Instead, we'll always assume we start from an AST. Parsing is a fascinating topic, though—programming languages people often joke that "parsing is a solved problem", but in fact there's been a *ton* of really interesting advances in parsing since it was "solved", with ideas like [packrat parsing](https://bford.info/packrat/), [parser combinators](https://en.wikipedia.org/wiki/Parser_combinator), and [parsing with derivatives](https://matt.might.net/papers/might2011derivatives.pdf). It's definitely worth studying more. Consider taking a compilers course!

### Syntax and semantics

What does it mean to formalize a programming language? We've just seen that we can define program *syntax* formally using an ADT, but is that enough? We actually need *two* things to formalize a programming language:

1. **Syntax** defines what programs *are*—their "shape" or "structure". Syntax is the "what". For the purposes of this course, syntax is given by an abstract syntax tree, which is an ADT.
2. **Semantics** defines what programs *mean*—how they behave, how they evaluate. Semantics are the "how". There are several different ways to define the semantics of a programming language, and we'll be studying them later.

It's important to remember that you need *both* these things to formalize a programming language, and to remember which one you're working with. To make this point concrete, here are two different programs written as ASTs:

1. `addn (number 1) (number 1)`
2. `number 2`

These programs are *not the same thing*! They are not equal. We haven't yet said anything about what programs *mean*, and so we have no basis to claim they're in any way the same—they are just as different as `number 7` and `mult (number 4) (number 6)` are. Of course, most sensible definitions of what the two programs *mean* will conclude that they mean the same thing—for example, they both *evaluate* to the same value. But they are *different programs*.

The rest of this lecture deals only with syntax; we'll see semantics later.

### Functions and proofs over ASTs

Since abstract syntax trees are just ADTs like we've been studying, the common themes apply again. We can define *functions* over ADTs to talk about *syntactic* properties of programs.

Let's define the "size" of a program by just counting the number of nodes in its abstract syntax tree:
```
size (number n)   = 1
size (variable x) = 1
size (addn e1 e2) = 1 + (size e1) + (size e2)
size (mult e1 e2) = 1 + (size e1) + (size e2)
```

Similarly, we could also define the "height" of a program as the longest path from the root of the AST to any leaf:
```
height (number n)   = 1
height (variable x) = 1
height (addn e1 e2) = 1 + max (height e1) (height e2)
height (mult e1 e2) = 1 + max (height e1) (height e2)
```
(From here on I'm going to be eliding some of the tedious details about natural numbers, and particularly the `max` function. If we were being pedantic—and we will be!—we'd need to define those first.)

Notice that both these functions are *only* about the syntax of programs; they say nothing about *meaning*.

Now let's try a proof about these functions to get some more practice with induction.

**Theorem**: for all `expr` `e`, `height e <= size e`.

**Proof**: as usual, since these functions are recursive, we'll proceed by induction on `e`. There are _four_ cases to consider here, though there's a lot of symmetry:

1. (Base case) if `e = number n`, then `size (number n) = 1` and `height (number n) = 1`.
2. (Base case) if `e = variable x`, then `size (variable x) = 1` and `height (variable x) = 1`.
3. (Inductive case) if `e = addn e1 e2`, then:
   ```
   height (addn e1 e2)  = 1 + max (height e1) (height e2)
                       <= 1 + max (size e1) (size e2)          (*)
                       <= 1 + (size e1) + (size e2)
                        = size (addn e1 e2)
   ```
   where we used *two* inductive hypotheses at `(*)`—structural induction gives us one inductive hypothesis *for each premise* of the relevant inference rule.
4. (Inductive case) if `e = mult e1 e2` the proof is the same as for `e = addn e1 e2`.

## Wrap up

That's it for this lecture! We've seen that ADTs can model data structures (lists, trees) and even program syntax. All of these can be reasoned about with induction.

As always, remember the motto: the structure of the proof follows the structure of the program or definitions.
