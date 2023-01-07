# Homework 2

## Setup

This homework has the same setup as previous homework assignments. As you did
for previous assignments, please ensure that the Coq compiler `coqc` is in one
of the directories included in your `$PATH` environment variable.

You can build the homework using `make`:
```
make
```

Building the homework should take just a few seconds.

You can also run our autograder locally by running `make grade`. It will tell
you if you changed of the starter code you weren't supposed to, and if you have
any `admit`s left to solve.

If you are using Windows powershell and the scoop package manager, the Makefile
should still work if you do
```
scoop install zip busybox
```
The busybox dependency adds several Unix utilities used by the scripts.

## Doing the Homework

The `Makefile` is good for checking the entire file, but when you are working on
solving a problem, you should use VSCode (or another editor with interactive Coq
support) to work interactively. Don't be constantly switching to the terminal to
run `make` every time you take one step in the proof.


## Submitting Homeworks

Upload `HW2.v` to the
[CSE 505 Winter 2023 Gradescope](https://www.gradescope.com/courses/480697).

Please make sure to upload to the correct assignment and add your partner(s) on
the Gradescope submission page!

We have set up Gradescope to run an autograder to check that your submission
compiles, and that it does not contain `admit`s. However, **points are assigned
manually** by course staff, so please ignore the points that come from the
autograder. The purpose of the autograder is only to help you know whether your
code is going to work on our machines. Also, consider this fair warning that the
autograder does not check everything about the homework. For example, if the
homework asks you write a comment, or to *state* and prove a theorem, those will
not be checked by the autograder.

Remember, you can run `make grade` to run the autograder on your machine without
having to upload to Gradescope, if you just want to see how you are doing so
far.


## How you will be assessed

This is our first "real" homework. We will award points according to the
breakdown in the `.v` file for problems that you solve. If you make a good faith
attempt to solve a problem, we will award partial credit. There may be small
deductions for violations of the
[proof style guide](https://docs.google.com/document/d/1UVpIDUa6-Yb7SSP6a_s9aedOr0wfTU7aapKL5-8SxjY/edit?usp=sharing).


## Tactic Hints

Below is a list of tactics we used in our solution. We provide this list **for
guidance only**. You might not need to use all these tactics in your solutions,
and it's also fine if you use tactics not listed here. We hope this list might
help you in case you get stuck or if you want to learn more about the zoo of
available tactics :)

In our solutions we used the following tactics:
  - [apply](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.wmyojbtjsbdm)
  - [assumption](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.qr9az1rc7dca)
  - [auto](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.s8985lhzdrok)
  - [congruence](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.l5al90wpis6d)
  - [constructor](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.q622ucs616sv)
  - [contradiction](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.y1lza0gmoahv)
  - [destruct](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.3newm5wqrxoe)
  - [exists](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.jouy8cipzyez)
  - [induction](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.7ndluma1lrar)
  - [intros](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.yb8lu0pui041)
  - [inversion](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.fxdv8537ex79)
  - [left](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.xwqwa0c1fd53)
  - [lia](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.8wwbpic2x9nw)
  - [reflexivity](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.ohxs34gkav2p)
  - [replace](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.j2xoy0u7qdxf)
  - [rewrite](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.ugz9yjjzknkr)
  - [right](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.u581zr88081n)
  - [simpl](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.os5ra4dtccqa)
  - [specialize](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.vnz3fx7vxduz)
  - [split](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.j2zisxkgl4ev)
  - [subst](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.33eihravx2z5)
  - [try](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.6wa9yuf1j810)
  - [unfold](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.q1em5gze4sdu)
