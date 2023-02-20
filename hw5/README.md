# Homework 5

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

Upload `HW5.v` to the
[CSE 505 Spring 2021 Gradescope](https://www.gradescope.com/courses/256901).

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

We will award points according to the breakdown in the `.v` file for problems
that you solve. If you make a good faith attempt to solve a problem, we will
award partial credit. There may be small deductions for violations of the [proof
style
guide](https://docs.google.com/document/d/1kRt6L8sjmi0LJgWQaBCT1je-wqSftyHpAH3KWAQLL5U/edit?usp=sharing).


## Tactic Hints

Below is a list of tactics we used in our solution. We provide this list **for
guidance only**. You might not need to use all these tactics in your solutions,
and it's also fine if you use tactics not listed here. We hope this list might
help you in case you get stuck or if you want to learn more about the zoo of
available tactics :)

In our solutions we used the following tactics:
  - all:
  - [apply](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.6hj9bgx79d4q)
  - assert
  - [auto](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.184wugz4h1iu)
  - break_up_hyps
  - [cbn](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=kix.f4bi7fezrctj)
  - compute
  - [congruence](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.l5al90wpis6d)
  - [constructor](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.gh30zoah4yh9)
  - [destruct](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.31h1z5e3u3wt)
  - discriminate
  - [eapply](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.pbw0eekdis6x)
  - eassumption
  - eauto
  - [econstructor](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.k0xvvq3sna6d)
  - eexists
  - eqn:?
  - eval_utlc
  - exfalso
  - [exists](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.jouy8cipzyez)
  - firstorder
  - [induction](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.vdd8yhofsq41)
  - [intros](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.ctlk62idrwvx)
  - intuition
  - invc
  - [reflexivity](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.w7wn2c8h0zwt)
  - repeat
  - revert
  - [rewrite](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.hge0chk9zpao)
  - [right](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.rb4oz7zetbh)
  - [simpl](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.tglpvbqrvega)
  - [split](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.lrn6242c5g3r)
  - [subst](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.mnjvub17qvcr)
  - [try](https://docs.google.com/document/d/1gsvW-iCWD7Ssr0hyDfIXa28Fk55nZMaayrg0Dg4JudE/edit#bookmark=id.6wa9yuf1j810)
  - [unfold](https://docs.google.com/document/d/1m9JxzgwORLVKaNayfdSvotwI1j4JGQ8YFUmbCbflk9M/edit#bookmark=id.4ecb7nfs35ei)
