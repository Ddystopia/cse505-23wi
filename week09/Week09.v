(*

System F in ASCII

Syntax

  Of types

    t ::= bool
        | t -> t
        | a                    (type variables)
        | forall a. t          (polymorphic type)

  Of expressions

    e ::= x
        | \x:t. e
        | e e
        | true
        | false
        | if e then e else e
        | /\a. e               (type abstraction)
        | e t                  (type application)

Free variables

  FTV(t)                       (free type variables of a type)

    FTV(bool)        = {}
    FTV(t1 -> t2)    = FTV(t1) U FTV(t2)
    FTV(a)           = {a}
    FTV(forall a. t) = FTV(t) - {a}

  FTV(e)                       (free type variables of an expression)

    FTV(x)                     = {}
    FTV(\x:t. e)               = FTV(t) U FTV(e)
    FTV(e1 e2)                 = FTV(e1) U FTV(e2)
    FTV(true)                  = {}
    FTV(false)                 = {}
    FTV(if e1 then e2 else e3) = FTV(e1) U FTV(e2) U FTV(e3)
    FTV(/\a. e)                = FTV(e) - {a}
    FTV(e t)                   = FTV(e) U FTV(t)

  Note that we are punning by giving two different functions the same name. You
  can always tell which FTV function we mean by seeing whether the argument is
  an expression or a type.

  Also note that FTV(e) calls FTV(t) in several cases.

  FV(e)                        (free expression variables in an expression)

    FV(x)                      = {x}
    FV(\x:t. e)                = FV(e) - {x}
    FV(e1 e2)                  = FV(e1) U FV(e2)
    FV(true)                   = {}
    FV(false)                  = {}
    FV(if e1 then e2 else e3)  = FV(e1) U FV(e2) U FV(e3)
    FV(/\a. e)                 = FV(e)
    FV(e t)                    = FV(e)

Substitution functions

  t[a |-> t_s]                 (substituting a type into a type)

    bool[a |-> t_s]            = bool
    (t1 -> t2)[a |-> t_s]      = t1[a |-> t_s] -> t2[a |-> t_s]
    a[a |-> t_s]               = t_s
    b[a |-> t_s]               = b    if a != b
    (forall b. t)[a |-> t_s]   = forall b. t[a |-> t_s]
                                 if a != b and b not in FTV(t_s)

  The side condition "if a != b and b not in FTV(t_s)" can always be satisfied
  by alpha-renaming the bound variable b.

  e[a |-> t_s]                 (substituting a type into an expression)

    x[a |-> t_s]               = x
    (\x:t. e)[a |-> t_s]       = \x:t[a |-> t_s]. e[a |-> t_s]
    (e1 e2)[a |-> t_s]         = e1[a |-> t_s] e2[a |-> t_s]
    true[a |-> t_s]            = true
    false[a |-> t_s]           = false
    (if e1 then e2 else e3)[a |-> t_s] =
        if e1[a |-> t_s] then e2[a |-> t_s] else e3[a |-> t_s]
    (/\b. e)[a |-> t_s]        = /\b. e[a |-> t_s]
                                 if a != b and b not in FTV(t_s)
    (e t)[a |-> t_s]           = e[a |-> t_s] t[a |-> t_s]

  e[x |-> e_s]                 (substituting an expression into an expression)

    x[x |-> e_s]               = e_s
    y[x |-> e_s]               = y    if x != y
    (\y:t. e)[x |-> e_s]       = \y:t. e[x |-> e_s]
                                 if x != y and y not in FV(e_s)
    (e1 e2)[x |-> e_s]         = e1[x |-> e_s] e2[x |-> e_s]
    true[x |-> e_s]            = true
    false[x |-> e_s]           = false
    (if e1 then e2 else e3)[x |-> e_s] =
        if e1[x |-> e_s] then e2[x |-> e_s] else e3[x |-> e_s]
    (/\a. e)[x |-> e_s]        = /\a. e[x |-> e_s]   if a not in FTV(e_s)
    (e t)[x |-> e_s]           = e[x |-> e_s] t


Operational Semantics

         e1 --> e1'
    ---------------------- StepAppL
      e1 e2 --> e1' e2

         e2 --> e2'
    ----------------------- StepAppR
      v1 e2 --> v1 e2'

    -------------------------------- StepBeta
      (\x. e1) v2 --> e1[x |-> v2]

                         e1 --> e1'
    ---------------------------------------------------- StepIfL
      if e1 then e2 else e3 --> if e1' then e2 else e3

    ---------------------------------- StepIfTrue
      if true then e2 else e3 --> e2

    ----------------------------------- StepIfFalse
      if false then e2 else e3 --> e3

        e --> e'
    ---------------- StepTyAppL
      e t --> e' t

    ----------------------------- StepTyBeta
      (/\a. e) t --> e[a |-> t]



Type System

    ---------------------- HTTrue
      D;G |- true : bool

    ----------------------- HTFalse
      D;G |- false : bool

        G(x) = t
    ----------------- HTVar
      D;G |- x : t

      D;G |- e1 : bool   D;G |- e2 : t   D;G |- e3 : t
    ---------------------------------------------------- HTIf
              D;G |- if e1 then e2 else e3 : t

      D;G |- e1 : tA -> tB   D;G |- e2 : tA
    ------------------------------------------ HTApp
              D;G |- e1 e2 : tB

      D |- tA   D;G,x:tA |- e : tB
    -------------------------------- HTAbs
       D;G |- \x:tA. e : tA -> tB

      a not in D      D,a;G |- e : t
    ---------------------------------- HTTyAbs
      D;G |- /\a. e : forall a. t

      D;G |- e : forall a. t1    D |- t2
    -------------------------------------- HTTyApp
          D;G |- e t2 : t1[a |-> t2]

We write "." for the empty context.

Lemma (Preservation):
    If .;. |- e : t and e --> e', then .;. |- e' : t.

Proof. By induction on the derivation of .;. |- e : t.

Cases ----------------------     -----------------------
        D;G |- true : bool         D;G |- false : bool

        D |- tA   D;G,x:tA |- e : tB        a not in D      D,a;G |- e : t
      --------------------------------    ---------------------------------
         D;G |- \x:tA. e : tA -> tB         D;G |- /\a. e : forall a. t

    These four cases are immediate, since e cannot step.

Case      G(x) = t
      -----------------
        D;G |- x : t

    This case is impossible since G = ., so no variable lookup can succeed.


Case   D;G |- e1 : bool   D;G |- e2 : t   D;G |- e3 : t
     ----------------------------------------------------
               D;G |- if e1 then e2 else e3 : t

    We have e = if e1 then e2 else e3. By inversion on the derivation of
    e --> e', there are three ways an if expression can step.

    Subcase                      e1 --> e1'
            ----------------------------------------------------
              if e1 then e2 else e3 --> if e1' then e2 else e3

        We have e' = if e1' then e2 else e3.  By the induction hypothesis for
        e1, since e1 --> e1', we have .;. |- e1 : bool. Then by HTIf, it follows
        that .;. |- e' : t.

    Subcase ----------------------------------
              if true then e2 else e3 --> e2

        We have e' = e2. The goal follows from the premise of this case,
        .;. |- e2 : t.

    Subcase -----------------------------------
              if false then e2 else e3 --> e3

        We have e' = e3. The goal follows from the premise of this case,
        .;. |- e3 : t.


Case   D;G |- e1 : tA -> tB   D;G |- e2 : tA
     ------------------------------------------
               D;G |- e1 e2 : tB

    We have e = e1 e2 and t = tB. By inversion on the derivation of e --> e',
    there are three ways an application expression can step.


    Subcase      e1 --> e1'
            ----------------------
              e1 e2 --> e1' e2

        We have e' = e1' e2. By the induction hypothesis for e1, since
        e1 --> e1', we have .;. |- e1' : tA -> tB. Then by HTApp, it follows
        that .;. |- e' : tB.

    Subcase      e2 --> e2'
            -----------------------
              v1 e2 --> v1 e2'

        We have e1 = v1 and e' = v1 e2'. By the induction hypothesis for e2,
        since e2 --> e2', we have .;. |- e2' : tA. Then by HTApp, it follows
        that .;. |- e' : tB.

    Subcase --------------------------------
              (\x. e1_body) v2 --> e1[x |-> v2]

        We have e1 = (\x. e1_body) and e2 = v2 and e' = e1[x |- v2]. The result
        follows from the substitution lemma.

Case   D;G |- e1 : forall a. t1    D |- t2
     ---------------------------------------
           D;G |- e1 t2 : t1[a |-> t2]

    We have e = e1 t2 and t = t1[a |-> t2]. By inversion on the derivation of
    e --> e', there are two ways a type application can step.

    Subcase     e1 --> e1'
            --------------------
              e1 t2 --> e1' t2

        We have e' = e1' t2. By the induction hypothesis for e1, since
        e1 --> e1', we have .;. |- e1' : forall a. t1. Then by HTTyApp, it
        follows that .;. |- e' : t1[a |-> t2].

    Subcase -------------------------------------------
              (/\a. e1_body) t2 --> e1_body[a |-> t2]

        We have e1 = (/\a. e1_body) and e' = e1_body[a |-> t2]. The result
        follows from the type substitution lemma.
Qed.

Lemma (Substitution)
    If .;x:t2 |- e1 : t1 and .;. |- e2 : t2, then .;. |- e1[x |-> e2] : t1.

Proof sketch. Similar to STLC, the lemma needs to be generalized to an arbitary
context. Then the proof proceeds by induction on e1's typing derivation. In the
variable case, when substitution occurs, use the weakening lemma.
Sketch-ed.

Lemma (Weakening)
    If .;. |- e : t, then for any D and G, D;G |- e : t.
Proof sketch. Similar to STLC, the lemma needs to be generalized to an arbitrary
context. Then the proof proceeds by induction on e's typing derivation.
Sketch-ed.

Lemma (Type substitution)
    If a;. |- e : t1 and . |- t2 then .;. |- e[a |-> t2] : t1[a |-> t2].

Proof sketch. The lemma needs to be generalized to an arbitrary context. Then
the proof proceeds by induction on e's typing derivation. In the case for type
application, use the "type substitutions commute" lemma.
Sketch-ed.

Lemma (Type substitutions commute)
    If a != b and a is not in FTV(t2), then
        t[a |-> t1][b |-> t2] = t[b |-> t2][a |-> t1[b |-> t2]].
Proof sketch. By induction on t. In the variable case, use the lemma
"type substitution is no-op if variable is not in FTV".
Sketch-ed.

Lemma (Type substitution is no-op if variable is not in FTV)
    If a is not in FTV(t1), then
        t1[a |-> t2] = t1.
Proof sketch. By induction on t1. All cases are straightforward.
Sketch-ed.

*)