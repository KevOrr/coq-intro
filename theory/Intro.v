<<<<<<< HEAD
From Hammer Require Import Hammer.
Hammer_version. (* CoqHammer 1.3 for Coq 8.12 *)
Require Import PeanoNat.
Theorem n_or_Sn_Odd : forall (n : nat), Nat.Odd n \/ Nat.Odd (n + 1).
  Fail predict 1.
  Fail hammer.

=======
>>>>>>> c1e1282 (A)
(*|
#####
Intro
#####

Before anything else, for a more comprehensive introduction to Coq, I recommend
`Software Foundations <https://softwarefoundations.cis.upenn.edu/>`_ and `Certified
Programming with Dependent Types <http://adam.chlipala.net/cpdt/>`_. This won't
be a complete introduction, but in this file I'll quickly review basic Coq syntax
and commands.

Data
****

First off: we use the `Inductive` keyword to define a datatype (think ``data`` in
Haskell or ML). I put these next few definitions into a module so we don't overwrite
the builtin ones of the same names later in the file.
|*)

Module Builtins. 
Inductive bool : Set :=
| true
| false.

(*|
We can have recursive types:
|*)

Inductive nat : Set :=
| O
| S (n : nat).

(*|
We can add type parameters:
|*)

Inductive list (A : Type) : Type :=
| nil
| cons (x : A) (xs : list A).

(*|
We can also use a syntax more familiar to Haskellers:
|*)

Reset list.
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

End Builtins.

(*|
We can also express GADTs. ``Vector A n`` is the type of exactly ``n``-length lists whose
members are of type ``A``:
|*)

Inductive Vector (A : Type) : nat -> Type :=
| vnil : Vector A 0
| vcons : forall (n : nat), A -> Vector A n -> Vector A (S n).

(*|

Here is a ``forall`` type. This is a lot like an arrow type (e.g. ``nat -> A -> ...``), and
in fact, ``A -> B`` is a *notation* (shorthand) for ``forall (_ : A), B``. A ``forall`` type
is called a *dependent* arrow, in that the *type* after the ``forall`` can *depend* on the
*value* of the ``forall``-quantified variable. This is the way that every explains what
a dependent arrow is, yet it usually doesn't sink in by simply defining it. Examples help.

Also notice that we have a type *parameter* before the colon (``A``), as well as a type
*index* (a value of type ``nat``) after the colon. TODO summarize difference between
parameters and indices. Let's take a look at what we can do with `Vector`.

Let's ask Coq what it thinks the types of ``Vector``, ``vnil``, and ``vcons`` are:
|*)

Check Vector. (* .unfold *)

(*|
That is, ``Vector`` is a type function (specifically a type constructor) which takes another
type (``A``), a ``nat``, and returns a concrete type.
|*)

Check vnil. (* .unfold *)

(*|
``vnil`` takes a type ``A``, and returns a value of type ``Vector A 0``
|*)

Check vcons. (* .unfold *)

(*|
``vcons`` takes a type ``A``, a number ``n``, a *value* of type ``A``, a value of type
``Vector A n`` (a length-``n`` vector), and returns a value of type ``Vector A (S n)``
(a length-``(S n)`` vector).
|*)

(*|
Implicit Parameters
===================

Notice how ``vnil`` and ``vcons`` are automatically generalized over ``(A : Type)``,
because ``Vector`` is parameterized over an ``(A : Type)``. Because the correct value
for ``A`` can be easily inferred from the types or values of later arguments, or from
the return type, we can ask Coq to automatically infer it, instead of us having to always
specify it:
|*)

Reset Vector.
Inductive Vector {A : Type} : nat -> Type :=
| vnil : Vector 0
| vcons : forall {n : nat}, A -> Vector n -> Vector (S n).

(*|
The curly braces ``{A : Type}`` means that Coq should infer ``A`` instead of the user having
to supply it. We call such a parameter an *implicit* parameter. However, we will often want to
specify the ``A`` in ``Vector A n``, so
|*)

Arguments Vector : clear implicits.

(*|
It is somewhat common to follow a type definition containing an implicit type parameter with a
``clear implicits`` for only the type constructor. I wish there were a more concise syntax for
this becuase it is such a common pattern...
|*)

Check Vector. (* .unfold *)
Check vnil. (* .unfold *)
Check vcons. (* .unfold *)

(*|
Now ``vnil`` and ``vcons`` look a lot like their list counterparts, ``nil`` and ``cons``,
except with an extra unification variable ``?n`` in the ``vcons`` case.

A taste of dependent types
**************************

Let's see what we can do with a ``Vector``.
|*)

Definition vlength {A n} (v : Vector A n) : nat := n.

(*|
Woah! Why don't we have to actually count how long a vector is to compute its length?
Because the length of a vector is encoded in its type. What if the length of a vector is
not known statically, for instance because it's chosen by the user at runtime or it's
based on a value returned by an RNG? Well, the idea is that the producer of a Vector
should know how long of a Vector it is producing. If a user asks for a length 4 Vector,
then that function which creates the Vector knows that it has a length of 4. This value
is then carried around in its type.

Doesn't this have terrible implications for runtime performance? Well, yes and no. Mostly
no, but that's a topic for another day.
|*)

Definition vhead {A n} (v : Vector A (S n)) : A :=
  match v with
  | vcons x _ => x
  end.

(*|
Few things to unpack here:

* Notice the ``{A n}``. This gets elaborated (automatically inferred) as ``{A : Type} {n : nat}``
  becuase of how ``A`` and ``n`` are used in ``Vector A (S n)``, making it obvious what their types
  should be. Then the curly braces are again implicit parameters.
* The ``(S n)`` indicates that there should be at least one element in the vector `v`, because 0 is not
  the successor of any number (¬∃ n, 0 = S n)
* Then, we only need to pattern match on the ``vcons`` case. Is this a partial function? No, Coq doesn't
  permit partial functions. It is because the type of ``v``, namely that it's index is ``S`` of some number.
  Because ``vcons`` is the only constructor that returns a ``Vector _ (S _)`` (``vnil`` returns a
  ``Vector _ 0``), then ``vcons`` is the only constructor that needs to be considered.

In fact, something much more complicated is happening behind the scenes, and this is part of the power
behind fully dependent pattern matching. Idris and Agda have long supported the kind of pattern match
given above, where we only have to consider the ``vcons`` case. In Coq, this used to be a much longer
incantation, and only recently has it begun to accept definitions like the one above and elaborate
it to the full thing. If you're curious, here's what the above elaborates to:
|*)

Print vhead.

(*|
Before showing ``vtail``, first here is the nat predecessor function:
|*) 

Print Nat.pred. (* .unfold *)
Compute Nat.pred 5. (* .unfold *)
Compute Nat.pred 1. (* .unfold *)
Compute Nat.pred 0. (* .unfold *)

Definition vtail {A n} (v : Vector A n) : Vector A (Nat.pred n) :=
  match v with
  | vnil => vnil
  | vcons _ xs => xs
  end.

(*|
This is typechecked by case analysis:

* In the ``vnil`` case, we are given a ``Vector A 0`` and must produce a ``Vector A (pred 0)``,
  but as shown above ``pred 0 = 0``, so we can return something of type ``Vector A 0``. That's
  exactly what we're given!
* In the ``vcons`` case, we are given a ``Vector A (S n)`` and must produce a
  ``Vector A (pred (S n))`` but again, due to its definition, ``Nat.pred (S n) = n``, so we
  can return a ``Vector A n``. If ``vcons _ xs : Vector A (S n)``, then ``xs : Vector A n``

Now we can try concatenating vectors, but first, we'll need addition:
|*)

Print Nat.add. (* .unfold *)

(*|
This is our first recursive function, and you'll notice the distinctive ``fix`` keyword.
This is the keyword for signalling that a recursive function follows; otherwise functions
are not allowed to be recursive. This has to do with Coq only permitting programs that
provably terminate on all inputs. Non-recursive functions certainly terminate, so the
special case becomes recursive functions. I won't get into how it checks whether a recursive
definition is certainly terminating, but suffice it to say that ``Nat.add`` is shown
to terminate.
|*)

Fixpoint vappend {A n m} (v1 : Vector A n) (v2 : Vector A m) : Vector A (n + m) :=
  match v1 with
  | vnil => v2
  | vcons x xs => vcons x (vappend xs v2)
  end.

(*|
It's almost a miracle that this definition is permitted. In fact, it would not be permitted
if the type signature ended in ``Vector A (m + n)``, even though such a function should
certainly exist! Let's open the proof shell to see how we can define such a function:
|*)

Theorem vappend' {A n m} (v1 : Vector A n) (v2 : Vector A m) : Vector A (m + n). (* .unfold *)
  (*| The items above the line are our hypotheses, or assumptions. The item(s) below the line are the goal(s). We must use the hypotheses to prove the goal in each case |*)
  (*| ``induction`` is how we start a recursive definition... No, actually, it's how you apply the principle of mathematical induction... No, actually, those are the same thing... Another topic for another day... |*)
  (*| We induction on ``v2`` this time, because the first argument to ``Nat.add`` is the one which it recurses on, and ``m`` is the index of ``v2``. Don't worry if that doesn't make sense |*)
  induction v1 as [ | ? x xs IH ]. (* .unfold .all *)
  (*| This leaves us with two goals, one in the case that ``v1 = vnil``, and one in the case ``v1 = vcons _ _`` |*)
  (*| Let's see if the first goal can be simplified by applying ``Nat.add``... |*)
  - simpl. (* .unfold *)
    (*| Let's first use an existing lemma that shows that ``n + 0 = n`` |*)
    SearchRewrite (_ + 0).  (* .unfold .no-goals *)
    rewrite <- plus_n_O.  (* .unfold *)
    exact v2. (* .unfold *)
  (*| The second case is a bit trickier: |*)
  - (* .unfold *)
    (*| Let's first use an existing lemma that shows that ``x + S y = S (x + y)`` |*)
    SearchRewrite (_ + S _). (* .unfold .no-goals *)
    rewrite <- plus_n_Sm. (* .unfold *)
    (*| Now we know that a ``Vector A (S _)`` can only be introduced by ``vcons`` |*)
    exact (vcons x IH).
Defined.

(*| The types line up, but is the definition correct? |*)
Definition v := Eval cbv in vappend' (vcons 1 (vcons 2 vnil)) (vcons 3 (vcons 4 vnil)).
Print v. (* .unfold *)

(*| Well that's... awful. But we can still see the ``vcons 1 (... (vcons 4 vnil)))`` hidden in there.
The reason there's a bunch of extra noise has to do with the *opaqueness* of ``plus_n_Sm`` and
``plus_n_O``. They are declared to be opaque, and so they can't be simplified away during reduction.
However, if we extract this code into a non-dependently typed language, all of the ``eq_`` nonsense
goes away:
|*)

Require Extraction.
Extraction Language Haskell.
Extraction Inline eq_rect.
Extraction Inline Vector_rect.

Extraction vappend'. (* .unfold *)

Extraction v. (* .unfold *)

(*|
Extraction
**********

This demonstrates an interesting feature, however: extraction. One of Coq's killer features is the
ability to extract Coq code into a variety of other functional programming languages, namely OCaml,
Haskell, and Scheme. In the process, we lose any dependent typing, so guarantees are lost. But the
invariants that held in the code will still hold. For instance,
|*)

Extraction vhead. (* .unfold *)

(*|
What is that ``__`` there? Well if we extract a complete module instead of one defintion...
|*)

Recursive Extraction vhead. (* .unfold *)

(*|
We can see that ``__`` is a runtime error. This makes sense because you cannot take the head of a
``vnil``. Haskell doesn't have dependent types (and the spec does not yet mention GADTs), so ``vhead``
can't enforce the pre-invariant; it's up to the caller to make sure to only call ``vhead`` with a
``vcons``. On the other hand,
|*)

Definition vhead_safe {A n} (v : Vector A n) : option A :=
  match v with
  | vnil => None
  | vcons x _ => Some x
  end.

Extract Inductive option => Maybe [Just Nothing].
Extraction vhead_safe. (* .unfold *)

(*|
Dependent match, and Prop
*************************

Let's revisit ``__``. It could have just as easily been defined as
``undefined``, except the error message is descriptive and helpful. In fact, what does it say?
"Logical or arity value used"? Huh? Why not just say "we've hit an absurd case! did you break
an invariant?"? Well that's actually not what this error message is saying at all! Let's take
another look at vhead's full, elaborated, definition:
|*)

Print vhead. (* .unfold *)

(*|
If you look in the ``vnil`` case, it returns an ``idProp``. Well, actually, the ``vnil`` case
can never be hit, because ``v : Vector A (S n)``. So why do we have to include anything at all?
Well, Coq's ``match`` knows nothing about absurd cases. We must use ``match`` in such a way
that, inside of a match, we return something trivial for the ``vnil`` case, and on the outside,
since we know that the ``vnil`` case will never be hit, the return type of the entire match only
depends on what the return type for the ``vcons`` case is.

What the ``return match ... end`` clause describes is how the return type of the match changes
in each case. It says "inside the match, if the length of ``v`` is 0, return an ``IDProp`` (more
on ``IDProp`` later); otherwise if it's ``S _``, return an ``A``". But it also describes what the
return type of the whole match is. The return type of the whole match is

.. code-block:: coq

  match (S n) with
  | 0 => IDProp
  | S _ => A
  end

But this just simplifies down to just ``A``. Aha! So inside the match, we must return an ``IDProp``
in the ``vnil`` case, and an ``A`` in the ``vcons`` case, but outside the match, we know we will
always have an ``A``. This is how you elide absurd cases using dependent match.

Prop
====

Okay, now, what are ``IDProp`` and ``idProp``?
|*)

Print IDProp. (* .unfold *)
Print idProp. (* .unfold *)

(*|
Put simply ``IDProp`` is a trivially true proposition, and ``idProp`` is a proof of ``IDProp``.
Proposition?

Due to the `Curry-Howard correspondence <https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence>`_,
the class of mathematical propositions is *isomorphic* to the class of types. All this means is
that there is a one-to-one correspondence between proofs (in the mathematical sense) and programs.
Under this analogy, propositions are types, and proofs are programs. That is fundamentally why
we can write proofs in a functional programming language such as Coq.

For instance, we are all familiar with the proposition of equality, yes? ``x = y``. What do
we know of equality. Well, it's the smallest relation that's reflexive, symmetric, and transitive.
How is it defined in Coq? (Yes, equality is *defined*, not primitive, in Coq)
|*)

Locate "_ = _". (* .unfold *)
Print eq. (* .unfold *)

(*|
Equality is an inductive type! Moreover, it only has one constructor. Hmm, the type signature
is a little confusing. It would be easier to grok if eq were instead defined as
|*)

Inductive eq' {A : Type} : A -> A -> Prop :=
| eq'_refl : forall x, eq' x x.

(*|
That is, eq' is an inductive type with only *one* constructor. This constructor says that
for all values ``x``, ``x`` equals itself. That is to say, equality is reflexive. What
about the other two properties, symmetry and transitivity? I won't get into it here, but
they actually follow from reflexivity and ``eq``-elimination (a.k.a the idiscernibility of
identicals).

So what does "Logical or arity value used" mean? Well, although proofs are programs, not all
proofs need to actually wind up in the extracted output program. ``idProp`` is simple enough,
but what about a beast like
|*)

(* Just quickly redefining the stdlib theorem *)
Theorem plus_n_Sm' : forall n m : nat, S (n + m) = n + S m.
  induction n; [easy | now intros; simpl; rewrite <- IHn].
Defined.

Compute plus_n_Sm'. (* .unfold *)

(*|
Holy cow, that's huge! Are we really running that code whenever some extracted code calls
``plus_n_Sm``? Actually, no. Recall that ``vappend'`` used ``plus_n_Sm`` in its definition,
and yet, ``plus_n_Sm`` didn't show up at all in the extracted output. Here it is again:
|*)

Extraction vappend'. (* .unfold *)

(*|
Why doesn't it have to show up? Well, simply put, the exact contents of ``plus_n_Sm`` are
*irrelevant* to the rest of the code. It can never affect the control or data flow of our program.
Specifically in this case, that is because the only value ``plus_n_Sm`` could ever return
is ``eq_refl``. But moreover, it is because ``eq : ... -> Prop``. ``eq`` is an inductive
type in *sort* ``Prop``. I can't get too much into sorts, but ``Prop`` is a special one.
Coq's type system (based upon the Calculus of (Co-)Inductive Constructions, CIC) is carefully
designed to not allow a value of sort ``Set`` or ``Type`` to depend on any value of sort
``Prop``. This essentially means that *no* value of sort ``Prop`` needs to wind up in extracted
code.

That's enough of that. Let's learn about some program sythesis.

Hammer
******

The `Coq Hammer <https://github.com/lukaszcz/coqhammer>`_ (terrible, unfortunate name) is
"an automated reasoning Hammer tool for Coq". The term Hammer (to my best knowledge) refers
to a `2010 paper <https://www.cl.cam.ac.uk/~lp15/papers/Automation/paar.pdf>`_ about
linking interactive proof assistants (like Coq, but the paper is about Isabelle/HOL) with
automatic theorem provers (ATPs) (e.g. CVC, Twelf, Z3, SPARK). With no further ado,
|*)

From Hammer Require Import Hammer.

(*|
Let's try to prove some really gnarly theorem
|*)

Theorem nat_thing : forall n m, (n + m) * (2*n*n + n*m) = (n*n + n*m) * (2*n + m). (* .unfold *)
  hammer. (* .unfold *)
Abort.

Theorem nat_thing : forall n m, (n + m) * (2*n*n + n*m) = (n*n + n*m) * (2*n + m). (* .unfold *)
  sauto. (* .unfold *)
Qed.

(*|
What happened there? What ``hammer`` does, is it sends all theorems that are available to us, as well
as the current hypotheses and goal, to an ATP (on my machine, probably CVC4 or Z3). It asks the ATP
if it can prove the current goal, and if so which helper lemmas did it use to prove it. If
the ATP was unable to prove the current goal, Hammer will ask the next available ATP if it can prove
it. If any available ATP responds back with a proof and a list of theorems it used, then Hammer
will attempt to reconstruct that proof in Coq. Now, not all reconstructions will work, mainly
due to the fact that Coq is based off of an intuitionistic logic, and most ATPs are based off of
classical logics. But the vast majority will work.

<<<<<<< HEAD
Actually, what happened here was somewhat simpler: Hammer was able to solve this goal using only its
builtin tactics written in Coq. Blast! Okay, let's try something even gnarlier:
|*)

Require Import PeanoNat.
Theorem n_or_Sn_Odd : forall (n : nat), Nat.Odd n \/ Nat.Odd (n + 1).
  predict 1.
  hammer.
=======
Tactician
*********
|*)
>>>>>>> c1e1282 (A)
