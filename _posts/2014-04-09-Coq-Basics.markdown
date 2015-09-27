---
layout: post
title:  "Coq Basics"
permalink: coq-basics-1.html
---

GADTs vs Inductive Datatypes
============================

Consider the following definition of Nat-indexed Vector GADT in
OCaml and Haskell:
OCaml:
{% highlight ocaml %}
    (*  vec : * -> * -> * 
     *)
    type (_,_) vec =
    | Nil : ('a,zero) vec
    | Cons : 'a * ('a,'b) vec -> ('a,'b succ) vec
{% endhighlight %}

Haskell:
{% highlight haskell %}
    data Vec :: * -> Nat -> * where
      VNil :: Vec a 'Zero
      VCons :: a -> Vec a n -> Vec a ('Succ n)
{% endhighlight %}

Observe that quantified type variables in the type of constructors are
generalized by the type-constructor signature. Infact, this is not
always true. For example, consider the GADT for higher-order abstract
syntax:
{% highlight haskell %}
  data Exp :: * -> * where
   -- other constructors elided
    App :: Exp (a -> b) -> Exp a -> Exp b
{% endhighlight %}
The type scheme of _App_ contains a type variable (_a_) that is not
generalized by the type-constructor signature. 
{% highlight haskell %}
  App :: ∀a. ∀b. Exp (a -> b) -> Exp a -> Exp b
{% endhighlight %}
This type is treated as existential type when an expression of type
`Exp b` is destructed and matched agains `App`.

Therefore, the correct observation is this: All type variables
generalized by the signature of type constructor are also generalized
in type schemes of its value constructors.

Here is the nat-indexed vector inductive datatype in Coq:
{% highlight coq %}
Inductive vec : Type -> nat -> Type :=
  | vnil : forall A:Type, vec A O
  | vcons : forall A:Type, forall n:nat, A -> vec A n -> vec A (S n).
{% endhighlight %}
The above definition should be read as following: `vec` is a `Type`
indexed by a `Type` and a `nat`. Here are the only ways to construct
values of `Vec X N`, where X could be any `Type` and N could be any
`nat`:

+ For any `Type` _A_, `vnil A` is a value of `Vec A O`
+ For any `Type` _A_ and for any `nat` _n_, `vcons A n` accepts a
  value of type _A_, a value of type `vec A n`, and generates a value
  of type `Vec A (S n)`

Notice that it looks quite similar to Haskell definition, with type
variables explicated. An empty list in explicitly typed haskell is
`VNil Int`, whereas in Coq, it is `vnil int`. However, unlike Haskell,
where there is term-type-kind hierarcy, Coq has full dependent types 
with infinite hierarchy of universes. One consequence of this is that we
will frequently see arrows mapping members of one universe to members
of a different universe. For example, if we `Print vec.`, this is what
we see:

{% highlight coq %}
    Inductive vec : Type (* Top.59 *) -> nat -> Type (* max(Set, (Top.61)+1, (Top.62)+1) *) :=
      | vnil : forall A : Type (* Top.61 *), vec A 0
      | vcons : forall (A : Type (* Top.62 *)) (n : nat),
                   A -> vec A n -> vec A (S n)
{% endhighlight %}

Evidently, `vec` maps a member of Type(59) universe and member of Set
universe to a type universe at higher level. Compare this to the type
of `Vec` type-constructor in haskell `* -> * -> *`, which simply says
that when _a_ is a type, and _n_ is a type (i.e., _a_ and _n_ have
kind `*`), then `Vec a n` is a type (i.e., it has kind `*`).

In the inductive definition of `vec`, observe that both constructors
construct values of type `vec A _`. Therefore, we can as well
generalize _A_ at the type of type-constructor (here, this is a mere
syntactic convenience):

{% highlight coq %}
    Inductive vec2 (A : Type) : nat -> Type :=
      | vnil2 : vec2 A O
      | vcons2 : forall n:nat, A -> vec2 A n -> vec2 A (S n). 
{% endhighlight %}

The above definition should be read as following: `vec` is a `Type`
indexed by a `Type` _A_ and a `nat`. Here are the only ways to construct
values of `Vec A N`, where N could be any `nat` ...

Another consequence of having full dependent types in Coq is that the
type of inductive type-constructors can be dependent as well. For eg,
here is the inductive definition of `sig` datatype:

{% highlight coq %}
    Inductive sig (T : Type) (P : T -> Prop) : Type :=
        exist : forall x : T, P x -> sig T P
{% endhighlight %}
`sig T P` is the type of values of type _T_ that satisfy proposition
_P_. `sig` is a function on type, and propositions on _that_ type.
Observe that the type of second argument to type-constructor `sig`
depends on the value of its first argument.

How did we arrive at that type definition? Let us say we want to
define a refinement type for values of `nat` satisfying a predicate
_P_.  Effectively, we would like to index `nat` with a predicate _P_
over natural numbers. Since _P_ is a predicate, `P : nat -> Prop`. We
define a new `Type` _natST_ (read "nat, such that") that is indexed by
`P : nat -> Prop`:

{% highlight coq %}
    Inductive natST (P : nat -> Prop) : Type := ??
{% endhighlight %}

What should be its constructors? There has to be only one constructor
that, given a nat (_n_), and a proof that it satisfies the predicate
(i.e., proof of `P n`), returns evidence for `natST P`. In other
words, we have an evidence for `natST P` if and only if we have a nat,
and the evidence that it satisfies the predicate. Destructing a `natST
P` value would produce a nat and a proof that it satisfies _P_.

Type `natST` helps us easily write type for division operation:

{% highlight coq %}
    Definition natPos : Type := natST (fun n:nat => n>0).
    Definition div : nat -> natPos -> nat * nat.
    Admitted. Defined.
    (* equivalent type of div: *)
    Definition div2 : forall n:nat, n>0 -> nat -> (nat*nat),
    Admitted. Defined.
{% endhighlight %}


Implicit Arguments
=================

Following is to set the implicit arguments option in Coq.
{% highlight coq %}
    Set Implicit Arguments.
{% endhighlight %}
When the mode for automatic declaration of implicit arguments is on,
the default is to automatically set implicit only the strict implicit
arguments (eg: tyarg of `Cons` is strict implicit, whereas that of
`Nil` is contextual implicit). 

By default, Coq does not automatically set implicit the contextual
implicit arguments. To tell Coq to infer also contextual implicit
argument, use command

{% highlight coq %}
    Set Contextual Implicit.
{% endhighlight %}

Setting contextual implcit too may not infer ty annot for Nil. Why?
How does coq know whether we want to partially applied Nil or fully
apply it? Setting Maximal Implicit works, but that would prevent us
from writing certain partial function applications. Therefore, we
explciity set implicit args for Nil:

{% highlight coq %}
    Implicit Arguments Nil [X].
{% endhighlight %}

Notation, Associativity, and Precedence
=======================================

The level is for precedence. Assume for instance that we want
conjunction to bind more than disjunction. This is expressed by
assigning a precedence level to each notation, knowing that a lower
level binds more than a higher level. Hence the level for disjunction
must be higher than the level for conjunction. 100 is the highest
level. There is a special 200 level higher than 100.

Since connectives are the less tight articulation points of a text, it
is reasonable to choose levels not so far from the higher level which
is 100, for example 85 for disjunction and 80 for conjunction

The Omega Tactic
================

[Omega][omega] is a decision procedure for linear arithmetic (also
known as Presburger arithmetic). It can be used to discharge any silly
goals on nats and integers like:

$$S x = x + 1$$

Omega can deal with nats. It converts nats to integers. Following
operations on nat are recognized by omega:

+ Predicates, such as =, le, lt, gt, ge
+ Functions, such as +, minus, mult, pred, S, O

Omega needs to be imported:

{% highlight coq %}
    Require Import Omega.
{% endhighlight %}

apply and eapply tactics
========================

`apply H` tries to unify the current goal with conclusion of H.  If it
succeeds, it generates a sub-goal for each assumption (argument) of H.
For instance, in the following context:

{% highlight coq %}
     A : Type
    s1 : Ensemble A
    s2 : Ensemble A
    s3 : Ensemble A
    x : A
    H2 : In A s1 x
    ============================
     In A (Union A s1 (Union A s2 s3)) x
{% endhighlight %}

using `apply Union_introl`, where

{% highlight coq %}
    Union_introl
     : forall (U : Type) (B C : Ensemble U) (x : U),
       In U B x -> In U (Union U B C) x
{% endhighlight %}

unifies U with A, B with s1, C with (Union A s2 s3), and x with x to
generate following sub-goal:

{% highlight coq %}
       ....
     ============================
        In A s1 x
{% endhighlight %}

which is already an assumption.

The tactic `eapply` does the same, except that instead of failing due
to inability to instantiate variables, it replaces them with
existentials. When you have existential in you context, destruct it to
skolemize. The ?6201 style variables in goal when you use eapply are
actually existential variables. 

The Auto Tactic
===============

The [auto][auto] tactic solves goals that are solvable by any combination of

+ intros, and
+ apply.

By default, auto only does `apply` on local hypotheses. To add to the
global hint database of auto:

{% highlight coq %}
    Hint Resolve <Lemma-name>.
    Hint Resolve <Constructors of inductive prop>
    Hint Constructors A. <Hint Resolve for all constructors of A>
    Hint Unfold <A Definition>.
{% endhighlight %}
One can optionally declare a hint database using the command `Create
HintDb`.

To see hints applicable in the current context, and list of all hints,
respectively:

{% highlight coq %}
    Print Hint.
    Print Hint *.
{% endhighlight %}


Using auto tactic with database of hints named sets:

{% highlight coq %}
    auto with sets.
{% endhighlight %}

You can extened hint DB for one application of auto with `using`
keyword. To extend with `Union_introl`:

{% highlight coq %}
    auto using Union_introl.
{% endhighlight %}

To extend with all constructors of `Union`:

{% highlight coq %}
    auto using Union.
{% endhighlight %}

More avatars of auto:

+ `trivial` tactic - non recursive auto. depth =0.
+ `autounfold` and `autorewrite` to use `Hint Unfold` and `Hint
  Rewrite` hints in the hint database.

Auto Examples
------------

Completely manual proof for theorem union\_is\_associative: 

{% highlight coq %}
    Theorem union_is_associative : forall A : Type, forall s1 s2 s3 : Ensemble A,
                         Union _ (Union _ s1 s2) s3 = Union _ s1 (Union _ s2 s3).
    Proof.
      intros; eapply Extensionality_Ensembles. unfold Same_set.
      unfold Included. split.
        intros; inversion H.
            inversion H0. Check Union_introl. apply Union_introl. assumption.
            apply Union_intror. apply Union_introl. assumption.
            apply Union_intror. apply Union_intror. assumption.
        intros. inversion H.
            apply Union_introl. apply Union_introl. assumption.
            inversion H0. 
              apply Union_introl. apply Union_intror; assumption. 
              apply Union_intror. assumption.
    Qed.
{% endhighlight %}

Proof with auto:

{% highlight coq %}
    Proof.
      intros. apply Extensionality_Ensembles. unfold Same_set.
      unfold Included. split; intros ? H; inversion H;
        [ inversion H0; auto with sets | auto with sets |
         auto with sets | inversion H0; auto with sets].
    Qed.
{% endhighlight %}

Even simpler auto proof:

{% highlight coq %}
    Proof.
      intros. apply Extensionality_Ensembles. unfold Same_set.
      unfold Included. split; intros ? H; inversion H; subst;
        try (inversion H0); auto with sets.
    Qed.
{% endhighlight %}

SF automation chapter ([sfauto][sfauto])says this on `auto`:

> Note that proof search tactics never perform any rewriting step
> (tactics rewrite, subst), nor any case analysis on an arbitrary data
> structure or predicate (tactics destruct and inversion), nor any
> proof by induction (tactic induction). So, proof search is really
> intended to automate the final steps from the various branches of a
> proof. It is not able to discover the overall structure of a proof.

The Solve Tactical
==================

Solve tactical takes a list of tactics, and tries them left to right,
stopping when a tactic is successful. If none of the tactics are
successful, the solve fails. 

{% highlight coq %}
    solve [inversion H | inversion H1].
{% endhighlight %}

The difference between `try solve [e1 | e2]' and `try e1; try e2` is
the short-cut behaviour of solve.

The Intuition Tactical
=====================

`Intuition t` applies propositional decision procedure to simplify the
goal, and then applies tactic `t` on the resultant. 

+ `intuition fail` succeeds if the goal is a propositional tautology.
  Fails otherwise. This is equivalent to `tauto` tactic.
+ Simply using `intuition` is equivalent to using `intuition auto with \*`.

Notes:
======

+ To instantiate a universally quantified hypothesis H on variable n,
  just do (H n). Eg: `destruct (H n).`
+ When there is ambiguity about which term `rewrite` rewrites when
  there are multiple rewritable terms in the goal, assert the required
  hypothesis as a separate assertion, and prove it (using apply).
+ It is futile to define strong lemmas with conjunction in consequent.
  Not only that applying them is difficult, but also that `auto` only
  tries such lemmas when current goal is a conjunction at top level.
  Instead, define two separate lemmas.

References:
===========

+ [Universes chapter][cptd-universes] in CPDT.

[cptd-universes]: http://adam.chlipala.net/cpdt/html/Universes.html
[omega]: http://coq.inria.fr/refman/Reference-Manual023.html
[auto]: http://coq.inria.fr/refman/Reference-Manual010.html#sec400
[sfauto]: http://www.cis.upenn.edu/~bcpierce/sf/UseAuto.html
