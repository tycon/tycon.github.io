---
layout: post
title:  "Extraction in Coq"
permalink: coq-extraction.html
---

### Extraction erases Props ###

Extraction in Coq works by erasing `Prop`s. For example, consider the
following definition of `div`:

{% highlight Ocaml %}
    Definition div (m n : nat)(H : n<>0): nat :=
      NPeano.div m n.
{% endhighlight %}

`div` expects a proof that its second argument is non-zero. Indeed, in
coq, it is impossible for `div` to divide by zero. However, when this
code is extracted to OCaml, the `n <>0` prop is erased (Coq renames our
`div` to `div0` to avoid name clash with `NPeano`'s `div`):

    let div0 m n = div m n

#### Sumbool ####

Coq's `sumbool` type is another good example to demonstrate the proof
erasing nature of extraction. `sumbool` is defined in `Specif` module
as following:

    (** [sumbool] is a boolean type equipped with the justification of
        their value *)

    Inductive sumbool (A B:Prop) : Set :=
      | left : A -> {A} + {B}
      | right : B -> {A} + {B}
     where "{ A } + { B }" := (sumbool A B) : type_scope.

`sumbool` is usually the return type of equality decision procedures
of various types. For example, the `string_dec`, the string equality
function has the type:

      forall s1 s2 : string, {s1 = s2} + {s1 <> s2}

Consider a type `id` defined as:

      Inductive id : Type :=
        T : string -> t.

A decision procedure `id`s can be constructed from `string_dec` as
following:

     Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
      Proof.
         intros id1 id2.
         destruct id1 as [n1]. destruct id2 as [n2].
         destruct (string_dec n1 n2) as [Heq | Hneq].
         Case "n1 = n2".
           left. rewrite Heq. reflexivity.
         Case "n1 <> n2".
           right. intros contra. inversion contra. apply Hneq. apply H0.
      Defined 

Extracting the `sumbool` and `eq_id_dec` generates the following:

{% highlight ocaml %}
      type sumbool =
      | Left
      | Right
      (** val eq_id_dec : t -> t -> sumbool **
      let eq_id_dec id1 id2 =
        string_dec id1 id2
{% endhighlight %}

OCaml's `sumbool` has no arguments because coq's `sumbool` has only
`Prop` arguments. The advantage of using `sumbool` instead of `bool`
is that it can be used seamlessly in proofs and computations. When
used in a computation, sumbool simply tells whether a property is true
or false, but when used in a proof, sumbool also tells _why_ a
property is true or false.

#### Theorems can also be extracted #####

Observe that `eq_id_dec` has been written as a theorem. `Theorem` can
be used to assert the existence of a witness to, not only `Prop`s, but
also `Set`s and `Type`s. For example:

      Theorem there_is_a_nat : nat.
      Proof.  apply 0.  Defined.

      Extraction there_is_a_nat.
      (* 
        let there_is_a_nat = O
      *)

Why do we say `Defined` instead of `Qed` whenever we are doing
extraction? `Qed` defines proof/definition as opaque, whereas
`Defined` defines it as transparent. If we used `Qed` instead of
`Defined` extraction would produce:

    (** val there_is_a_nat : nat **)

    let there_is_a_nat =
      failwith "AXIOM TO BE REALIZED"

Note that theorems can only be extracted if the statement is either
`Set` or a `Type`, not `Prop`. The following two examples should
demonstrate this point. Example 1:

      Theorem there_is_plus: forall (n1 n2 : nat), exists (n :nat), n = n1 + n2.
      Proof.  intros.  exists (n1+n2).  reflexivity.
      Defined.

      Check (forall (n1 n2 : nat), exists (n :nat), n = n1 + n2). (* Prop *)

      Extraction there_is_plus.
      (*
          (** val there_is_plus : __ **)

          let there_is_plus =
            __
      *)

Contrast Example 1 with the following Example 2:


      Inductive plus_defined (n1 n2: nat) : Set :=
        | PlusT : forall(n:nat), (n=n1+n2) -> plus_defined n1 n2.

      Extraction plus_defined.
      (*
          type plus_defined =
            nat (* singleton inductive, whose constructor was PlusT *)
      *)

      Theorem there_is_plus_t: forall (n1 n2 : nat), plus_defined n1 n2.
      Proof.  intros.
      apply PlusT with (n:=n1+n2); reflexivity.
      Defined.

      Extraction there_is_plus_t.
      (*
        let there_is_plus_t n1 n2 = plus n1 n2
      *)

Why would anyone want to write a `Set` or a `Type` term as a proof of
a theorem, rather than a Definition or a Fixpoint? If the `Set` or
`Type` term expects `Prop` witnesses (like `sumbool`), then its better
to write it as a proof. Sometimes, it may not even be possible to
write the term otherwise. For example, here is a failed attempt at
defining `eq_id_dec` as a Definition:

      Inductive id : Type :=
        T : string -> t.

      Theorem eq1 : forall (s1 s2: string), s1=s2 -> (T s1) = (T s2).
      Proof.
        intros.
        subst. reflexivity.
      Qed.

      Theorem neq1 : forall (s1 s2 : string), s1<>s2 -> (T s1) <> (T s2).
      Proof.
      unfold not.
      intros.
      apply H; inversion H0. subst; reflexivity.
      Qed.

      Definition id_eq (id1 id2 : id) : ({id1 = id2}+{id1 <> id2}) :=
        match (id1,id2) with
        | (T s1,T s2) => match string_dec s1 s2 with
                         | left A => left (eq1 s1 s2 A)
                         | right B => right (neq1 s1 s2 B)
                         end
        end.

The approach fails because the term `left (eq1 s1 s2 A)`, which has
the type `{T s1 = T s2} + {?66}`, fails to type check agains the
required type `{id1 = id2} + {id1 <> id2}`. The problem is that while
pattern matching under a definition, coq does not populate the context
with equalities between scrutinees and patterns. Although we know that
`id1 = T s1` and `id2 = T s2`, we have no way of obtaining it from the
context. Recall that we did not face this problem when proving
`eq_id_dec`. This is why we sometimes prefer writing `Set` or `Type`
terms as proofs.


