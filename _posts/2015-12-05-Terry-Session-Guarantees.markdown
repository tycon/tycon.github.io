---
layout: post
title:  "Notes - Terry's Session Guarantees"
comments: true
permalink: terry-session-guarantees.html
---

This post is the compilaton of my notes on Terry et al's PDIS'94
paper: Session Guarantees for Weakly Consistent Replicated Data.

### System Model ####

From what I understand, the paper is the first to describe the
abstract system model of a weakly consistent replicated database that
now serves as a frame of reference to describe KV stores (eg.,
Cassandra and Riak) and mobile computational nodes. The abstract
system model is very similar to [Quelea][quelea]'s system model
described in Sec.2 of the [PLDI paper][paper]. Like in Quelea, where
the state of an application at a replica \\(r\\) is the set of
application-specific effects present at that replica (i.e., \\({\sf
vis}\\) set at \\(r\\)), the application state at server \\(S\\) in
Terry's model the collection of app-specific _Write_'s at \\(S\\)
(denoted \\(DB(S)\\)). Following is a more detailed comparison:

+ A Write in Terry's model is an abstraction of creation, updatation,
  or deletion of concrete data items (collectively called _CUD_
  operations). Hence, multiple Write operations need not commute. The
  \\({\sf WriteOrder}\\) therefore assumes significance. A Write in
  Quelea is an abstraction of a single atomic _effect_. Quelea's
  model in general encourages commutative Writes, and the model does
  not have a built-in notion of a \\({\sf WriteOrder}\\). Application
  state in Quelea is a _set_ of effects, and the result of a Read
  operation is obtained by folding over this set. Nonetheless, Quelea
  model does not preempt CUD operations; it is possible to write
  applications with Read, Write and Delete operations, such as
  registers, in Quelea. However, applications have to implement their
  own mechanisms (eg., tagging effects with local timestamps) and
  conflict resolution semantics (eg., Last-Writer-Wins) to ensure
  convergence. 
+ Both models rely on _total propagation_ and _consistent ordering_ to
  ensure eventual consistency. Total propagation can be achieved via
  _anti-entropy_ mechanisms such as hinted-handoff and read-repair
  (more about these in [this paper][uiucpaper]). In Quelea's
  implementation, this is taken care by Cassandra. No further
  assumptions about total propagation are made. Consistent ordering
  for non-commutative writes is essential for convergence. Both models
  rely on application semantics to consistently order writes at all
  replicas. However, while Terry's abstract model takes cognisance of
  the write order via the binary \\({\sf WriteOrder}\\) predicate,
  Quelea's model (intriguingly) does not. 
+ A Write in Terry's model is an abstraction of _multiple_ CUD
  operations, which appear to take place atomically. Hence, Terry's
  Writes are in fact transactions with RC isolation level.

### Session Guarantees ###

In Terry's and Quelea's perspective, a _session_ is an abstraction of
a sequence of Read and Write operations performed during the execution
of an application. Note that operations from the same client session
can be dispatched to different replicas, hence the result of a read
operation in a session may not be consistent with the write operations
performed previously in the same session. This could be very annoying
to the end user. The purpose of the paper is to equip the
aforedescribed abstract system model with additional guarantees that
collectively ensure that the __results of operations performed in a
session will be consistent with the model of a single centralized
server, possibly being read and updated concurrently by multiple
clients__.

Terry et al propose four session guarantees for their model, and, due
to the close correspondence between both models, they can also be
(nearly) stated as specifications in Quelea's spec language. Below, I
present both versions (Note: what Terry calls \\({\sf
RelevantWrites}\\), Quelea calls\\({\sf Visibility}\\)):

+ __Read Your Writes__: If Read \\(R\\) follows Write \\(W\\) in a session
  and \\(R\\) is performed at server \\(S\\) at time \\(t\\), then
  \\(W\\) is included in \\(DB(S,t)\\).
  + \\(\forall a,b.\, {\sf soo}(a,b) \Rightarrow {\sf vis}(a,b)\\)
+ __Monotonic Reads__: If Read \\(R_1\\) occurs before \\(R_2\\) in a
  session and \\(R_1\\) accesses server \\(S_1\\) at time \\(t_1\\)
  and \\(R_2\\) accesses server \\(S_2\\) at time \\(t_2\\), then
  \\({\sf RelevantWrites(S_1,t_1,R_1)}\\) is a subset of
  \\(DB_{}(S_2,t_2)\\).
  + \\(\forall a,b,c.\, {\sf vis}(a,b) ~\wedge~ {\sf soo}(b,c)
    \Rightarrow {\sf vis}(a,b)\\)
+ __Writes Follow Reads__: If Read \\(R_1\\) precedes Write \\(W_2\\)
  in a session and \\(R_1\\) is performed at server \\(S_1\\) at time
  \\(t_1\\), then, for any server \\(S_2\\), if \\(W_2\\) is in
  \\(DB(S_2)\\) then any \\(W_1\\) in \\({\sf RelevantWrites}(S_1,t_1,R_1)\\) is also in \\(DB(S_2)\\) and
  \\({\sf WriteOrder_{}}(W_1,W_2)\\).
  + \\(\forall a,b,c,d.\, {\sf vis}(a,b) ~\wedge~ {\sf soo}(b,c) ~\wedge~ 
       {\sf vis}(c,d) \Rightarrow {\sf vis}(a,d) ~\wedge~ ?{\sf
       WriteOrder}(a,c) \\).
+ __Monotonic Writes__: If Write \\(W_1\\) precedes Write \\(W_2\\) in
  a session, then, for any server \\(S_2\\), if \\(W_2\\) in
  \\(DB(S_2)\\) then \\(W_1\\) is also in \\(DB(S_2)\\) and \\({\sf
  WriteOrder_{}}(W_1,W_2)\\).
  + \\(\forall a,b,c.\, {\sf soo}(a,b) ~\wedge~ {\sf vis}(b,c)
    \Rightarrow {\sf vis}(a,c) ~\wedge~ ?{\sf WriteOrder}(a,b)\\).

<!-- _The only difference is that, while Quelea data store concretizes the
notion of a database as a log of effects, Terry's system model leaves
it abstract; a database is a set of _data items_, where a data item
could be anything from a conventional file to a tuple in a relational
database. -->

Observe that Terry's \\({\sf WriteOrder}\\) becomes \\(?{\sf
WriteOrder}\\) in Quelea. The punctuation is to explicitly denote the
fact that Quelea is unaware of \\({\sf WriteOrder}\\). To make the
matters worse, Quelea does not expose \\({\sf happens-before}\\) order
to application semantics. Consequently, a straightforward port of a
Bayou (Terry's system) application, which requires WFR or MW session
guarantee, onto Quelea does not preserve application semantics.

__Example__ Alice tweets "The chicken laid an egg". Bob sees Alice's
tweet and tweets "A chicken hatched out of the egg". If `GetTweets` is
tagged with WFR spec in Quelea, then Cheryl, who sees Bob's tweet is
also guaranteed to see Alice's tweet. However, she canot figure out
the causal order among the tweets making her wonder what comes first:
Alice's chicken, or Bob's egg.

How do we overcome the handicap described above? Some thoughts:

1. The state of an application that admits non-commutative operations
   is not an unordered set of effects, but a partially-ordered set of
   effects with respect to the \\({\sf happens-before}\\) relation.
   Accordingly, Read operations in Quelea must reduce over a graph
   representing the poset, but not a list representing a set.
2. Is there a way to explicitly track causality by tagging effects
   with vector clocks? Since each component of the vector must
   represent the monotonically increasing clock local to a replica,
   and there is no way to know the `currentReplicaId` in Quelea, this
   approach seems implausible. However, `getCurrentReplicaId` is a
   simple extension to Quelea, hence supporting this approach is easy.
   Unfortunately, explicitly tracking vector clocks is tedious and
   complicates application logic. Hence, first approach may be
   preferable.



[quelea]: http://gowthamk.github.io/Quelea/
[paper]: http://gowthamk.github.io/docs/quelea.pdf
[uiucpaper]: http://web.engr.illinois.edu/~garg11/papers/eventual_consistency.pdf

