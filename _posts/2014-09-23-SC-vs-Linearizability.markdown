---
layout: post
title:  "SC vs Linearizability"
permalink: sc-vs-linearizability.html
---

Sequential consistency requires that all data operations appear to
have executed atomically in some sequential order that is consistent
with the order seen at every individual process.

If instead of individual data operations, we apply sequential
consistency to transactions, the resultant condition is called
serializability in database theory.

Linearizability imposes more constraints on an order decided by
sequential consistency - the order needs to make sense to an external
observer. Let us say that an external observer is running two threads
`A` and `B`. If thread `A` performs action `a0`, then syncs with
thread `B` following which `B` performs `b0`. A sequentially
consistent execution can order `b0` before `a0`, as long as both `A`
and `B` perceive the same order. On the other hand, such an execution
is not valid under linearizability condition. Linearizability dictates
that an operation should take effect instantaneously before the
perceived end of the operation.

Evidently, linearizability is a stronger constraint than sequential
consistency (or serializability). Nevertheless, it is said that
linearizability is a local property (i.e., composable), sc is not.  (I
don't understand this. If you know what this means, please let me
know.)
