---
layout: post
title:  "CAP Theorem and Related"
date:   2014-09-09 11:23:41
permalink: cap-theorem-notes.html
---

My intention in writing this note is to understand the relation
between conventional model of distributed systems that they usually
teach in the distributed systems course and the the distributed web
services hosting replicated datatypes. Fault tolerance is a concern in
the former, and it is studied separately from communication link
failures. On the other hand, partition tolerance is a concern in the
later, and it looks like this means tolerance to communication
failures.  Consistency and availability are major concerns in
distributed web services, whereas they don't figure anywhere in the
formal study of distributed systems. What is the connection? How can
we express CAP theorem in conventional models?

### The System Model ###

The conventional model of a distributed system is that of a replicated
state machine (automaton), where the automaton models a local
computation that _reacts_ to external messages. This makes it clear
that the focus in conventional model is on how to perform a replicated
computation rather than on how to maintain replicated data.

![TRLifeCycle]({{ site.baseurl }}/assets/distributed-automata.png)

The above image is taken from Reliable Distributed Systems textbook. 

This view is also corroborated by Eric Brewer in his PODC'2000 talk,
where he conjectured CAP. Here are some exerpts from his
([slides](http://www.cs.berkeley.edu/~brewer/cs262b-2004/PODC-keynote.pdf)):

<pre>
Inktomi builds distributed systems ... but very little use of
classic DS research.

"Distributed Systems" don't work

Persistent state is hard. Classic DS focuses on computation, not
data. This is WRONG; computation is the easy part.
</pre>

The semantics of a distributed system that is intented to maintain
replicated data is best captured in Burckhardt et al's POPL'14 paper.
Since we are familiar with the model, I am not going to reproduce it
here.


### Communication Links and Failures ###

In the conventional model, process is the unit of communication and
the the unit of failure. It is assumed that there is a one-to-one
communication link between every pair of processes in the system.
Conventional model allows for processes to fail. The widely used model
of process failure is crash-stop, where a process crashes and stops,
and therefore becomes inaccessible. A communication link may also
fail, but this failure shows up as a process failure - processes at
both ends of a link preceive each other as failed processes. However,
other processes may still view them as correct processes, and the
conventional model allows for this disparity in processes' view of
what other processes have failed. 

Replicated data stores are usually geo-distributed, so there do not
exist one-to-one links between processes. Processes are organized into
subnets, which are often connected through a single communication
link. Therefore, in distributed web services model, a communication
link is considered a unit of failure. Failure of a link can cause
network to be _paritioned_ into disconnected subnets, and web-services
are often required to tolerate these partitions. For most purposes, a
process failure can also be modeled as network partitioning by simply
assuming that the failed process is in its own parition. In summary,
in distributed webservices model, faults occur in communication links
thereby leading to network partitions, and fault tolerance effectively
means partition tolerance.

### Timing Assumptions ###

Both conventional and current models of a distributed system are
asynchronous models - they do not make any assumptions about time
bounds on communication delays or (relative) process speeds. In both
the models, we rely on logical clocks (eg: vector clocks) and causal
ordering to understand the behaviour of the system with respect to
passage of time.

### Consistency & Availability ###

Ideally, a distributed web-service has to be consistent in the sense
that it should behave the same as if it is operating on an atomic data
object. Any operation performed on the data object should see the
effects of all previous operations. For example, consider a
web-service for a simple read/write register. The operations allowed
are _write_ and _read_, which write a value to the register and read
the current value in the register, respectively. Let us assume that
the client performs two successful writes of values 20 and 40 to the
register. Then a subsequent _read_ should return 40, failing which the
system is deemed inconsistent. This kind of consistency guarantee is
called _strong consistency_ or _sequential consistency_. Under this
consistency guarantee, there must exist a total order on all
operations such that each operation looks as if it were completed at a
single instance. 

Along with being consistent, a distributed web-service needs to be
available - every request made to the web-service should be met
with a response, given that the web-service remains accessible on the
network. To be available, no non-failing node in the distributed
system implementing the web-service should wait infinitely for an
event to occur before responding to a client request.

CAP theorem says that it is impossible to guarantee (strong)
consistency and availability in a system that needs to be partition
tolerant. First, let us see if this makes sense intuitively. Consider
the read/write register web-service described previously. Assume that
it is being implemented by a distributed system with two
geo-distributed nodes, each holding a replica of the register.
Consider a client which makes following requests to the web-service in
the order shown:

    1. write 20
    2. write 40
    3. read

The order is called session order. Let us tag each request with is
serial number in session order. Assume that `write 20` goes to first
node, which immediately writes 20 to the local register and
simlutatenously forwards the request to second node. Now, should the
first node wait for the acknowledgement from second node before
responding to the client? Given that we are operating in an
asynchronous environment and there is no time bound on the delivery of
acknowledgement, the wait time for first node could potentially be
infinite. This leads to the violation of the availability guarantee.
Therefore, the node should respond immediately to the client, and use
timeouts and retransmissions to eventually propagate client request to
the second node.   

Consider a scenario where second write request (`write 40`) also goes
to first node, but the `read` request goes to the second node. Assume
that by the time `read` request was made to second node, it already
received the `write 20` request forwarded by the first node. Looking
at their serial numbers (1 for `write 20` and 3 for `read`), the
second node knows that there is a request made by the client before
the `read` that it has not yet received. This missing request
could be a `write` (it is indeed a `write` in this case). Therefore,
if the node has to respond with a correct value for the `read` request
, it has to wait until it receives the missing request, in which case
it might have to wait infinitely as network may get partioned in
meantime. This violates availability. The other option is to respond
with the current value of the register without waiting for the second
request to be delivered. In this case, the client reads 20 instead of
the expected 40, which means that the system is no longer (strongly)
consistent. Therefore, it is impossible for our service to be both
available and consistent in presence of network partitions. 

### Consistency & Avalability in Conventional Model ###

The conventional model accounts for network partitioning through
process failures - A faulty process that stops communicating with rest
of the processes in the system effectively leads to network
partitioning.  Fault tolerance is the ability of a system to behave in
well-defined manner once faults occur. There has been an extensive
research on fault tolerance in conventional models, but does this
research include a study of consistency and availability properties in
presence of faults? 

The answer is yes. They were studied under broad categories of safety
and liveness properties, respectively.  A safety property of a system
is usually expressed as a set of legal system configurations, commonly
referred to as an _invariant_. To be safe, a system has to always
remain in the set of safe states as defined by the safety property.
Consistency is a safety property as it restricts the set of observable
states of the system. For the read/write register example, consistency
dictates that the observable state of the register after the first two
writes is the value 40. Any other state is inconsistent or unsafe. 

On the other hand, a liveness property claims that some good thing will
eventually happen during system execution. Liveness properties are
_eventuality_ properties - a traffic signal should _eventually_ allow
every car waiting at an intersection to pass through. Availability is
a liveness property, as it requires every request to be eventually met
with a response. In literature on fault tolerance, availability
property is more commonly referred to as _guaranteed service_.

Recall that fault tolerance is the ability of a system to behave in
well-defined manner once faults occur. In his landmark survey paper on
fault tolerance in distributed systems, Gartner identifies four
forms of fault tolerance based on which among safety (S) and liveness
(L) properties hold when faults occur in the system. The four are
listed below:

1. Masking fault tolerance: when both S and L hold in presence of
   faults
2. Fail-safe: when only S holds
3. Non-masking: when only L holds
4. None (or fault intolerant): when none of them hold.

Gartner's paper was published in 1999, before CAP was conjectured, and
before eventually consistent data stores proliferated. The paper
reflects the kind of applications that researchers had in mind when
studying distributed systems. These applications are quite different
from replicated data stores, which explains the disparity between
conventional models and current systems. Below, I reproduce some of
the relevant verbatim from the paper, which is suggestive of this
gulf:

<pre>
  fail-safe fault tolerance and is preferable to non-masking
  whenever safety is much more important than liveness. An example
  is the ground control system of the Ariane 5 space missile project
  [Dega 1996]. The system was masking fault tolerance for a single
  component failure, but was also designed to stop in a safe state
  whenever two successive component failures occurred [Dega 1996].
  For the latter type of faults, the launch of the missile
  (liveness) was less important than the protection of its pre-
  cious cargo and launch site (safety).

  ....

  In effect (of non-masking fault tolerance), the user may
  experience a certain amount of incorrect system behavior (i.e.,
  failures). For example, a calculation result will be wrong or a
  <b>replication variable may not be up to date</b>

  ....

  Research has traditionally focused on forms of fault tolerance
  that continuously ensure safety. This can be attributed to the
  fact that <b>in most fault-tolerance applications, safety is much
  more important than liveness</b>.

  ...

  For a long time nonmasking fault tolerance has been the “ugly
  duckling” in the field, as <b>application scenarios for this type of
  fault tolerance are not readily visible</b>. However, the potential of
  non-masking fault tolerance lies in the fact that it is strictly
  weaker than masking fault tolerance, and can therefore be used in
  cases where masking fault tolerance is too costly to implement or
  even <b>provably impossible</b>.

  ...

  (Talking about self-stabilizing programs, which are pre-cursors of
  eventually consistent programs) Examples show that such programs
  are quite difficult to construct and verify [Theel and Gärtner
  1998]. Also, their <b>nonmasking nature has inhibited them from yet
  becoming practically relevant</b>.

  ...
</pre>


In summary, the paper says that masking fault tolerance, where both
safety and liveness is preserved in presence of faults is "strictest
and most costly" form of fault tolerance, and that ensuring such
tolerence is a "major area of research". Instead, fail-safe fault
tolerance is preferable for most practical applications.

### The CAP Theorem ###

Now that we are aware of Gartner's categorization of fault tolerance,
we can state the CAP theorem simply as:

    It is impossible to have masking fault tolerance in an unreliable
    distributed system

In the words of Gilbert and Lynch, who gave the first the proof of the
theorem:

    The CAP Theorem, in this light, is simply one example of the
    fundamental fact that you cannot achieve both safety
    and liveness in an unreliable distributed system
          - From "Perspectives on the CAP Theorem"


It should therefore be noted that oft reproduced formulation of the
CAP theorem as "pick any two among Consistency, Availability and
Partition Tolerance" is misleading at best. A better formulation is:

    A distributed system that is network partition tolerant cannot be
    consistent and available at the same time.

So, it is more about picking one among the two rather than picking two
among the three. 

### Eventual Consistency & Its Impact on Availability ###

Bailis et al's paper on _Highly Available Transactions: Virtues and
Limitations_, classifies operations on a replicated data store as
unavailable, sticky-available and available. An operation, such as a
_write_ on read/write register, that has no requirements on
consistency is classified as available. This is expected, as _write_
can be applied to any replica without any need to wait for an event,
and the client can be informed of success/failure of write 


