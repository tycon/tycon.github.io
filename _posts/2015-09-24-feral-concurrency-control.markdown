---
layout: post
comments: true
title:  "Notes - Feral Concurrency Control"
permalink: feral-concurrency-control.html
---

This post is a compilation of my notes on Peter Bailis et al's
SIGMOD'15 paper: Feral Concurrency Control: An Empirical Investigation
of Modern Application Integrity.

### Background ###

Modern relational DBMs offer a range of primitives to help the
developer ensure application integrity, even under the presence of
concurrency: built-in integrity constraints (e.g: `UNIQUE`, `NOT
NULL`, `FOREIGN KEY`), triggers, stored procedures to implement
application-specific integrity constraints, optimistic/pessimistic
locking of rows, serializable transactions etc. However, modern web
application frameworks (e.g: Ruby on Rails), which promote ORM-based
programming, refrain from using most of the primitives provided by the
DB layer, instead choosing to reimplement them in the application
layer.  Consider Ruby on Rails for instance, which is an MVC web
framework.  Ruby on Rails lets application developers specify their
data model (M in MVC) as a set of classes that implement Rails' native
`ActiveRecord` class. The data model can also contain application
integrity constraints in form of _validations_ and _associations_. For
example, `presence` and `uniqueness` are a couple of validations, and
`belongs_to` and `has_many` are a couple of associations supported
natively by Rails. Rails implements object-relational mapping (ORM) by
automatically mapping the classes (resp. objects) that constitute the
data model (resp. data) to relations (resp.  tuples) in the underlying
DB, provided that the application code adheres to some pre-defined
naming conventions. However, validations and associations are not
mapped to corresponding itegrity constraints at the DB level. For
instance, `uniqueness` validation is not mapped to MySQL `UNIQUE`
primitive, but instead implemented by rails by performing a `SELECT`
query and making sure that the record being inserted is not already
present (all this is done within a transaction). Likewise, instead of
mapping `belongs_to` association to `FOREIGN KEY` constraint native to
DB, rails implements it by running a `SELECT WHERE` query to check
that the key being referred to is indeed present. 

Eschewing native database integrity and concurrency control solutions,
Rails has developed a set of primitives for handling application
integrity at the application level itself, thereby building, from the
perspective of the underlying DB, a feral concurrency control system.
The motivation behind this apparent irrationality is to enhance
maintainability of the system, and to facilitate testing. Let me
elaborate:

* _Maintainability_: The set of available integrity and concurreny control
  mechanisms at the database layer depends on the data model employed
  by the underlying database, and also, in some cases, on the vendor.
  For instance, while relational data model supports foreign key
  constraints as a means to implement referential integrity, data
  models employed by weakly consistent data stores do not. Even among
  relational data stores, some (e.g: PostgresSQL) support foreign key
  constraints, while some other (e.g: MySQL's MyISAM and NDB storage
  engines) do not. Likewise, the `CHECK` constraint used to check
  domain-specific integrity constraints, such as `bal ≥ 0`, is
  supported by PostgresSQL, but not supported by MySQL. Futhermore,
  besides standard validations and associations, such as uniqueness
  and foreign key constraints, Rails allows developers to define
  application-specific validations and associations, for which the
  corresponding native primitives may not exist, and even if they
  exist, it is not clear how to do the mapping. To make matters worse,
  DB systems usually silently ignore any constraint that they do not
  support.  Therefore, an application that relies on DB's native
  constraints to enfore integrity risks correctness, is not portable,
  and is consequently difficult to maintain.
* _Testing_: Database's referential integrity constraints "get in the
  way of" testing by insisting that test data be inserted/deleted
  into/from the database in a specific order such that the integrity
  is never violated. In many cases, developers want to simply _dump_
  the sample data (known to be consistent) into the database and get
  along with testing their application. Requiring that such data still
  be inserted/deleted respecting referential integrity might be an
  overkill.

<!--
  The default transaction isolation level in PostgresSQL is RC,
  whereas in MySQL it is RR. Clearly, counting on DB's transaction
  primitive does not help in ensuring deterministic application
  behaviour, but doesn't Rails's transaction construct default to
  DB's?  
-->
The aforementioned reasons, along with some personal convictions of
its creators, has motivated Rails to eschew concurrency and integrity
controlling mechanisms at the database layer, and view it simply as a
table storage. This approach of Rails has been hugely successful, as
evident from its large-scale adoption.

Replacing database native primitives with feral mechanisms may improve
maintainability of the application, but does it really work? Are the
feral invariants correctly enforced in Rails? Do they work in
practice? This paper performs theoretical analysis and emperical
studies to answer these questions.

### How prevalent are feral mechanisms in practice? ###

They are quite prevalent. Analyzing a corpus of 67 popular opensource
web applications, authors found that applications, on average, used
just 3.8 transactions against 52.4 validations and 92.8 associations
(median could've been a better metric). The overwhelming number of
associations relative to transactions indicates that Rails developers
use associations to perform referential integrity preserving
insertions into multiple tables, which is otherwise performed in a
transaction.

### Rails Concurrency Control Mechanisms ###

Implementing validations (e.g: `uniqueness`) and associations (e.g:
`belongs_to`) in the application layer is trivially safe in the
sequential setting. But, in the presence of concurrent client requests
attempting to modify the database simultaneosly, some concurrency
control mechanisms are needed in order to ensure that validations and
associations are indeed being enforced correctly. Otherwise, data
integrity is jeopardized. Towards this end, Rails does the following:

* When a model state is being updated (for e.g., during an insertion),
  Rails runs all the validations on the model sequentially, in a
  (database-backed) transaction. The rationale is to rely on ACID
  guarantees of the transaction to ensure the correctness of
  validation. For instance, uniqueness validation (by issuing a
  `SELECT` query to the database) is performed within a transaction so
  as to preempt concurrent insertions that may result in duplicates. 
* Associations are _validated_ in the similar way: by enclosing the
  the corresponding validations inside a transaction.

If transactions are serializable as expected, then validations are
indeed safe. However, databases do not offer serializable transactions
by default (the default isolation level in PostgresSQL is RC. In
MySQL, it is RR.), and, in some cases, they do not offer
serializability at all. Given the possibility of concurrent
transactions under weaker isolation levels (for e.g., RC ensures that
visible transactions are entirely visible. It doesn't guarantee total
order among transactions.), Rails validations may not really ensure
the validity of data. Examples:

* Concurrent `uniqueness` validations can independently succeed, thus
  allowing concurrent duplicate insertions.
* Association (e.g: foreign key) checking in one transaction, and
  record deletion in a concurrent transaction can independently
  succeed, thus compromising referential integrity.

Rails acknowledges these anomalies. The documentation warns that
`uniqueness` validation can still occassionally admit duplicates, and
association validation can occassionally result in violation of
referential integrity.

### How likely are these anomalies in practice? ###

Not very likely. For instance, in LinkBench workload capturing
Facebook's MySQL record access pattern, with 64 concurrent clients
issuing 100 insert requests per second on 1000 different keys, an
average of 10 duplicate records were observed when `uniqueness`
validation is turned on. In less adversarial production workload, we
may get much less number of duplicates, or maybe no duplicates.
Therefore, it may be argued that validations are "good enough" for
many web applications, where correctness is not a top priority.

However, concurrency is not the only reason for incorrect application
behaviour. Quite often, anomalies might also result because of the
incorrect implementation of a validation/association in Rails
framework, or because of some non-trivial interactions between various
application-level validations that Rails developers haven't foreseen.
For instance, in Rails, `delete_all` operation, unlike the `delete`
operation, doesn't create objects for rows it is deleting, thus
failing to perform validations on the data being deleted (note:
validations are performed only when a data model _object_ is updated).
This could result in the violation of referential integrity, resulting
in http error messages being shown to user, as in the case of
[thoughtbot][thoughtbot], a popular blogging platform. Thoughtbot has
since started relying on PostgresSQL's foreign key constraints to
enforce referential integrity. Similar experiences have prompted few
other Rails users to start a forum called _Rails devs for data
integrity_ ([ref][snowgiraffe]) that advocates strengthening Rails
validations with database-backed checks.


### What can be done about the anomalies? ###

Most databases natively support `UNIQUE` constraint, which ensures
absence of duplicates at no extra expense. It is therefore a shame if
one is forced to choose an incorrect implementation instead of a
similar performing correct implementation just for software
engineering reasons. Can something be done about this?

One solution is to insist that all validations are done inside
serializable transactions (i.e., choose serializability instead of the
default RC or RR isolation level at the database layer). This
trivially ensures correctness of all feral implementations.
Unfortunately, serializability comes at the cost of availability,
which is a more important in the context of web applications.
Moreover, the study finds that 75% of application invariants do not
need serializability for correct enforcement. Imposing serializability
by default is therefore unjustified.

The paper concludes that there is currently no database-backed
solution that "respects and assists with application programmer
desires for a clean, idiomatic way means of expressing correctness
criteria in domain logic". Authors believe that "there is an
opportunity and pressing need to build systems that provide all three
criteria: performance, correctness, and programmability." To
domesticate feral mechanisms, the authors argue, application users and
framework authors need a __new database interface__ that will enable them
to:

1. Express correctness criteria in the language of their domain model,
   with minimal friction, while permitting their automatic
   enforcement. Any solution to domestication must respect ORM
   application patterns and programming style, including the _ability
   to specify invariants in each framework's native language_. An
   ideal solution for domestication should provide _universal_ support
   to applications' feral invariants with _no_ additional overhead for
   application developers.
2. Only pay the price of coordination when necessary. As already
   discussed, serializable transactions only when needed.
3. Easily deploy the framework/application across multiple database
   backends. For example, the interface must allow Rails to talk to a
   relational store, as well as a key-value store.

Notes
-----

"Rails can’t be trusted to maintain referential integrity, but you
know what’s really good at doing that? Our relational database." -
[thoughtbot][thoughtbot]

"Even when both systems are configured to one of the strict levels of
transaction locking, the differences between the two implementations
are subtle enough that which implementation will work better for a
particular application is hard to state definitively. "- [postgresql
wiki][postgresqlwiki].



[thoughtbot]: https://robots.thoughtbot.com/referential-integrity-with-foreign-keys
[snowgiraffe]: http://www.snowgiraffe.com/tech/462/rails-devs-for-foreign-keys/
[postgresqlwiki]: https://wiki.postgresql.org/wiki/Why_PostgreSQL_Instead_of_MySQL:_Comparing_Reliability_and_Speed_in_2007
