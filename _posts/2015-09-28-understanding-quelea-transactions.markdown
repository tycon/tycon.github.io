---
layout: post
title:  "Understanding Transactions in Quelea"
permalink: understanding-quelea-transactions.html
---

[Quelea][quelea] is our eventually consistent data store with an
associated programming framework intended to simplify programming
under eventual consistency. In this post, I describe how various
applications written in Quelea employ a combination of [highly
available][hat] and serializable transactions to enforce application
integrity. Three applications participate in this survey:

* [BankAccount][BankAccount]: A highly available concurrent bank
  account application.
* [Microblog][Microblog]: A twitter-like microblogging site, modeled
  after [Twissandra][Twissandra]. The application allows adding new users,
  adding and replying to tweets, following, unfollowing and blocking
  users, and fetching a user’s timeline, userline, followers and
  following.
* [Rubis][Rubis]: An eBay-like auction site. The application allows
  users to browse items, bid for items on sale, and pay for items from
  a wallet modeled after a bank account.

First let me define what I mean by a transaction:

### What is a transaction? ###

For all practical purposes, a transaction can be defined as a set of
operations on some data, which, when executed, appear to have been
executed simultaneously. We say that the set of operations has taken
effect atomically. Atomicity implies that the set of effects generated
by a transaction `T` is visible to operations in other transaction
`T'` in its entirety, or it is not visible at all.  From the
perspective of the other transaction `T'`, an operation `op'` in `T'`
either sees all the effects of a transaction `T`, or it sees none of
them. Note that this is the requirement of Read Committed (RC)
isolation level. Hence, atomicity being a defining property of a
transaction means that every transaction automatically experiences RC
isolation level. Note that a set of effects that offers atomicity, but
with stronger isolation properties than RC is also a transaction. 

Transactions are used for in various applications towards different
ends. Below, I describe some of the common purposes served by
transactions in some sample applications:

### To perform atomic updates ###

Transactions are primarily used in practice when we want to perform a
series of actions on the data taking it through some intermediary
states, where the integrity of data may be violated. In order to not
expose these intermediary states, we want to wrap these actions inside
a transaction so that, for observers, it appears as if all actions
have been committed atomically. Typically, these actions perform
updates to multiple tables or materialized views, or multiple rows in
the same table. Some usecases:

<!--(_models_, in ORM language)-->
<!--(ORM's objects)--> 

1. BankAccount:
  1. When a user saves money, then withdraw operation on the checking
     account, and deposit operation on the savings account should
     appear to have happened atomically. Intermediary state (after
     withdraw, but before deposit) may violate app-specific integrity
     constraints (e.g: user shown incorrect total bal, or user
     incorrectly penalized for insufficient bal etc).
2. Microblog (Twitter): 
  1. When a user (B) unfollows another user (A), then B has to be
     removed from A's follower list, and A has to be removed from B's
     following list. Both updates should appear to have happened
     atomically. Intermediate state violates app-specific integrity
     constraint that _follows_ is a symmetric relation.
  2. When a user tweets, the tweet should be added to the table of all
     tweets, and its Id should be added to the `userline` materialized
     view against tweeter's userId, and `timeline` materialized view
     against the userIds of all the followers. All insertions should
     appear to have happened simultaneously. Intermediary states may
     violate (a) app-specific integrity constraints (e.g: user B sees a
     tweet by A in his timeline, but doesn't find the tweet in A's
     userline), and (b) referential integrity (happens if data store
     can reorder operations, like in the case of EC stores).
  3. When user (A) blocks user (B), then B should be forced to
     unfollow A (the unfollow operation needs to be performed in the
     same way as above). Furthermore, to prevent B from re-following
     A, B needs to be added to A's `Blocks` list, and A needs to be
     added to B's `IsBlockedBy` list, both in the user table itself.
     All changes must commit atomically.
3. Rubis (Auction site):
  1. When a user (A) bids for an item (I), then following updates need
     to happen atomically:
     * The bid information needs to be added to the Bids table against
       a new bidId.
     * bidId needs to be added against I's itemId in ItemBids
       materialized view.
     * bidId needs to be added against A's userId in UserBids
       materialized view.
     * I's maxBid needs to be updated against I's itemId in the Item
       table.<br />
     The intermediate states may violate (a) app-specific integrity
     constraints (e.g: bid appears as top bid on the item page, but
     doesn't appear in the list of bids by the bidder), and (b)
     referential integrity (happens if data store can reorder
     operations, like in the case of EC stores).
  2. When a user cancels his bid, all the above insertions need to be
     deleted atomically. Intermediate states may violate referential
     integrity (under reordering of operations).
  3. When a user (A) offers an item (I) for auction, then I needs to
     be added to the Items table, and its itemId against A's userId in
     the UserItems table/materialized view, simultaneously.
  4. When the auction concludes, the above insertions need to be
     deleted atomically. Intermediate states may violate referential
     integrity (under reordering of operations).

<!--4. Spree (eCommerce application):
  1. When a user cancels an order (O), the cancellation information
     needs to be added against O's orderId in the order table
     atomically.
  2. When a user approves an order, approval information needs to be
     added as above.-->

### To ensure consistent reads ###

Atomicity only guarantees that a transaction's effects, if visible,
are visible in their entirety. It does not prevent effects from
becoming visible to only a subset of operations in a different
transaction. Therefore, in many cases, atomicity of a _write_
transaction itself is not sufficient to ensure that all reads witness
consistent version of data; we need certain _isolation_ gurantees on
reads. Applications use transactions to achieve isolation.  Usecases:

1. BankAccount:
  1. When a user (A) saves money (an atomic transfer from checking to
     savings account), and immediately checks the total balance in her
     accounts by issuing two `getBalance` operations, one on each of
     her accounts, she might see an inconsistent balance. This can
     happen if first `getBalance` witnesses the effects of `save`
     transaction, but second does not, or vice versa. To prevent this
     from happening, both `getBalance` operations should be wrapped
     inside a transactions, which needs to be executed in isolation
     with respect to a consisten snapshot of the database.
2. Microblog:
  1. A read operation on user A's _followers_ list might tell us that
     user B follows A, but a read of user B's _following_ list might
     return an inconsistent result. This happens if first read
     witnessed the `followUser` transaction whereas second read did
     not. This situation can be prevented by wrapping both reads in a
     transaction and insisting that this transaction be executed in
     isolation with respect to a consistent version of the database.
  2. When retrieving a user(A)'s profile using username, we perform two
     reads - one to fetch user's uuid from his username, and other to
     fetch the profile details indexed by uuid. When the user A tries
     to view her profile immediately after registering, the first read
     may succeed but second read may fail due to the absence of
     relevant record. This happens if the first read witnesses the
     effects of `addUser` transactions, whereas the second read does
     not. This situation can also be avoided by wrapping both reads in
     a transaction and running it under an appropriate isolation.
3. Rubis:
  1. When displaying the list of all bids on an item, we might
     encounter an instance of referential integrity violation,
     although none actually exists in the data. This can happen if a
     read operation on ItemBids table reads latest version of the
     table, whereas the subsequent read on the Bids table reads an
     earlier version, which may not contain certain bids. Fix for this
     case is same as above.

### To perform consistent (integrity-respecting) updates ###

Making atomic updates to the data in complete isolation can still
leave the data in an invalid state. This happens when multiple such
atomic updates succeed in complete isolation, but the merging
resultant states results in an inconsistent state. Applications use
serializable transactions to preempt the possibility of a concurrent
conflicting update. Usecases:

1. BankAccount
  1. A `transfer` transaction from account A to account B has to be
     serializable with respect to all other `transfer` transactions
     from account A to gaurantee application invariant of non-zero
     balance.
2. Microblog:
  1. When deactivating the account of user (A), the userId has to be
     removed from the _following_ list of all her followers, and
     subsequently from the user table. All operations should appear to
     have happened simultaneously, so they have to be wrapped in a
     transaction. Furthermore, to prevent violation of referential
     integrity, the transaction has to be serializable with respect to
     all `addFollower` transactions adding followers to A.
3. Rubis:
  1. `concludeAuction` and `cancelBid` transactions both can
     independently succeed possibly resulting in a state, where a bid
     is simultaneously a winning bid and a canceled bid. To avoid this
     inconsistency, `cancelBid` transaction needs to be serializable
     with `concludeAuction` transaction.

#### Notes ###

* [Circular referencing](http://stackoverflow.com/questions/1006917/are-circular-references-acceptable-in-database).
* Let a transaction `T` contain an SC operation. If a transaction `T'`
  requests RR isolation w.r.t `T`, then `T` and `T'` are automatically
  serializable.

[quelea]: http://gowthamk.github.io/Quelea/
[hat]: http://www.bailis.org/blog/hat-not-cap-introducing-highly-available-transactions/
[BankAccount]: https://github.com/gowthamk/Quelea/tree/master/tests/BankAccount
[Microblog]: https://github.com/gowthamk/Quelea/tree/master/tests/Microblog
[Twissandra]: https://github.com/twissandra/twissandra
[Rubis]: https://github.com/gowthamk/Quelea/tree/master/tests/Rubis
