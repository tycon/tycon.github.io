---
layout: post
title:  "Understanding Transactions in Rails"
permalink: understanding-rails-transactions.html
---

In my [previous post][fcpost] I have noted that Rails encourages
application developers to rely on feral mechanisms, such as
validations and associations, to ensure application integrity. In this
post, I first explore various feral mechanisms in Rails, and how they
are being used by some sample applications. Next, I will throw some
light on how Rails actually enforces these feral mechanisms.

### ORM and Active Record ###

Quoting from Ruby on Rails [guide][arb]:

__Object Relational Mapping__:
Object-Relational Mapping, commonly referred to as its abbreviation
ORM, is a technique that connects the rich objects of an application
to tables in a relational database management system. Using ORM, the
properties and relationships of the objects in an application can be
easily stored and retrieved from a database without writing SQL
statements directly and with less overall database access code.

__Active Record as an ORM Framework__:
`ActiveRecord` is Rails's implementation of ORM. Active Record gives
us several mechanisms, the most important being the ability to:

* Represent models and their data.
* Represent associations between these models.
* Represent inheritance hierarchies through related models.
* Validate models before they get persisted to the database.
* Perform database operations in an object-oriented fashion.

__Active Record Models__:
A class that extends `ActiveRecord` is an Active Record model, or
simply a model. Each model has a corresponding table in the underlying
database. For instance, defining the `Product` model:

    class Product < ActiveRecord::Base 
    end

will create a table with the following schema:

    CREATE TABLE products (
      id int(11) NOT NULL auto_increment,
      name varchar(255),
      PRIMARY KEY  (id)
    );

__CRUD__:
To write a record to the the database, we first create an Active
Record object (note: `arg:` denotes an argument named _arg_. Think of
Ruby methods as functions accepting named variants):

    product = Product.create(name: "Milk")

or

    product = Product.new do |p|
      p.name = "Milk"
    end

To save, `ActiveRecord` offers save method:

    product.save

Reading can be done via multiple querying methods. Example:

    all_prods = Product.all
    milk = Product.find_by(name: "Milk").order(id: :asc)

Active record querying [webpage][arq] has more details.

Updatation can be done via read-modify-save sequence:

    milks = Product.find_by(name: "Milk")
    milks.each do |m| 
      m.name = "Whole Milk"
      m.save
    end

Note: Active Record uses SQL INSERT for new record saves, and SQL
UPDATE for updatations. It uses `new_record?` flag to keep track of new
Active Record objects that are not yet saved into the database
(source: Active Record Callbacks [guide][arc]).

Deletion is done using `destroy`:

    milks = Product.find_by(name: "Milk")
    milks.each do |m| 
      m.destroy
    end

The corresponding records will be deleted from the database.

### Associations ###

Associations are useful to keep track of semantic associations between
various models. For instance, using a `belongs_to` association, the
developer can let Rails know that every order in an eCommerce
application belongs to utmost one customer (Note: the `:name` syntax
denotes a symbol called _name_. Meta-level functions accept symbols
and generate new code, which would then be spliced into original code
(somewhat like MetaOCaml and TemplateHaskell). Ruby, being a dynamic
language, does not treat meta-level functions specially.).

    class Order < ActiveRecord::Base
      belongs_to :customer
    end 

The result is that the `order` table will now have a column named
`customer_id` that is expected to refer to `id` of the `customer`
table. Order objects will also have a field named `customer`
referring to the Customer object to which the order belongs to
(note: the field can be `nil`). When an order object is saved, the
`id` of its customer object will be saved to the `customer_id` field
of the corresponding record in the database.

The other end of `belongs_to` association is usually a `has_many`
association or `has_one` association. Using a `has_many` association,
the developer can specify that a customer can have one or many orders:

    class Customer < ActiveRecord::Base
      has_many :orders
    end
     
Other than adding a field named `orders` to a customer object,
specifying the `has_many` association will have no tangible effect; 
there is no change in Rails's interaction with `order` and `customer`
tables. However, we can qualify the `has_many` association with an
optional `dependent` argument set to `:destroy` that asks Rails to
destroy all orders placed by a customer, when the customer is deleted.

    class Customer < ActiveRecord::Base
      has_many :orders, dependent: :destroy
    end

This behaviour corresponds to `ON DELETE CASCADE` behaviour offered by
SQL for foreign key dependents.

With `belongs_to` association from `Order` to `Customer`, and
`has_many` association from `Customer` to `Order`, with a `dependent:
:delete` qualification, we have something close to, but not exactly, a
foreign key constraint from the order table to the customer table. To
effectively enforce a foreign key constraint, we need a guarantee that
an order cannot exist without the corresponding customer existing in
the customer table. Currently, this invariant can be violated if, for
example, we `save` an order object referring to a customer object, whose
corresponding record was already destroyed. The effective foreign key
enforcement that prevents this scenario (theoretically, at least) can
be achieved using _Model Validations_, described in the next section.

It is also possible to specify many-to-many relationships between
models in a similar way to how such relationships are defined in
relational databases: via an intermediary model. For example, in a
microblogging application, a user can _follow_ many users, and can
have many users as _followers_. This many-to-many relationship between
users can be specified via a third model called, say, `relationships`.
Each user `has_many` _following_ `relationships` and _follower_
`relationships`. Each relationship `belongs_to` two users: user who is
being followed, and the user who is following. This scenario is
described in the picture below (source: Michael Hartl's
[book][picurl]. Released under [MIT License][MITLicense]):

![MicroblogAssns]({{ site.baseurl }}/assets/MicroblogAssns.png)

Observe that there is a transitive `has_many` relationship between
users, which can be made explicit via `through:` argument to
`has_many` association: a user `has_many followers through:
relationships`, and `has_many followed_users through: relationships`.

Besides `belongs_to`, `has_many`, and `has_one`, Rails defines few
other associations. They are described [here][ara].

### Validations ###

Quoting from Rails [guide on validations][arv]:
Validations are used to ensure that only valid data is saved into your
database. For example, it may be important to your application to
ensure that every user provides a valid email address and mailing
address. Model-level validations are the best way to ensure that only
valid data is saved into your database.  

Validations are primarily declared using `validates`
[method][validates]. For example, to ensure that user provides an
email address during during a new account creation (i.e., `email`
field is not `nil`), and to ensure that there are no existing accounts
associated with this email, we can perform `presence` and
`uniqueness` validations, respectively.

    class Account < ActiveRecord::Base
      validates :email, uniqueness: true, presence: true
    end

Rails also provides variants of `validates` specialized for common
validations:

    class Account < ActiveRecord::Base
      validates_presence_of :email
      validates_uniqueness_of :email 
    end

`validates_uniqueness_of` is clearly useful to ensure primary key
property.  Besides being useful to preempt `nil` values,
`validates_presence_of` is also useful to enforce foreign key
constraints, when used in conjunction with associations. For instance,
in the eCommerce example, the foreign key constraint from `Order` to
`Customer` can be enforced by validating the presence of `customer`
field.

    class Order < ActiveRecord::Base
      belongs_to :customer
      validates_presence_of :customer
    end 
    class Customer < ActiveRecord::Base
      has_many :orders, dependent: :destroy
    end

Another useful validation is `validates_associated`. You should use
this helper when your model has associations with other models and
they also need to be validated.  When you try to save your object,
`valid?` will be called upon each one of the associated objects. For
instance, when the `Customer` class validates associated orders:

    class Customer < ActiveRecord::Base
      has_many :orders, dependent: :destroy
      validates_associated :orders
    end

All the orders associated with the customer are validated when the
customer object is being `save`'d (in this case, this entails a
validation for the presence of the customer object owning orders,
which is trivially true).

`validates_associated` works with all of the association types.
Although it is by default turned off for most associations, it is by
default on for `has_many` association. So, for the above example we
needn't explicitly specify `validates_associated`.

Note: Ruby has a concept of _virtual attributes_, which, in the
context of `ActiveRecord` are attributes that do not get recorded in
the database. Validations can also be defined over virtual attributes.

### Custom validations ###

Validations, such as `validates_presence_of`, are built into Rails.
Sometimes, built-in validations are not sufficient. Rails allows
developers to define custom validations for this purpose. Custom
validations can be defined as methods, which are used once locally, or
they can be defined by implementing Rails's `ActiveModel::Validator`
interface. Examples of custom validators include Spree's
`AvailabilityValidator`, which checks whether an eCommerce inventory
as sufficient stock available to fulfill an order. More on custom
validations [here][arc-custom-validations].

### When are validations enforced? ###

When an Active Record object is being persisted to the database
(`save`), although this is not entirely accurate:

> Validations are typically run before these commands (INSERT/UPDATE)
> are sent to the database. If any validations fail, the object will
> be marked as invalid and Active Record will not perform the INSERT
> or UPDATE operation. This helps to avoid storing an invalid object
> in the database. You can choose to have specific validations run
> when an object is created, saved, or updated.

> There are many ways to change the state of an object in the database.
> Some methods will trigger validations, but some will not. This means
> that it's possible to save an object in the database in an invalid
> state if you aren't careful. - [ActiveRecord validations callbacks guide][arc]

Validations and any callbacks registered on the state changes of the
model object are queued for execution. This queue will include all
your model’s validations, the registered callbacks, and the database
operation to be executed. The whole callback chain is __wrapped in a
transaction__. If any validation/callback method returns false or raises
an exception the execution chain gets halted and a ROLLBACK is issued
([source][arc-halting-execution]).

## Sample Applications ###

We will now examine some sample applications to understand how
validations and associations are being used. 

#### Microblog ###

First is based on a small [microblogging
application](https://github.com/railstutorial/sample_app_rails_4) from
the Ruby on Rails [tutorial](https://www.railstutorial.org) by Michael
Hartl. 

The app defines 3 models - `micropost`, `user`, and `relationship`
with following associations and validations:

* Micropost `belongs_to` a user, and validates the presence.
* A user has an email address; validates its presence and uniqueness.
* A user `has_many` _follower_ relationships, and `through:` those
  relationships, `has_many` followers. Follower relationships need to
  be destroyed if this user is deleted. 
* A user `has_many` _following_ relationships, and `through:` those
  relationships, `has_many` followed users. _Following_ relationships
  need to be destroyed if this user is deleted.
* A relationship jointly `belongs_to` a follower user and a followed
  user, and validates their presence.

Following are some interesting operations that the app defines:

__Adding a User__: Adds a user after validating that the email is
present and unique.

    addUser(u) = transaction do
      assert(u.email != nil);
      dups := SQL "SELECT * FROM users WHERE email = `u.email` LIMIT 1"
      assert (dups == []);
      SQL "INSERT INTO users VALUES (`freshId()`,`u.email`,`u.name`)";
      followUser(thisUser, thisUser); /* One must follow oneself */

__Follow a User__: Makes the current user follow another user.

    followUser(thisUser,thatUser) = transaction do
      usr1 := SQL "SELECT * FROM users WHERE id = `thisUser.id` LIMIT 1";
      assert (usr1 != []);
      usr2 := SQL "SELECT * FROM users WHERE id = `thatUser.id` LIMIT 1";
      assert (usr2 != []);
      SQL "INSERT INTO Relationships VALUES (`thisUser.id`,`thatUser.id`)";

__Unfollow a User__: Makes the current user unfollow other user.

    unfollowUser(thisUser,thatUser) = transaction do
      SQL "DELETE FROM Relationships WHERE follower_id = `thisUser.id`
                                     AND followed_id = `thisUser.id`";

__getFollowers__: Returns the list of users following the current
user.

    /* Implementation 1 : from the original sample app */
    getFollowers(thisUser) = 
      SQL "SELECT * FROM users INNER JOIN relationships ON
          users.id = relationships.follower_id WHERE
          relationships.followed_id = `thisUser.id`"

    /* Implementation 2: If the data store does not support joins
                (e.g: Cassandra) */
    getFollowers(thisUser) = transaction do
      rels := SQL "SELECT * FROM relationships WHERE 
                      followed_id = `thisUser.id`";
      followers := [];
      rels.each |rel| do
        /* The following pattern-match must always pass because:
            1. Relationship model validates presence of follower
               before persisting.
            2. When a user is deleted, all the dependent
               relationships are deleted as well.
            3. User model validates uniqueness when persisiting. */
        [follower] = SQL "SELECT * FROM users WHERE 
                        id = `rel.follower_id`";
        followers := follower::followers;
      return followers;

__getFollowedUsers__: Returns the list of users that the current user
is following. Implementation similar to `getFollowers` described
above.

__postBlog__: Posts a microblog on behalf of the current user.
Validates the presence of current user record before persisiting the
microblog.

    postBlog(thisUser,blog) = transaction do
      usr = SQL "SELECT * FROM users WHERE id = `thisUser.id` LIMIT 1"; 
      assert(usr != []);
      SQL "INSERT INTO microposts (content, user_id) 
           VALUES (`blog.content`, `thisUser.id`)";

__getTimeLine__: Get a list of microposts by a user (the call is: 
`Micropost.includes(:user).from_users_followed_by(user)`).

    getTimeLine(user) =
      posts := SQL "SELECT * FROM microposts WHERE 
        user_id = `user.id`";
      posts.each |post| do
        post.user := (SQL "SELECT * FROM users WHERE id = post.user_id LIMIT 1").first;
      return posts;

<!-- To display the timeline, the application might do the following:

    posts = getTimeLine(user);
    posts.each |post| do
      print post.user.name;
      print post.content;
-->

The SQL call to `users` table never returns an empty collection because:

* A micropost `belongs_to` a user, and checks the presence of the user
  before persisting, and
* When a user is deleted, the dependent microposts are also deleted.

Therefore, `.first` on the collection returned by SQL is always valid.

__getFeed__: Get a list of microposts by users being followed by
the current users. The implementation, and discussion for this
operation is same as that of `getTimeLine`.

__deleteUser__: Delete the current user. It has to enforce `dependent:
:destroy` on microposts and relationships.

    deleteUser(thisUser) = transaction do
      /* First, delete all microposts by this user */
      SQL "DELETE FROM microposts WHERE user_id = `thisUser.id`";
      /* Next, delete all relationships on this user */
      SQL "DELETE FROM relationships WHERE 
        follower_id = `thisUser.id` OR
        followed_id = `thisUser.id`";
      /* Finally, delete the user */
      SQL "DELETE FROM users WHERE id = `thisUser.id`";

[fcpost]: feral-concurrency-control.html
[validates]: http://apidock.com/rails/ActiveModel/Validations/ClassMethods/validates
[arv]: http://guides.rubyonrails.org/active_record_validations.html
[arb]: http://guides.rubyonrails.org/active_record_basics.html
[arq]: http://guides.rubyonrails.org/active_record_querying.html
[ara]: http://guides.rubyonrails.org/association_basics.html
[arc]: http://guides.rubyonrails.org/v2.3.11/activerecord_validations_callbacks.html#when-does-validation-happen
[arc-custom-validations]: http://guides.rubyonrails.org/v2.3.11/activerecord_validations_callbacks.html#creating-custom-validation-methods
[arc-halting-execution]: http://guides.rubyonrails.org/v2.3.11/activerecord_validations_callbacks.html#halting-execution
[picurl]: https://www.railstutorial.org/book/following_users#sec-relationship_user_associations
[MITLicense]: https://www.railstutorial.org/book/frontmatter#copyright_and_license

