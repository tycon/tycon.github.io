---
layout: post
title:  "SAT solving puzzles"
permalink: cheryl-birthday.html
---

Few months ago, [Cheryl birthday puzzle](http://goo.gl/siAHSi) has has
been an internet phenomenon. If you found the puzzle tricky to solve,
we are in the same boat. However, if you observe, the puzzle only
requires us to apply simple logic; not number theory or complex
arithmetic, just simple logic. What, then, makes the puzzle tricky? 

I attribute its trickiness to the chain of reasoning involved -
repeated application of simple logic to the existing knowledge to make
new deductions until we arrive at the solution. Since the reasoning is
quite involved, it would be great if we can enlist the services of a
computer to help us in the process.  But, how can a computer assist us
in making deductions? The answer lies in the well-known SAT problem.

Knights and Knaves Puzzle
-----------------------------------

Consider the following simple instance of the famous [Knights and
Knaves](http://en.wikipedia.org/wiki/Knights_and_Knaves) class of
puzzles:

    There is an island in which certain inhabitants, called knights
    always tell the truth, and others, called knaves always lie. It is
    assumed that every inhabitant of this island is either a knight or 
    a knave. 

    Suppose A says, “Either I am a knave or B is a knight.” 

    What are A and B?

The puzzle is easy to solve mentally. Nonetheless, if you have a 2-SAT
solver handy, you can also let solver do the work. Here is how:

Let `AisKnight` and `BisKnight` be boolean variables, denoting the
propositions “A is a Knight”, and “B is a Knight”, respectively. Since
an inhabitant can either be Knight or Knave but not both, boolean
formulas `¬ AisKnight` and `¬ BisKnight` denote the propositions that
“A is a Knave”, and “B is a Knave”, respectively. 

Now, consider the statement made by A: “Either I am a knave or B is a
knight”. Symbolically, it is equivalent to: `(¬ AisKnight) ∨
BisKnight`. Since Knights always speak truth, and Knaves always lie,
the statement is true if A is a Knight, and false if A is a Knave. In
other words, the statement holds if and only if A is a Knight.
Symbolically, it means: 

    AisKnight ⇔ (¬ AisKnight) ∨ BisKnight

Observe that the above boolean formula *completely* describes the
constraints imposed by the puzzle, and does so quite succinctly. If
the above formula is satisfiable, then the constraints imposed by the
puzzle are also satisfiable, which means that puzzle has a solution.
Furthermore, the satisfying assignment to literals in the formula
(i.e., their truth values) give us the solution to the puzzle. To get
those satisfying assignments is what the 2-SAT solver is for. If we
feed the above formula to a 2-SAT solver, we get `AisKnight = true`and
`BisKnight = true` as satisfying assignments, telling us that A and B
are both knights.

Note that satisfying assignment only tells us that “if A is knight,
then the puzzle is solved”. Maybe the puzzle is also solved if A is a
knave. How do we check for this possibility? Again, using the solver.
We explicitly encode the constraint that A is Knave, and ask if our
constraints are satisfiable. The boolean formula is shown below:

    (AisKnight ⇔ (¬ AisKnight) ∨ BisKnight) ∧ (¬ AisKnight)

A 2-SAT solver cannot find any satisfying assignment to the above
formula, indicating that our constraints are unsatisfiable. Hence, A
can never be a Knave.

Now, lets take a step back and summarize what we have done. We were
given a puzzle that is not difficult, but not obvious either. Instead
of doing the reasoning ourselves, we simply described the puzzle as a
boolean formula, and let a SAT solver do the reasoning for us. In
other words, we have outsourced the reasoning to a solver.This
facility to outsource some or all of the reasoning to a solver can be
quite handy when we are solving logical puzzles that require more
complex reasoning, like Cheryl’s birthday puzzle.

<!--more-->

From SAT solvers to SMT solvers
--------------------------------

Like the Knights and Knaves puzzle, most logical thinking puzzles can
be encoded as logical formulas, whose satisfiability determines the
solution of the puzzle. However, quite often puzzles are complex
enough that encoding them as boolean formulas in propositional logic
is cumbersome and impractical. This is akin to having to write every
program in assembly language. Often, we encounter situations where a
puzzle can be expressed as simple constraints in more complex
_theories_, like arithmetic, but translating the constraints into
propositional logic might seem impossible.  An example is the [8-Queens
puzzle](http://en.wikipedia.org/wiki/Eight_queens_puzzle), where
constraints can be straightforwardly expressed using equalities and
inequalities in [linear
arithmetic](http://math.stackexchange.com/questions/435326/linear-arithmetic-why-calling-it-linear),
but doing the same using only boolean variables is quite complicated.

It turns out that are some complex theories, including linear
arithmetic, in which constraints expressed can _always_ be translated
as constraints into propositional logic. More precisely, there exist
algorithms that can translate constraints expressed in these theories
into propositional logic without ever failing! This means that we can
describe puzzles as constraints in high-level theories like
arithmetic, which is relatively easy, then make use of these
algorithms to translate such constraints into boolean constraints, and
finally use a SAT solver to find satisfying assignments. Such
satisfying assignments can then be mapped back into original theory
(possibly arithmetic) to yield the solution to the puzzle. Wouldn’t it
be great if there is a tool that can do all of this? 

Fortunately, such tools already exist; they are called SMT solvers.
SMT is short for Satisfiability Modulo Theories, which informally
means that it is a SAT solver extended with theories. Besides linear
arithmetic, SMT solvers support various other theories, like BitVector
arithmetic, sets, multi-sets, arrays, and to some extent
quantification. There are many SMT solvers that are open source and
freely available, but one that has proved its mettle in various
industrial and research projects is Microsoft’s Z3 SMT solver [4]. 

Z3 has an easily-readable [tutorial
page](http://rise4fun.com/z3/tutorial) that demonstrates how to
use the tool to solve constraints in various theories. They even have
a very cool [web interface](http://rise4fun.com/z3) to make it easy
for us to play around.  SMT solvers, including Z3, have a standardized
input language called [SMT-LIB](http://www.smt-lib.org/) to describe
constraints in any theory they support. As a simple example, here is
the translation of boolean formula describing the Knights and Knaves
puzzle in SMT-LIB language:

    (declare-const AisKnight Bool)
    (declare-const BisKnight Bool)
    (assert (= AisKnight (or (not AisKnight) BisKnight)))
    (check-sat)
    (get-model)

The explanations for keywords like `declare-const` and `assert` are
found on the [tutorial page](http://rise4fun.com/z3/tutorial). The
command `check-sat` asks Z3 to check if the constraints stated so far
are satisfiable. It returns/prints either `sat` or `unsat`. The next
command `get-model` asks Z3 to return/print the model if the formula
is satisfiable. A
model is simply a collection of satisfying assignments to unknowns in
the variables of the formula. For the above formula, any model should
contain `true` as the satisfying assignment to both the variables
`AisKnight` and `BisKnight` denoting that A and B both are knights. I
have also made a [permalink](http://rise4fun.com/Z3/KM6s) to Z3’s
web-interface containing the above code. If you visit the page and
click on the play button, you will see the model that Z3 constructed
for the formula. It should be similar to the following:

    (model 
      (define-fun AisKnight () Bool
        true)
      (define-fun BisKnight () Bool
        true)
    )

Model describes `AisKnight` and `BisKnight` as nullary functions
instead of variables, but this is a mere technicality that you should
ignore. 

When I first encoded the Knights and Knaves puzzle in Z3, my encoding
is a little longer (and more closer to puzzle’s English description)
than the one we have seen. Here is the SMT-LIB code:

    (declare-const AisKnight Bool)
    (declare-const AisKnave Bool)
    (declare-const BisKnight Bool)
    (declare-const BisKnave Bool)
    ;; A is either a Knight or a knave, but not both.
    (assert (xor AisKnight AisKnave))
    ;; Likewise, B.
    (assert (xor BisKnight BisKnave))
    ;; A's statement
    (declare-const AStatement Bool)
    (assert (= AStatement (or AisKnave BisKnight)))
    ;; If A is a Knight, then A's statement is true.
    (assert (=> AisKnight AStatement))
    ;; If A is a Knave, then A's statement is a total lie
    (assert (=> AisKnave (not AStatement)))
    (check-sat)
    (get-model)

You can also see it’s [permanent page](http://rise4fun.com/Z3/8u4) on
Z3’s web interface.

8-Queens
---------

I confess that Knights and Knaves is a pretty simple puzzle to warrant
the fuss we have made.  A more worthy candidate is 8-Queens puzzle.
Fortunately, Nikolaj Bjørner, a co-creator of Z3, has written a
succinct
[tutorial](http://research.microsoft.com/en-us/events/z3dtu/lab-sat.pdf)
describing how to solve the more general n-Queens problem making use
of BitVector theory in Z3. I encourage you to take a look. 

Cheryl Birthday Puzzle
----------------------

We shall now see how formal logic and Z3 to can be used to simplify
the reasoning required to solve Cheryl’s birthday puzzle. For the
impatient, [here](http://rise4fun.com/Z3/sA4R) is the solution.

First, let us recall the problem statement. Here is the text:

    Albert and Bernard just became friends with Cheryl, and they want to
    know when her birthday is.  
    Cheryl gave them a list of 10 possible dates:
          May 15       May 16     May 19
          June 17     June 18
          July 14     July 16
        August 14   August 15   August 17
    Cheryl then tells Albert and Bernard separately the month and the day
    of the birthday respectively.
    Albert: I don't know when Cheryl's birthday is, but I know that
    Bernard does not know too.
    Bernard: At first I don't know when Cheryl's birthday is, but I know
    now.
    Albert: Then I also know when Cheryl's birthday is.

    So when is Cheryl's birthday?

First of all, we need to model dates as the date type is not available
in Z3.  Since Cheryl treats month and day of her birthday
independently, we need to model them independently, and then model
date as a combination of month and day. We don’t have to consider all
the months, or all the days; the ones in the possible dates are
enough. We model months as BitVectors of length 2 (i.e., two bits),
and days as BitVectors of length 3 respectively. There are two other
attractive alternatives to BitVectors: integers, and uninterpreted
sorts. Unlike BitVectors, which are finite, an integer in Z3 is an
unbounded datatype, hence makes reasoning unnecessarily difficult.
Declaring an uninterpreted sort (call it `T`) in Z3 introduces a new
type `T`, whose values have no attached interpretation, unlike, say,
integers. We could have introduced `Month` as an uninterpreted sort,
and then declared `May` etc as values of sort `Month`. But this is not
enough; we must also explicitly assert that (a). No other value
besides declared values (i.e. `May`, `June`, `July`, and `August`)
have the sort `Month`, and (b). None of the declared values is equal
to the other. Sans these constraints, Z3 is free to add  more values
to the sort `Month`, and can even assume that `May` and `June` are the
same.

Using BitVectors of length 2, here is how we model months:

    ;; define-sort is like typedef.
    (define-sort M () (_ BitVec 2))
    (declare-const may M)
    (assert (= may #b00))
    (declare-const june M)
    (assert (= june #b01))
    (declare-const july M)
    (assert (= july #b10))
    (declare-const aug M)
    (assert (= aug #b11))

Similarly, days using BitVectors of length 3:

    ;; Days
    (define-sort D () (_ BitVec 3))
    (declare-const _14 D)
    (assert (= _14 #b000))
    (declare-const _15 D)
    (assert (= _15 #b001))
    (declare-const _16 D)
    (assert (= _16 #b010))
    (declare-const _17 D)
    (assert (= _17 #b011))
    (declare-const _18 D)
    (assert (= _18 #b100))
    (declare-const _19 D)
    (assert (= _19 #b101))

You might have noticed that BitVectors of length 3 allow 8 values,
whereas we have only 6 possible days. BitVectors `#b110` and `#b111`
do not correspond to valid days. Furthermore, not all combinations of
months and days are candidate dates for Cheryl’s birthday; only 10 of
them are valid. We therefore define an `isDate` predicate (i.e., a
function whose co-domain is Bool) on months and days to define which
dates are valid dates:

    ;; What is a date?
    (define-fun isDate ((m M)(d D)) Bool
      (or (and (= m may) (or (= d _15) (= d _16) (= d _19)))
          (and (= m june) (or (= d _17) (= d _18)))
          (and (= m july) (or (= d _14) (= d _16)))
          (and (= m aug) (or (= d _14) (= d _15) (= d _17)))))

Now that we have modeled months, days and dates, we have the
scaffolding ready to state the constraints of the puzzle. Firstly,
since we are interested in knowing actual month and day of Cheryl’s
birthday, we declare them as two unknowns - `bdaym` and `bdayd` of
month and day type respectively:

    (declare-const bdaym M)  
    (declare-const bdayd D)

The idea is that, once we have described all the constraints of the
puzzle, satisfying assignments to `bdaym` and `bdayd` are the
BitVector representations of month and day of Chery’s actual birthday.

Now, lets consider the two propositions made by Albert in his first
statement: 

1. Prop1: “I don't know when Cheryl's birthday is”.
2. Prop2: “I know that Bernard does not know too”.

Let us represent the above two propositions as two boolean variables,
namely `aDoesntKnow` and `aKnowsBDoesnt`, respectively. Considering
that Albert does know `bdaym` (Cheryl told him), the only way he
cannot know the birthday date is if `bdaym` is a month with many days.
Let us say there is a predicate called `hasManyDays(m)` that precisely
expresses the fact that a given month (`m`) has many days. Then,
`aDoesntKnow` is true if and only if `hasManyDays(bdaym)` is true:

    (assert (= aDoesntKnow (hasManyDays bdaym)))

Here is the definition of `hasManyDays(m)` predicate:

    (define-fun hasManyDays ((m M)) Bool
      (exists ((d1 D) (d2 D))
        (and (not (= d1 d2)) (isDate m d1) (isDate m d2))))

The definition simply says that a given month `m` hasManyDays if and
only if there exist two days `d1` and `d2` such that `d1 ≠ d2`, and
`isDate m d1` is true and `isDate m d2` is also true. In other words,
there exist two distinct days in the month `m`.

Now, let us consider Prop2. Albert is aware that Bernard knows the day
of the birtday (`bdayd`). Although Albert himself is not aware of
`bdayd`, he knows that it must be a day occuring in `bdaym`. Now, if
there exists a day (call it `d`) in `bdaym` that occurs uniquely in
`bdaym` (i.e., `∀m. isDate (m,d) ⇒ m = bdaym`), and `bdayd` happens to
be that day, then Bernard can deduce the `bdaym` from `bdayd`, and can
consequently know Cheryl's birthyday. However, Albert is sure that
this is not possible and Bernard does not know the birthday. This
means that no day occurs uniquely in `bdaym`. 

Let us say that there is a predicate `hasNoUniqueDay(m)` that asserts
that the given month (`m`) has no days that uniquely identify `m`.
Then, Albert can be sure that Bernard does not know the birthday if
and only if `hasNoUniqueDay(bdaym)` is true:

    (assert (= aKnowsBDoesnt (hasNoUniqueDay bdaym)))

Here is the definition of `hasNoUniqueDay(m)` predicate:

    (define-fun hasNoUniqueDay ((m M)) Bool
      (forall ((d D)) (=> (isDate m d)
        (exists ((_m M)) (and (not (= _m m)) (isDate _m d))))))

The predicate simply states that the given month `m` hasNoUniqueDay
if and only if all days `d` in month `m` also occur in alteast one
another month `_m`. 

We have now captured both the propositions made by Albert in his first
statement as formulas. All that remains is to assert that the formulas
are true:

    (assert (and aDoesntKnow aKnowsBDoesnt))

Before we consider Bernard's statement, let us take a step back and
make one crucial observation. We have modeled whatever Albert has
said, and it led to two constraints on `bdaym`: `hasManyDays(bdaym)`
is true and `hasNoUniqueDay(bdaym)` is true. Therefore, due to the
statements made by Albert, we know have information about `bdaym`,
namely that it has many days and that it has no day that uniquely
identifies it. Since Bernard listened to Albert, he would also have
deduced the same. 

Now, lets consider propositions made by Bernard in his only statement: 

1. Prop3: At first I don't know when Cheryl's birthday is.
2. Prop4: I now know when Chery's birthday is.

Prop3 is simply a reaffirmation of Albert's Prop2. Prop4, however, is
very important. It effectively says that whatever Albert has said
about `bdaym` coupled with the knowledge of `bdayd` is enough to
deduce the birthday. In other words, any month (`m`) containing
`bdayd` and satisfying Albert's constraints (viz., `hasManyDays(m)`
and `hasNoUniqueDay(m)`) must be unique, and it has to be `bdaym`.
More precisely:

    (assert (forall ((m M)) 
              (=> (and (hasManyDays m) (hasNoUniqueDay m)
                       (isDate m bdayd)) 
                  (= m bdaym))))

For convenience, we factor the above constraint into a predicate
called `determinesBdayM` on any day `d`, and use it to constraint
`bdayd`:

    (define-fun determinesBdayM ((d D)) Bool
      (forall ((m M)) 
              (=> (and (hasManyDays m) (hasNoUniqueDay m)
                       (isDate m d)) 
                  (= m bdaym))))
    (assert (determinesBdayM bdayd))

Before we consider Albert's final statement, we make another important
observation. We have captured whatever Bernard has said about the
`bdayd`, and it gave us one constraint on `bdayd`, namely that
`determinesBdayM(bdayd)` is true. Albert too would have made this
deduction.

In his final statement, Albert declares that he too knows the birthday
now.  Since Albert already knows the birthday month (`bdaym`), this
means that any day (`d`) in `bdaym` that satisfies Bernard's
constraints must be unique, and it must be `bdayd`. More precisely:

    (assert (forall ((d D)) 
      (=> (and (isDate bdaym d) (determinesBdayM d)) 
      (= d bdayd))))

Thats it. We have no more constraints to capture. Using Z3, we now
check if the given constraints are satisfiable, and if they are, then
ask it to return a satisfying assignment. To do this, go to this
[page](http://rise4fun.com/Z3/JQ2R) containing all the SMT-LIB
statements we have made so far, and then click on the play button. Z3
should print sat, followed by a long model describing satisfying
assignment to every variable in our long formula. Since we are only
interested in knowing `bdaym` and `bdayd`, we only pay attention to
relevant parts in the model:
    
    (define-fun bdaym () (_ BitVec 2)
       #b10)
    (define-fun bdayd () (_ BitVec 3)
        #b010)

Among months, `#b10` stands for July, and among days `#b010` stands
for 16th. Therefore, Z3's solution to Cheryl's birthday problem is
July 16th, which happens to be the actual answer!

Final Remarks
-------------

This blog should have hopefully demonstrated the utility of including
a SAT/SMT solver in the workflow when the problem demands us to make a
sequence of nontrivial logical deductions. If you are new to formal
reasoning tools, like SMT solvers, you may have many questions
including:

1. Does the ability to do away with some amount of manual reasoning
   worth the substantial effort required to describe everything in formal logic?, and
2. Why can't we simply write some code to solve the puzzle instead of
   encoding it rigorously in logic? 

The answer to both the questions is the same: the benefits of formally
modeling a problem in an automatic reasoning tool goes beyond its end
product, i.e., the solution to the problem. Formal modeling is also a
medium that (a). enables us to think precisely about the problem, and
(b). lets us understand _what_ should be the solution to the problem,
without necessarily requiring us to think about _how_ to construct it
(unlike writing code).  In other words, formal modeling drastically
improves our thinking and makes us better problem solvers. To [quote](http://research.microsoft.com/en-us/um/people/lamport/tla/book.html)
Leslie Lamport: "Writing is nature's way of letting you know how
sloppy your thinking is, mathematics is nature's way of letting you
know how sloppy your writing is, and Formal mathematics is nature's
way of letting you know how sloppy your mathematics is."

In this blog, I have used puzzle solving as a vehicle for
demonstrating the ability of SMT solvers in assisting with our
thought process. However, the utility of solvers extends well beyond
puzzle solving. Today, they power some of the state-of-the-art program
analysis and verification tools that perform heavyweight reasoning on
computer programs to automatically find bugs, and sometimes to even
prove that a certain class of bugs (e.g. null pointer dereferences, or
`ArrayOutOfBounds`) do not exist in the program. If you are interested
in finding out some more cool tricks possible via SMT solvers, I
encourage you to take a look at Torlak et al's [Onward'13](http://homes.cs.washington.edu/~emina/pubs/rosette.onward13.pdf) and [PLDI'14](http://www.cs.berkeley.edu/~bodik/Files/2014/rosette-pldi2014.pdf)
papers describing their Rosette solver-aided language. 


<!-- References:

1. http://www.wolframalpha.com/input/?i=a+%3C%3D%3E+%28~a+%7C%7C+c%29+
2. http://en.wikipedia.org/wiki/Eight_queens_puzzle
3. http://math.stackexchange.com/questions/435326/linear-arithmetic-why-calling-it-linear
4. http://rise4fun.com/z3/tutorial
5. http://rise4fun.com/z3
6. http://rise4fun.com/Z3/KM6s 
7. http://rise4fun.com/Z3/8u4
8. http://research.microsoft.com/en-us/events/z3dtu/lab-sat.pdf
9. http://research.microsoft.com/en-us/um/people/lamport/tla/book.html
-->
