---
layout: post
title:  "Notes - A Data-Driven Approach for Algebraic Loop Invariants"
permalink: data-driven-loop-inv.html
---

This post contains my notes on Rahul Sharma et al's ESOP'13 paper: A
Data-Driven Approach for Algebraic Loop Invariants.

The paper proposes a neat approach of inferring algebraic loop
invariants by observing concrete program states, and making use of
techniques from linear algebra to gain insights.


Following is an example take from the paper:

    assume (x=0 && y=0);
    writelog (x,y);
    while(nondet()) do
      y := y+1;
      x := x+y;
      writelog (x, y);

For the above example, we are interested in finding the loop invariant
for the `while` loop. Assume we already know that invariant can be
non-linear, but no complex than degree 2. Let \\(f(x,y)\\) denote a
polynomial of degree less than or equal to 2. The equation
\\(f(x,y)=0\\) is a polynomial equation or algebraic equation in
variables `x` and `y`. Since `x` and `y` are the only two variables in
scope at the head of the loop, we know that loop invariant will be of
form:

  $${\bigwedge}_{i}\;f_i(x,y)=0$$

where each \\(f_i\\) is a unique polynomial of degree utmost 2.
A polynomial of degree 2 is simply a linear combination of monomials
of degree utmost 2. In this case, we have 6 unique monomials:
\\({1,x,y,x^2,y^2,xy}\\). Therefore, each polynomial will be of the
following form:

  $$f(x,y) = w_1 + w_2x + w_3y + w_4x^2 + w_5y^2 + w_6xy$$

The invariant inference problem then is to infer the rational
constants \\(w_1-w_6\\) such that \\(f(x,y)=0\\). 

The paper proposes a data-driven approach to solve this problem.
Informally, a loop invariant over-approximates the set of all possible
program states that are possible at the loop head. For the above
example program, the program state consists of values of `x` and `y`.
We instrument the code to observe the program state (i.e., values of
`x` and `y`) at the beginning of every iteration of the loop, when the
program is executed over test inputs (user-provided or random). We
record these observations in a log file.

Next, for every observed program state, we calculate the values of all
6 monomials and record them in a matrix, where a row denotes a program
state (i.e., fixed values for `x` and `y`), and a column denotes
values of a fixed monomial in various program states. A sample
datamatrix for the above example is shown below:

  $$
    \begin{bmatrix}
       1 & 0 & 0 & 0 & 0 & 0 \\\
       1 & 1 & 1 & 1 & 1 & 1 \\
    \end{bmatrix}
  $$

Now, any valid solution for \\(w_1-w_6\\) (hence the loop invariant
problem) should explain the observed program states. Therefore,
following has to hold:

$$
  \begin{bmatrix}
     1 & 0 & 0 & 0 & 0 & 0 \\\
     1 & 1 & 1 & 1 & 1 & 1 \\\
  \end{bmatrix}
  \times
  \begin{bmatrix}
    w_1 \\\
    w_2 \\\
    w_3 \\\
    w_4 \\\
    w_5 \\\
    w_6 \\\
  \end{bmatrix}
  = 0
$$

Observe that any solution to the above equation gives us an invariant
that holds over observed program states. However, it may not hold over
_all_ possible program states. Therefore, solving above equation gives
us _candidate invariants_, which we can then verify for validity. But,
how do we solve the above equation. Here is where techniques from
linear algebra help.

Let us denote the datamatrix with \\(A\\), and the matrix of
coeffecients (\\(w_1-w_6\\)) with \\(W\\). The matrix \\(W\\) has only one
column, and is referred to as column vector or simply a vector. Set of
all possible solutions to \\(W\\) (each is a vector) is called the _null
space_ of \\(A\\). Note that _NullSpace(A)_ is a set of vectors. _Span_
of any set of vectors \\(\{x_1,..,x_n\}\\) is set of all vectors that can
be expressed as a linear combination of \\(\{x_1,...,x_n\}\\). In other
words, span of a set of vectors is the entire vector space represented
by those vectors. Observe that span of a _NullSpace(A)_ is
_NullSpace(A)_, as every linear combination of vectors in
_NullSpace(A)_ results in a vector \\(x\\), which satisfies \\(Ax=0\\).
Hence, _NullSpace(A)_ is a vector space. Basis of any vector space is
a set \\(B\\) of linearly independent vectors such that every other
vector in the space can be expressed as a linear combination of
vectors in \\(B\\). For a 3-D cartesian vector space, the set
\\(\{(3,0,0), (0,2,0), (0,0,1)\}\\) can be considered a basis. The
cardinality of the basis is the dimension of the vector space, as is
evident from the basis set of 3-D cartesian space.

For the matrix \\(A\\), Let \\(B_w\\) denote the basis of _NullSpace(A)_.
What does set \\(B_w\\) represent? Each vector in the set is a unique
solution to \\(W\\) that cannot be expressed as linear combination of
other solutions. Further, any solution to \\(W\\) can be expressed as a
linear combination of vectors in \\(B_w\\). Effectively, this means
that **by calculating basis set of _NullSpace(A), we derive _all
unique_ algebraic invariants of degree utmost 2 that hold on observed
program states**. The invariants are unique as any other invariant can
be expressed as a linear combination of polynomials denoted by the
basis set.

Once candidate solutions are generated by calculating the basis of
null space of \\(A\\), they are verified via symbolic execution and SMT
solvers. Verification failure results in a counterexample, which is
simply a valuation for `x` and `y` for which candidate invariant
fails. In such case, loop is rerun with these values of `x` and `y`
and more observations are recorded, thereby increasing the datamatrix
\\(A\\). Invariants generated by calculating the basis of null space of
larger datamatrix will now definitely account for the counterexample
generated by the solver in the previous step. This counterexample
guided iterative refinement (which they call \\({\sf
Guess-And-Check}\\)) is similar in flavour to CEGAR, but there is one
fundamental difference. Recall that CEGAR starts with a formula that
over-approximates program behaviours, and gradually refines the
formula until it is valid, or a bug is found in the program. In
contrast, \\({\sf Guess-And-Check}\\) starts with under-approximation
of program behaviours (represented by the datamatrix), and adds more
behaviours until we have sufficient representation of the all possible
program behaviours. In this sense, \\({\sf Guess-And-Check}\\) is more
similar to CEGIS. The only difference is that, while CEGIS relies on
an SMT oracle to generate positive samples, \\({\sf
Guess-And-Check}\\) relies on tests.

In practice, the number of possible monomials at the loop head could
be large. The paper uses a heuristic to discard monomials that are
unlikely to be part of the final invariant. The heuristic is that
monomials which grow at a rate much larger than the loop counter \\(i\\)
(i.e., at a rate \\(\omega(i^d)\\)) are most often red herrings.

