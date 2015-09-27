---
layout: post
title:  "Notes - McCarthy's Lisp and Reynolds's Definitional Interpreters"
---

This post is a compilation of my notes on two landmark papers:

1. The Lisp paper: McCarthy J, Recursive Functions of Symbolic
   Expressions and Their Execution by Machine, CACM'60 
2. Interpreters paper: Reynolds J C, Definitional Interpreters for
   Higher-Order Programming Languages, ACM'72


### 1.The Lisp Paper ###

This paper by John McCarthy introduces the Lisp programming language
and describes its implementation on IBM 704 machines. Lisp stands out
among the programming languages of its day (eg: Algol 60) as the first
high-level programming language that abstracts the underlying machine
completely. Instead, Lisp allows symbolic computation by letting
programmers define (recursive) functions over symbolic expressions
(called S-expressions). An S-expression is either an atomic symbol
(hence "symbolic"), or an ordered pair of S-expressions. Reserving an
atomic symbol NIL to denote an empty list, we can construct a list of
S-expressions:

    [s1,s2,s3]

using ordered pairs as:

    (s1,(s2,(s3,NIL)))

Observe that above is also an S-Expression. Hence, a list of
S-expressions is also an S-expression. Since most functions operate on
a list of symbols, programming such functions in Lisp is effectively
LISt Programming (hence, the name "Lisp").  

Lisp defines five primitive S-functions to construct & destruct lists,
and to check equality among atomic symbols: 

1. atom 
2. eq
3. car
4. cdr
5. cons

Lisp, as defined in paper, includes a class of expressions called
Meta-expressions (written M-expressions) to let us define and apply
S-functions over S-expressions. An M-expression is either

1. A function application. For eg, f[2; EMPTY] is an M-expression that
   denotes application of function f over S-expressions of atomic
   symbols 2 and EMPTY. 
2. A function definition with grammar: _fname[x0, ..., xn] = expr_, and
3. A conditional expression: [expr1a -> expr1b; ...; exprna -> exprnb ]

Using M-expressions and primitive S-functions, we can define a subst
function to substitute An S-expression (x) for an atomic symbol (y) in
another expression (z) as:

    subst[x;y;z] = [
      atom[z] -> [
        eq[z;y] -> x;
        T -> z
      ]
      T -> cons [subst[x; y; car[z]]; 
                 subst[x; y; cdr[z]]]
    ]

This example demonstrates that while M-expressions are control
structures (functions & conditional expressions), S-expressions
represent data to be manipulated by M-expressions.

The definition (semantics) of Lisp are given as an interepreter
program in Lisp itself. McCarthy's list interpreter, implemented as
mutually recursive _eval_ and _apply_ functions, is often cited as
an example of metacircular evaluation -  defining the evaluation
semantics of embedded language in terms of evaluation semantics of
host-language, which happens to be same as embedded languge.
Interestingly, McCarthy defines Lisp as a dynamically scoped language
(Paul Graham
[says](http://languagelog.ldc.upenn.edu/myl/ldc/llog/jmc.pdf) so,
but is it really? Reynolds's 2nd interpreter, which he says is similar
to McCarthy's, is lexically scoped.).

In order to use metacircular lisp interpreter to interpret a lisp
program, the program first has to be converted to data. In other
words, all M-expressions need to be translated to S-expressions (Note:
this means that M-expressions are only a syntactic sugar). A simple
algorithm to perform the same has been described in the paper. The
algorithm converts all function names and their arguments in the user
lisp program (which are meta-variables) to atomic symbols. The
interpreter (_eval_ function, to be specific) maintains an environment
which defines bindings for these atomic symbols. However, note that
the original program may also contain atomic symbols, and these
symbols have no attached interpretation. To distinguish between atomic
symbols that are present in the user program, and atomic symbols that
are introduced while convering M-expressions to S-expressions, the
former set of atomic symbols are quoted.

As mentioned previously, Lisp is the first language that abstracted
the underlying machine completely. In order to be able to do that, the
run-time should be able to manage scarce machine resources, such as
memory. Towards this end, Lisp introduced automated memory
reclamation, which is now commonly known as "Garbage Collection".

### 2.Definitional Interpreters Paper ###


The Lisp paper defines semantics of Lisp using a metacircular
interpreter written in Lisp itself. The definitional interpreters
paper by Reynolds exposes subtle aspects of such definitional
interpreters. In particular, it shows how semantics of the embedded
language (called the defined language) can depend on semantics of the
host language (called the defining language), such as its treatment of
higher-order functions, and the order of function application . To
demonstrate this point, the paper first constructs a metacircular
interpreter for a higher-order (defined) language in another
higher-order (defining) language, by simply translating an expression
(eg: function application) in defined language as the corresponding
expression in defining language. The paper makes two observations
about this interpreter:

1. The nature of higher-order functions is not clear.  
2. The order of application is not explicit; the order of evaluating
   function applications  in defined language depends on
   whether the defining language is call-by-value or call-by-name.

Subsequently, Reynolds proposes two transformations to make the
treatment of higher-order functions, and order of function
applications explicit in the semantics of defined language:

1. Defunctionalization: A function in defined language is not a
   function in defining language. Instead, functions and function
   closures are represented explicitly as data structures (For eg, as
   S-expressions in Lisp interpreter), and the semantics of a function
   application is defined explicitly, as a transformation over data.
   Defunctionalization effectively lets us write a definitional
   interpreter for a higher-order language in a first-order language.
2. CPS transformation: A continuation is a function that explicitly
   represents "rest of the computation". At every atomic step of
   evaluation in a definitional interpreter, if we explicitly describe
   what "rest of the evaluation" is, then the semantics of defined
   language no longer depends on order of evaluation of defining
   language; the order of evaluation is now explicit in the
   interpreter. This kind of interpreter is said to be written in
   continuation passing style (CPS). 

The paper also describes how imperative features, such as assignments,
can be encoded explictly in a definitional interpreter written in
applicative style.

