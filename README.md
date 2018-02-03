# Random Coq Code

Hello. This repository contains some random Coq code, as you probably have guessed from the name. The structure of the development is as follows:

* RCCBase.v contains some basic tactics and auxiliary stuff.
* DS/ contains data structures.
* Memoization/ is a lame attempt at memoizing functions. Nothing worth looking at.
* Reflection/ has some code on proof by reflection.
* Sorting/ uses stuff from DS/ to implement and verify sorting algorithms.
* Structures/ has implementations of algebraic and order-theoretic structures needed for sorting and doing reflection
* Trash/ is, well, trash. Don't even look at it.

## Accomplished

Structures/ contains LinDec, an implementation of decidable linear orders, used in most of the sorting algorithms, along with some lemmas and quite powerful automation tactic called dec.

There's also TrichDec, which stands for "decidable trichotomous order". The idea is that such a structure should provide a function  which can decide x < y, x = y or x > y all in one step. It is used in a variant of quicksort. It also comes with appropriate lemmas and automation.

CMon is an implementation of commutative monoids along with a few lemmas used in further developments of reflective tactics. UCRing is an implementation of unitary commutative rings. It comes equipped with most of the basic identities.

Among the basic data structures in DS, there are binary trees, binary search trees and general trees. They are all quite undeveloped and contain only things needed to implement and verify more advanced data structures coming from the book "Purely Functional Data Structures" by Chris Okasaki.

There are queues, deques, splay trees (called splay heaps for some weird reason), redblack trees (not verified yet), leftist heaps, pairing heaps and random access binary lists. There's also a lame attempt at formalizing positional number systems.

It's worth nothing that Binary Random Access List witness a wonderful use of the Bove-Capretta method to define a non-structurally recursive function, derive it's functional induction principle and fixpoint equation.

Sorting/ contains sorting algorithms of two proveniences: classic algorithms like insertion sort, selection sort, merge sort and quicksort, and sorting algorithms based on  the data structures from DS/ — typically variants of tree sort or heapsort. Most of these algorithms are formally verified, but some are not (redblack sort).

The whole development of sorting is based on permutations defined by counting elements in a list. A sort is defined as a function whose input is a sorted permutation of the input. Ther's also a file with various list lemmas which I couldn't find in the standard library.

In Reflection/ you can find simple developments showing how to do reficiation using Ltac and the typeclass mechanism, examples of using reflection to decide propsitions and simplify expressions in commutative monoids (including the use of sorting to reorder terms). In the most advanced development I try to employ reflection to simplify expressions in unitary commutative rings.

There's also an unfinished attempt at doing modular reflection using the "Datatypes à la carte" approach from Wouter Swierstra's paper of the same title.

Memoization/ has verified memoized Fibonacci and nothing besides. Trash/ is useless.

## TODO

* Investigate universe inconsistencies.
* Develop the basic data structures more.
* Define typeclasses for Queues, Heaps, etc.
* Refactor leftist heaps.
* Refactor everything else.
* Investigate modular reflection.
* Remove axioms from Memoization/.
* Finish/remove normalizaion by evaluation example for monoids.
* Prove that perm is equivalent to Permutation from the standard library.
* Prove general facts about sorting algorithms.
* Check if the method used for some functions operating on Binary Random Access Lists is a silver bullet/snake oil that can be used always and everywhere (how nice it would be if this were true).
