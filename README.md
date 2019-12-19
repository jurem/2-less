# 2-less sequences

Let n>1 be a natural number. Consider two triplets x=(x1,x2,x3) and y=(y1,y2,y3), where xi, yi are in the interval from 1 to n. We say that x<y if at least two components of x are less (component-wise) than that of y. A sequence of triplets t=(t1,t2,...,tm) is called a *2-less sequence* if for every i<j it follows that ti<tj. The problem is to generate such a sequence of maximum length.

In this repository you can find:
  * ocaml ... OCaml implementation of generator of such sequences
  * seqs ... some generated sequences
  * isabelle ... proofs of some interesting properties in Isabelle/HOL automatic theorem prover


## OCaml

Install OCaml and compile by running `make`. Programs:
  * enum_all ... enumerates all 2-less sequences
  * count_all ... counts all 2-less sequences
  * solve ... enumerates only minimal 2-less sequences
  
A sequence is called minimal if every element folllowing a prefix is minimal among all set of candidates.

## Isabelle

Install Isabelle and open.
