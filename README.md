# outcome logic in coq
(final project for [cs6115](https://www.cs.cornell.edu/courses/cs6115/2024fa/))

summary
---
This repo contains an encoding of [Outcome Logic](https://dl.acm.org/doi/10.1145/3586045)
in Coq. We depart from the original paper in two significant ways: we use a big-step
operational semantics instead of a denotational semantics and fix our execution model
to the powerset monad.

Our main results are in [`theorems.v`](theories/theorems.v), we mechanized the
soundness of OL's proof rules, semantic falsification, the equivalence of 
syntactic and semantic outcome triples, as well as the principle of denial.

We also have an example of our framework in use in
[`malloc.v`](examples/malloc.v), where we prove the specificiation of a simple
program with malloc that might succeed or have a null dereference error and use
the soundness of OL's proof rules to extract the program traces corresponding
to both outcomes.

structure
---
the main files to look at are:
* [`syntax.v`](theories/syntax.v): syntax of command language
* [`semantics.v`](theories/semantics.v): semantics of command language
* [`assertion.v`](theories/assertion.v): outcome assertion language
* [`ol.v`](theories/ol.v): definition of valid outcome triples
* [`rules.v`](theories/rules.v): outcome logic proof rules

with most proofs in:
* [`soundness.v`](theories/soundness.v): soundness of individual proof rules
* [`lemmas.v`](theories/lemmas.v): general lemmas
* [`theorems.v`](theories/theorems.v): main theorems

there's also:
* [`state.v`](theories/state.v): program state
* [`set.v`](theories/set.v) and [`vec.v`](theories.set.v): data structures used for state

dependencies
---
OCaml version: 5.2.0

Coq version: 8.19.1

building
---
```
dune build
```
or
```
make -f CoqMakefile
```
