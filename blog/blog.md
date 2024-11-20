# Outcome Logic in Coq

## Background

Program logics such as Hoare Logic are a useful tool for reasoning about the behavior of programs. For example, in Hoare Logic we can prove a **Hoare triple** `{P} C {Q}` indicating that given a precondition `P` is true, some postcondition `Q` will hold after executing the program `C`.

A Hoare triple can specify the correctness of the program. For example,
```
{y ≠ 0} z = div(x, y) {z is defined}
```
encodes that `z` will be defined as long as `y` is not equal to `0`. If this triple is provable, then we've shown that our implementation of `div` is correct according to this specification.

What if we want to specify the _incorrectness_ of the program instead (e.g. to know with certainty that the program has some bug)?
```
x = malloc(n)
*x = 1
```
Let's say we want to show that this program has a "bug" in the case that `malloc` fails and `x` is assigned to `null`. We might try proving the following Hoare triple specifying that the program will result in a "buggy" state:
```
{⊤} x = malloc(n) ; *x = 1 {*x fails}
```
However, in Hoare Logic our postcondition must be true for _any_ execution of the program. We could only prove the above triple if `malloc` _always_ failed. For this reason, we have to prove the following Hoare triple:
```
{⊤} x = malloc(n) ; *x = 1 {x ↦ 1 ∨ *x fails}
```
This triple appears to state that the program will either result in (1) `x` mapping to `1` or (2) a failure when `x` is dereferenced. However, the postcondition `x ↦ 1 ∨ *x fails` does not necessarily specify incorrectness: for any provable Hoare triple `{P} C {Q}` we can always prove `{P} C {Q ∨ ⊥}` -- even if `C` is correct!

That said, in practice we often find bugs in programs by showing their existence (e.g. through unit tests). For this reason, it would be nice to be able to reason about programs through their incorrectness. Recently, program logics such as Incorrectness Logic [^incorrectness-logic] have been developed for this purpose.

In Incorrectness Logic, an **incorrectness triple** `[P] C [Q]` indicates that given precondition `P`, the postcondition `Q` will hold for _some_ execution of the program `C`. Using an incorrectness triple, we can now encode the exact behavior we wanted to describe about the program before:
```
[⊤] x = malloc(n); *x = 1 [*x fails]      -- brackets instead of curly braces
```
Proving this triple now truly shows that the program has a bug -- there is some execution of the program that will result in a failure when dereferencing `x`.

However, because incorrectness logic underapproximates (the postcondition need only be true for some execution of the program) -- it is not suitable for proving the correctness of a program (which necessitates reasoning about _all_ executions of a program).

Outcome Logic [^outcome-logic] is a recent generalization of Hoare Logic that allows you to reason about both the correctness _and_ incorrectness of a program.

The approach that Incorrectness Logic takes to reason about the existence of bugs in programs is to underapproximate (the postcondition need only be true for some execution of the program). However, the issue with Hoare Logic is not that it overapproximates but rather that it is not rich enough to talk about _reachability_: the logical disjunction `P ∨ Q` gives no guarantee that both `P` and `Q` are reachable.

On the other hand, Ouctome Logic is enriched with an outcome conjunction `P ⊕ Q` indicating that _both_ the conditions `P` and `Q` are reachable. An **outcome triple** `⟨P⟩ C ⟨Q⟩` still indicates that `Q` is satisfied for any execution of the program as in Hoare Logic, but we can now specify both the correctness and incorrectness of the earlier example in a single triple:
```
⟨⊤⟩ x = malloc(n); *x = 1 ⟨x ↦ 1 ⊕ *x fails⟩        -- angle brackets
```
Proving this outcome triple not only shows that there is an execution of the program that is buggy -- it also shows that there is an execution of the program that is correct.

Outcome Logic still lets us talk about programs that are entirely correct (as the postcondition must be satisfied for any execution of the program), and we can also still talk about a single bug in the program as in Incorrectness Logic. Instead of listing out every possible outcome, we can use the outcome conjunction with `⊤`:
```
⟨⊤⟩ x = malloc(n); *x = 1 ⟨⊤ ⊕ *x fails⟩
```
Using the outcome conjunction with `⊤` underapproximates: it guarantees that there is a bug (as `*x fails`), but there may be other behaviors that are not covered (in the case that the trivial postcondition `⊤` is satisfied).

## Project Summary

### Introduction

The goal of our project is to encode outcome logic in Coq. Program logics have proven to be particularly useful in mechanized settings (e.g. the concurrent separation logic framework Iris [^iris]). In addition to being monoidal (to reason about reachability of different outcomes), Outcome Logic is also monadic (to capture different computational effects). We believe Outcome Logic would be a helpful program logic to encode in Coq to prove both correctness and incorrectness properties about programming languages with effectful properties, such as nondeterminism or probabilistic behavior.

### Roadmap and Ongoing Work
We plan to encode outcome logic for a command language (CL) with nondeterministic branching. Outcome logic is usually formulated over the denotational semantics for programs. Because CL is nonterminating and nondeterministic, we interpret CL programs using choice trees [^ctree].

Choice trees are a recent extension to interaction trees [^itrees] (a general-purpose data structure for representing behavior of impure and potentially non-terminating programs) that can be used to model nondeterministic behavior. Crucially, interactions trees can exhibit invisible behavior, which is used to encode "stutter" steps, silently divergent programs, and is generalized to non-deterministic branching in choice trees. Quotienting computation trees by invisible behavior induces a weak bisimulation relation, which we utilize for equivalence in our semantic domain.

The denotational semantics that outcome logic is formulated over assumes programs are interpreted to an _execution model_ that is both a monad and a partial commutative monoid. We also chose to use choice trees because they are a monad and additionally form a commutative monoid.

### Command Language
We start by embedding the command language `cl` used in the original outcome logic paper, defined below:

```coq=
Inductive cl : Type :=
| Zero                         (* sugared to 𝟘 *)
| One                          (* sugared to 𝟙 *)
| Seq : cl -> cl -> cl         (* sugared to ⨟ *)
| Branch : cl -> cl -> cl      (* sugared to + *)
| Star : cl -> cl              (* sugared to ⋆ *)
| Atom : cmd -> cl.
```

We then denote the first four cases of`cl` into choice trees in the following way:
- `𝟘`  is translated to stuck, a branching choice tree that has no branches.
- `𝟙` is translated to identity in the choice tree monad.
- `⨟` is translated to bind in the choice tree monad.
- `+` is translated to branching in the choice tree monad.

By our monad laws and the fact choice trees form a monad, we have the following properties of our logic automatically, where $\equiv$ represents weak bisimulation:
- 𝟙 (unit) is identity. $𝟙⨟\alpha\equiv\alpha⨟𝟙\equiv\alpha$ 
- ⨟ (bind) is associative. $(\alpha⨟\beta)⨟\theta \equiv \alpha⨟(\beta⨟\theta)$.

We also have commutativity for free. Branching in choice trees occur internally (as a generalized form of the taus in interaction trees), which force branches to be commutative modulo visible behavior. As a result of the identity, associativity, and commutativity properties of our choice trees, we have the necessary algebraic properties to form the commutative monoid used in Outcome Logic.

Unlike the original outcome logic paper, our domain is not partial. For example, we denote `⋆` a bit differently, chosing to define it via direct iteration, taking advantage of the coinductive nature of interaction trees. By contrast, the original outcome logic paper defines `⋆` as a least fixed point of the following equational rule $c^⋆ = cc^⋆ + 1$.

Finally, we give our computational model state and denote atoms as either boolean tests (which can currently only test $\top$ and $\bot$) or updates to the state.

### Future Work
We have not yet proved interesting properties of the Outcome Logic proof system (e.g. soundness). We also have not yet proved properties about non-deterministc programs (e.g. the shuffle example in the original Outcome Logic paper). We aspire to complete the above two tasks.

[^itrees]: Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur, Gregory Malecha, Benjamin C. Pierce, and Steve Zdancewic. 2020. Interaction Trees: Representing Recursive and Impure Programs in Coq. Proc. ACM Program. Lang. 4, POPL, Article 51 (January 2020), 32 pages. https://doi.org/10.1145/3371119

[^alg-effects]: Donnacha Oisín Kidney, Zhixuan Yang, and Nicolas Wu. 2024. Algebraic Effects Meet Hoare Logic in Cubical Agda. Proc. ACM Program. Lang. 8, POPL (2024), 1663–1695. https://doi.org/10.1145/3632898

[^iris]: Ralf Jung, David Swasey, Filip Sieczkowski, Kasper Svendsen, Aaron Turon, Lars Birkedal, and Derek Dreyer. 2015. Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning. In POPL. 637–650. https://doi.org/10.1145/2676726.2676980

[^our-repo]

[^incorrectness-logic]: Peter W. O’Hearn. 2019. Incorrectness Logic. Proc. ACM Program. Lang. 4, POPL, Article 10 (Dec. 2019), 32 pages.
https://doi.org/10.1145/3371078

[^our-repo]: https://github.com/InnovativeInventor/outcome-logic-coq

[^outcome-logic]: Noam Zilberstein, Derek Dreyer, and Alexandra Silva. 2023. Outcome Logic: A Unifying Foundation for Correctness and Incorrectness Reasoning. Proc. ACM Program. Lang. 7, OOPSLA1, Article 93 (April 2023),
29 pages. https://doi.org/10.1145/3586045

[^ctree]: Nicolas Chappe, Paul He, Ludovic Henrio, Yannick Zakowski, and Steve Zdancewic. 2023. Choice Trees: Representing Nondeterministic, Recursive, and Impure Programs in Coq. Proc. ACM Program. Lang. 7, POPL, Article 61 (January 2023), 31 pages. https://doi.org/10.1145/3571254

[^ctree-github]: https://github.com/vellvm/ctrees/tree/jfp
