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

The approach that Incorrectness Logic takes to reason about the existence of bugs in programs is to underapproximate (the postconditon need only be true for some execution of the program). However, the issue with Hoare Logic is not that it overapproximates but rather that it is not rich enough to talk about _reachability_: the logical disjunction `P ∨ Q` gives no guarantee that both `P` and `Q` are reachable.

On the other hand, Ouctome Logic is enriched with an outcome conjunction `P ⊕ Q` indicating that _both_ the conditions `P` and `Q` are reachable. An **outcome triple** `⟨P⟩ C ⟨Q⟩` still indicates that `Q` is satisfied for any execution of the program as in Hoare Logic, but we can now specify both the correctness and incorrectness of the earlier example in a single triple:
```
⟨⊤⟩ x = malloc(n); *x = 1 ⟨x ↦ 1 ⊕ *x fails⟩        -- angle brackets
```
Proving this outcome triple not only shows that there is an execution of the program that is buggy -- it also shows that there is an execution of the program that is correct.

Outcome Logic still lets us talk about programs that are entirely correct (as the postcondition must be satisfied for any executiono of the program), and we can also still talk about a single bug in the program as in Incorrectness Logic. Instead of listing out every possible outcome, we can use the outcome conjunction with `⊤`:
```
⟨⊤⟩ x = malloc(n); *x = 1 ⟨⊤ ⊕ *x fails⟩
```
Using the outcome conjunction with `⊤` underapproximates: it guarantees that there is a bug (as `*x fails`), but there may be other behaviors that are not covered (in the case that the trivial postcondition `⊤` is satisfied).

## Project Summary

### Introduction

Our project encodes outcome logic in Coq. Program logics have proven to be particularly useful in mechanized settings (e.g. the concurrent separation logic framework Iris [^iris]). In addition to being monoidal (to reason about reachability of different outcomes), Outcome Logic is also monadic (to capture different computational effects). We believe Outcome Logic is a helpful program logic to encode in Coq to prove both correctness and incorrectness properties about programming languages with effectful properties, such as nondeterministim or probabilistic behavior.

### Command Language
We work with a command language (CL) with nondeterministic branching and memory loads/stores. Here is the syntax in Coq:

```coq=
Inductive cl : Type :=
| Zero                         (* sugared to 𝟘 *)
| One                          (* sugared to 𝟙 *)
| Seq : cl -> cl -> cl         (* sugared to ⨟ *)
| Branch : cl -> cl -> cl      (* sugared to + *)
| Star : cl -> cl              (* sugared to ⋆ *)
| Atom : cmd -> cl.
```

The command language encodes the flow of the program, whereas atomic commands actually perform memory loads/stores (as well as tests on expressions and assigning local variables). Here is the Coq syntax for atomic commands:

```coq=
Inductive cmd : Type :=
| Assume : expr -> cmd              (* sugared to just 'e' *)
| Not : expr -> cmd                 (* sugared to ¬ e *)
| Assign : string -> expr -> cmd    (* sugared to x <- e *)
| Alloc : string -> cmd             (* sugared to x <- alloc *)
| Load : string -> expr -> cmd      (* sugared to x <- [ e ] *)
| Store : expr -> expr -> cmd.      (* sugared to [ e1 ] <- e2 *)
```

If we let `x <- malloc` just represent `x <- alloc + x <- null`, the previous malloc example can be written in Coq as:

```coq=
Seq
  (Branch
    (Atom (Alloc x))
    (Atom (Assign x Null)))
  (Atom (Store (Var x) (Lit 1)))
```

With Coq notation, we can write it almost as we had it before:
```coq=
  x <- malloc ⨟
  [ x ] <- 1
```

### Semantics

We depart from the original Outcome Logic paper and use an operational, big-step semantics for the command language, with `(C , σ) ⇓ σ'` denoting that the program `C` evaluates the state `σ` to `σ'`. A state is either an error state (representing a memory error) or a stack (static memory) + heap (dynamic memory). Atomic commands modify the stack and heap, possibly resulting in an error state (in the case of a null pointer dereference).

### Encoding outcome logic

Let `ϕ`, `ψ` range over outcome logic assertions ---- with `P`, `Q` instead ranging over atomic assertions (e.g. propositions). We say that an outcome triple `⟨ ϕ ⟩ C ⟨ ψ ⟩` is valid (denoted `⊨ ⟨ ϕ ⟩ C ⟨ ψ ⟩`) if running the program on any state that satisfies the precondition results in a set of states that all satisfiy the postcondition. This is slightly different from the definition in the original Outcome Logic paper -- they generalize the definition over an arbitrary monad, while we fix our monad to the powerset monad. We do so to be able to prove concrete properties about nondeterministic programs (in particular, that our working malloc example can result in a trace that has a memory error).

We do not go over all of the assertions in outcome logic, instead we go over atomic assertions and the outcome logic assertion `ϕ ⊕ ψ`. We say that a set `S` satisfies this assertion (denoted `S ⊨ ϕ ⊕ ψ`) if `S = S1 ∪ S2` and `S1 ⊨ ϕ` and `S2 ⊨ ψ`. Atomic assertions are those relating to a specific "outcome", e.g. `x --> 1` (the pointer stored at `x` maps to `1` in the heap). A set satisfies an atomic assertion if it is a singleton set with a single state satisfying the outcome.

We also have an atomic assertion `ok` that is satisfied by any non-error state and an atomic asserion `error` satisfied by the error state.

### Outcome Logic rules

We encode a set of rules (denoted `⊢ ⟨ ϕ ⟩ C ⟨ ψ ⟩` that can be used to derive the validity of an outcome triple. For example:
```coq=
   ⊢ ⟨ phi ⟩ C1 ⟨ psi ⟩   ->   ⊢ ⟨ psi ⟩ C2 ⟨ theta ⟩ ->
  (* ------------------------------------------------ *)
              ⊢ ⟨ phi ⟩ C1 ⨟ C2 ⟨ theta ⟩
```
The first main result we prove is that these rules are _sound_:
```
if ⊢ ⟨ ϕ ⟩ C ⟨ ψ ⟩, then ⊨ ⟨ ϕ ⟩ C ⟨ ψ ⟩
```

### Putting it all together

With our encoded OL rules, we are able to derive the OL triple:
```coq=
  ⊢ ⟨ ok ⟩ x = malloc(n) ⨟ [ x ] = 1 ⟨ x --> 1 ⊕ error ⟩
```

By the soundness of our rules, we have`⊨ ⟨ ok ⟩ x = malloc(n) ⨟ [ x ] = 1 ⟨ x --> 1 ⊕ error ⟩`. The validity of this outcome triple means that if we run this program on any non-error state, one of our possible outcomes is an error.

### Other properties of Outcome Logic
Our other main results are other properties about Outcome Logic itself.
Following the original Outcome Logic paper, we define the semantic interpretation of an Outcome Logic assertion $\phi$ to be the set of models $\Phi \in 2^{M\Sigma}$ that satisfy the assertion. (Note that in our case $M\Sigma=2^{\Sigma}$).

A semantic outcome logic triple is then defined as follows:
$$
\vDash_S \langle \Phi \rangle\,C\,\langle \Psi \rangle \text{ iff } \forall m \in M\Sigma, m \in \Psi \implies [[C]] (m) \in \Psi
$$

With these definitions, we proved the following theorems from the Outcome Logic paper:
- *semantic falsification* for a triple $\langle \Phi \rangle\,C\,\langle \Psi \rangle$, which states that a semantic triple does not hold [^caveat] if and only if there exists some $\Phi' \subseteq \Phi$ consistent with the precondition such that the semantic triple $\langle \Phi' \rangle\,C\,\langle \lnot \Psi \rangle$ holds. (Negation of a semantic assertion is complement in the powerset $\lnot \Phi = 2^{M\Sigma} - \Phi$.)
- *equivalence of semantic and syntactic triples*, which states that the semantic interpretation of assertions holds in the semantic outcome logic triple if and only if the corresponding syntactic triple holds

These theorems together let us prove *principle of denial*, which states that if there is a syntatic assertion $\phi'$, $\phi'$ is satisfiable, and the syntactic triple $\langle \phi' \rangle\,C\,\langle \lnot \psi \rangle$ holds, then the syntactic triple $\langle \phi \rangle\,C\,\langle \psi \rangle$ does not hold for any weaker precondition $\phi$ (that is, $\phi' \implies \phi$).

### Conclusion
We have encoded an instance of outcome logic in Coq and used it prove the (in)correctness of nondeterministic programs with dynamic memory. We have additionally mechanized in Coq properties about Outcome Logic shown in the original Outcome Logic paper. As future work, we would like to 1) generalize this framework to an arbitrary monad to make it more reusable, explore other instantiations of outcomne logic (e.g. to prove properties about probabilistic programs), and 3) use Coq to explore extensions to outcome logic, such as relational outcome logic.

[^caveat]: We interpret a semantic triple to not hold as constructively meaning that there exists a countermodel that falsifies the triple.

[^iris]: Ralf Jung, David Swasey, Filip Sieczkowski, Kasper Svendsen, Aaron Turon, Lars Birkedal, and Derek Dreyer. 2015. Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning. In POPL. 637–650. https://doi.org/10.1145/2676726.2676980

[^incorrectness-logic]: Peter W. O’Hearn. 2019. Incorrectness Logic. Proc. ACM Program. Lang. 4, POPL, Article 10 (Dec. 2019), 32 pages.
https://doi.org/10.1145/3371078

[^our-repo]: https://github.com/InnovativeInventor/outcome-logic-coq

[^outcome-logic]: Noam Zilberstein, Derek Dreyer, and Alexandra Silva. 2023. Outcome Logic: A Unifying Foundation for Correctness and Incorrectness Reasoning. Proc. ACM Program. Lang. 7, OOPSLA1, Article 93 (April 2023),
29 pages. https://doi.org/10.1145/3586045
