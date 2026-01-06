# Failure–Recovery Monads

## Recovery-Preserving Kleisli Semantics for World-Computer Virtual Machines

---

## Abstract

This paper introduces the **Failure–Recovery Monad (FR Monad)**, a monadic semantic structure for systems in which failure, evidence, and recovery are first-class values.
Failures are modeled as explicit results paired with mandatory evidence, and recovery is expressed as a compositional structure rather than as implicit control flow.

Composability is characterized not by the abundance of successful execution paths, but by the **existence of recovery-preserving morphisms whose meaning is invariant under Kleisli composition**.
Monad laws are interpreted as semantic invariants ensuring that refactoring and modularization preserve recovery obligations.

We present state-indexed and obligation-graded realizations of the FR Monad, and demonstrate that the Ethereum Virtual Machine (EVM), due to its synchronous execution model and atomic failure semantics, constitutes a privileged experimental substrate.
We further report on practical implementations in Idris2, including a coverage framework that resolves a fundamental incompatibility between dependent types and conventional coverage metrics, and a subcontract framework that applies the FR Monad end-to-end.

---

## 1. Introduction

In large-scale computational systems, failure is inevitable.
The central semantic question is therefore not how to eliminate failure, but how failure behaves under composition.

In many existing models, failures are treated as exceptional control-flow exits and are erased during compilation or optimization.
This erasure destroys information required for compositional reasoning, particularly in systems that rely on strong static guarantees.

This paper proposes a semantic discipline in which:

* failures are values,
* evidence is mandatory,
* and recovery is structurally preserved.

---

## 2. Preliminaries

We work in ordinary set-theoretic mathematics.

Let:

* $$S$$ be the set of global states,
* $$V$$ the set of values,
* $$F$$ the set of classified failure modes,
* $$E$$ the set of evidence.

Define the result type:
$$
R := (V \times E) ;\cup; (F \times E)
$$

Every computation produces a result paired with evidence.
There are no observationally silent transitions.

---

## 3. Failure–Recovery Morphisms

A **Failure–Recovery morphism** is a function
$$
f : S \to (S \times R)
$$

Failures are ordinary outputs.
They are not control-flow escapes.

---

### 3.1 Boundaries and Recovery Interfaces

Let $$B$$ be a set of boundaries representing execution regimes.

Each boundary $$b \in B$$ induces a recovery interface:
$$
\mathsf{Resolve}_b : (F \times E) \to \mathcal{P}(A_b)
$$

A system is recovery-closed at boundary $$b$$ if failures are either resolved internally or explicitly exported.

---

## 4. Recovery-Aware Kleisli Composition

Assume evidence forms a monoid $$(E, \oplus, e_0)$$.

Kleisli composition is defined such that:

1. Evidence accumulates via $$\oplus$$.
2. Failures propagate unless handled.
3. No failure is erased without recovery.

This defines a Kleisli category $$\mathcal{K}_{FR}$$.

---

## 5. The Failure–Recovery Monad

The construction above induces a monad $$\mathsf{FR}$$.

### 5.1 Monad Laws as Semantic Invariants

* **Unit laws** ensure that pure computations introduce no recovery obligations.
* **Associativity** ensures that refactoring does not change recovery meaning.

These laws guarantee that recovery obligations are invariant under composition.

---

## 6. Composability

### Definition (Composability)

A system is composable if and only if the required recovery-preserving morphisms exist in $$\mathcal{K}_{FR}$$.

Success-path enumeration is irrelevant.

---

## 7. Indexed and Graded Variants

### 7.1 State-Indexed FR Monad

We define:
$$
\mathsf{IFR} : \mathsf{State} \to \mathsf{State} \to \mathsf{Type} \to \mathsf{Type}
$$

Composition exists only if state transitions align.

---

### 7.2 Obligation-Graded FR Monad

We further define:
$$
\mathsf{GFR} : \mathsf{Obligations} \to \mathsf{Type} \to \mathsf{Type}
$$

Grades accumulate under composition and statically track unresolved recovery obligations.

---

## 8. Typed Realizations in Idris2

In Idris2:

* $$F$$ is realized as a closed sum type.
* $$E$$ is realized as a structured record.
* Recovery interfaces are total functions over classified failures.

Invalid compositions manifest as type errors.

---

## 9. The EVM as a Privileged Substrate

The Ethereum Virtual Machine provides:

* synchronous call semantics,
* deterministic execution order,
* revert-based atomicity,
* canonical execution traces.

These properties align precisely with recovery-aware Kleisli composition.

---

## 10. Evaluation and Implementation

### 10.1 FR Semantics for the EVM

The FR Monad is implemented in Idris2 for an EVM-like instruction set
(see *idris2-evm* and *idris2-yul*).

The implementation demonstrates that:

* failures are explicitly classified,
* evidence is mandatory,
* recovery structure composes as predicted by the semantics.

---

### 10.2 Coverage in Dependently Typed Languages

Conventional coverage metrics assume that all syntactic branches are observable at runtime.
This assumption fails in dependently typed languages.

In Idris2, branches that are statically proven unreachable are **eliminated during compilation** and do not appear in the resulting binary.
Naïvely counting such branches as coverage candidates renders coverage meaningless.

The *idris2-evm-coverage* framework resolves this incompatibility by:

* distinguishing *syntactic branches* from *reachable execution branches*,
* removing statically unreachable branches from the coverage domain,
* computing hit counts only over dynamically realizable paths.

Formally, coverage is defined over the quotient of the syntactic control-flow graph by compile-time unreachability.

This restores coverage as a meaningful observational tool and enables unit tests to probe the remaining semantic surface where recovery obligations may arise.

As a result, test suites can precisely target the “gaps” left by monadic safety guarantees, ensuring that recovery behavior is exercised where static typing alone is insufficient.

---

### 10.3 Subcontracts as End-to-End FR Applications

The *idris2-subcontract* framework applies the FR Monad across the full lifecycle of contract interaction:

* specification,
* composition,
* execution,
* failure propagation,
* and recovery handling.

Subcontracts explicitly encode recovery obligations at module boundaries and ensure that:

* failures cannot cross boundaries without evidence,
* unresolved obligations are statically visible,
* and composition is rejected when recovery structure is incomplete.

This framework constitutes a full application of the FR Monad, validating that the theory scales from individual computations to multi-contract systems.

---

## 11. Discussion

The FR Monad reframes safety and testing:

* Static typing enforces structural correctness.
* Graded obligations expose unresolved recovery.
* Coverage, corrected for dependent-type compilation, probes remaining dynamic behavior.

These mechanisms are complementary rather than redundant.

---

## 12. Conclusion

We have presented the Failure–Recovery Monad as a compositional semantic structure in which failure, evidence, and recovery are explicit and preserved.

By modeling failures as values with mandatory evidence and interpreting monad laws as invariants of recovery meaning, we obtain a precise criterion for composability: the existence of recovery-preserving morphisms.

State-indexed and obligation-graded variants enable static enforcement, while corrected coverage techniques ensure that dynamic testing remains meaningful in dependently typed settings.

The EVM serves as a privileged substrate for experimentation, and the subcontract framework demonstrates that the FR Monad can be applied end-to-end in practical systems.

