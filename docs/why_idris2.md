# Why Idris2?

## Motivation

This project deliberately adopts **Idris2** as its primary language, despite the existence of more popular alternatives such as Lean, Haskell, or Rust with advanced type systems.

This choice is not driven by novelty, popularity, or personal preference.
It follows directly from the *kind of systems we aim to model* and the *semantic guarantees we require*.

In short:

> **Idris2 is chosen because it allows us to define systems, not merely implement or prove properties about them.**

---

## Problem Context

The target domain of this project includes:

- Systems-of-Systems (SoS)
- Failure–recovery semantics
- Explicit obligations, evidence, and observability boundaries
- Test coverage and unreachable-state elimination
- AI-assisted program synthesis and verification

These domains require a language that can:

1. Treat *types as first-class semantic objects*
2. Preserve proofs and evidence at runtime when desired
3. Express *unreachability* and *obligation discharge* at the type level
4. Remain executable, testable, and deployable as a systems language

Most mainstream languages satisfy only a subset of these requirements.

---

## Why Not Lean?

Lean is an excellent **proof assistant** and a strong candidate for formal mathematics.
However, it is optimized around a fundamentally different design goal.

### Key Limitation

Lean enforces a strict separation between:

- `Prop` (proofs)
- `Type` (computational data)

Proofs are *erased* during execution by design.

This makes Lean unsuitable for systems where:

- Proofs must remain as **runtime evidence**
- Failure traces and recovery obligations are *observable artifacts*
- Semantic structure must survive compilation and execution

In this project, proofs are not meta-level artifacts.
They are *part of the system state*.

Lean’s design explicitly forbids this.

---

## Why Not Haskell?

Haskell provides an exceptionally mature ecosystem and powerful abstractions.
However, its type system remains **non-dependent** in a strict sense.

### Structural Limitations

While Haskell supports:

- GADTs
- Type families
- Singleton encodings

these features simulate dependent types rather than natively supporting them.

As a result:

- Value-level invariants cannot fully constrain the program
- Semantic unreachability cannot be expressed globally
- Coverage and exhaustiveness remain heuristic rather than provable

For example:

> A state being *logically impossible* cannot be enforced as a compile-time fact across the entire system.

This limitation directly impacts the core claim of this project:
**eliminating combinatorial explosion via type-level semantics**.

---

## Why Idris2?

Idris2 occupies a rare design point:

> **A fully dependent type system combined with an executable systems language.**

### Core Properties

- Types and values share the same computational universe
- Proofs are ordinary values and may persist at runtime
- Erasure is explicit and controlled, not implicit
- Linear types allow direct modeling of resource usage
- Backends exist for C, Chez Scheme, and WASM-like targets

This enables a style of development where:

- Semantic invariants are *defined once*
- Tests are derived from the same definitions
- Unreachable states are eliminated structurally
- Coverage metrics align with semantic structure

---

## Idris2 as a Semantic Definition Language

In this project, Idris2 is not treated as a general-purpose application language.

Instead, it plays the role of a **semantic definition language**.

Concretely:

- Idris2 defines the *meaning* of computation
- Other languages (Rust, Haskell, Solidity, etc.) are potential *lowerings*
- AI agents operate primarily at the Idris2 level
- Correctness flows downstream, not upstream

This mirrors the role of:

- Coq in verified compilers
- Agda in language semantics
- Isabelle/HOL in protocol logic

—but with the crucial difference that **the definitions are executable**.

---

## AI-Assisted Development Considerations

Idris2’s strictness is a feature, not a drawback, for AI-driven workflows.

- Ill-defined code fails immediately
- Partial definitions are rejected
- Ambiguous semantics cannot be compiled

This creates a strong feedback signal for AI agents:

> **Either the semantics are correct, or the program does not exist.**

In contrast, more permissive languages allow
“plausible but semantically false” implementations to survive.

For automated reasoning and synthesis, this distinction is critical.

---

## Addressing the “Immaturity” Concern

It is true that Idris2 is:

- Less popular
- Less standardized
- Less “production-ready” than mainstream alternatives

However, this project explicitly targets:

- Research
- Semantic foundations
- Tooling that generates or verifies downstream code

In this context, *maturity is a liability* if it freezes design space prematurely.

Idris2 remains sufficiently flexible to encode new semantic structures
without fighting entrenched idioms.

---

## Summary

Idris2 is chosen because it uniquely satisfies the following conjunction:

- Fully dependent types
- Executable semantics
- Runtime-preserving proofs
- System-level resource modeling
- AI-compatible failure modes

This project does not ask:

> “Which language is most popular?”

It asks:

> “Which language allows the system itself to be defined without semantic loss?”

For this purpose, **Idris2 is not a compromise**.

It is the minimal adequate choice.

---

## Intended Use

- As a semantic specification layer
- As a reference implementation
- As a source of derived tests and coverage metrics
- As an input language for AI-driven development loops

Downstream implementations may—and often should—be written in other languages.

Idris2 defines *what they mean*.

