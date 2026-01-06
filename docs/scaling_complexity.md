# Scaling Complexity in System-of-Systems Testing

## Overview

This document clarifies how test complexity scales in System-of-Systems (SoS) architectures,
and why the apparent “complexity reduction” achieved by the GFR formulation should not be
misunderstood as eliminating inherent difficulty.

The central claim is not that complexity disappears,
but that **complexity becomes explicit, localized, and conditionally manageable**.

In contrast, traditional testing strategies often *silently collapse* under the same conditions.

---

## Terminology

We fix the following definitions:

- **N**: Number of services composed in the system
- **K**: Maximum number of failure / obligation categories per service
- **Traditional testing**: Integration testing by enumerating all success/failure combinations
- **GFR-based testing**: Testing structured around obligation handlers and typed composition

---

## Traditional Scaling: Implicit Collapse

In traditional integration testing, each service is typically modeled as:

```

service_i : Input → {Success, Failure}

```

For N services, this induces:

```

2^N integration scenarios

````

### The Hidden Assumptions

This enumeration implicitly assumes:

1. Failures are independent
2. Failure categories are irrelevant (all failures are equal)
3. Recovery behavior is context-free
4. Handler order does not affect semantics

When **K = 1**, these assumptions may approximately hold.

When **K > 1**, they no longer do.

Yet traditional testing does not fail loudly when these assumptions are violated.
Instead, it continues to enumerate combinations whose semantic meaning is undefined.

This is the first form of collapse: **loss of meaning without loss of tests**.

---

## GFR Scaling: Explicit Semantics

In the GFR formulation, a computation has the shape:

```idris
GFR : Obligations → Type → Type
````

where the type parameter tracks *unresolved recovery obligations*.

Execution is only permitted when all obligations are discharged:

```idris
runGFR : GFR [] a → Either (Fail, Evidence) (a, Evidence)
```

### Consequences

* Unhandled failures cannot be executed
* Recovery is not implicit control flow, but explicit structure
* Failure categories are preserved as values
* Evidence accumulates monotonically

This immediately changes the scaling question.

---

## Scaling When K = 1

When there is a single obligation category:

* Each handler can be tested independently
* Integration tests only need to verify representative paths
* The type system guarantees that no unhandled failures remain

In this regime:

```
T_gfr(N, K=1) = O(N)
```

This is the regime demonstrated in the current experiment.

---

## What Changes When K > 1

When multiple obligation categories are present, **complexity does not reappear magically**.
Instead, **new semantic structure becomes visible**.

Crucially:

> K > 1 is not a failure of GFR.
> It is the point at which previously hidden assumptions are exposed.

### 1. Handler Interaction Becomes Observable

Handlers are no longer guaranteed to commute:

```
h_a ∘ h_b ≠ h_b ∘ h_a
```

The order of recovery now has semantic meaning.

Traditional testing implicitly ignores this.
GFR makes it explicit.

### 2. Recovery Becomes Context-Dependent

The same failure category may require different recovery depending on:

* Which service failed
* At which phase of execution
* Whether downstream effects are idempotent

In traditional testing, this context is erased.
In GFR, insufficiently precise obligations result in type-level friction.

### 3. Cascading Failures Become Typed

A recovery value may trigger new failures downstream.

This is not a new problem introduced by GFR.
It is a real system behavior that traditional testing masks by flattening failures to booleans.

---

## Reframing “Breakdown”

It is misleading to say that GFR “breaks down” when K > 1.

A more accurate statement is:

> **Traditional testing collapses silently, while GFR refuses to hide complexity.**

GFR does not claim to eliminate inherent system complexity.
It ensures that complexity cannot be ignored or accidentally erased.

---

## Comparative Summary

| Aspect                 | Traditional Testing   | GFR-Based Testing               |
| ---------------------- | --------------------- | ------------------------------- |
| Failure representation | Boolean               | Typed value + evidence          |
| Unhandled failure      | Runtime artifact      | Type error                      |
| K > 1 behavior         | Implicitly ignored    | Explicitly surfaced             |
| Handler order          | Undefined             | Semantically relevant           |
| Test explosion         | Hidden by enumeration | Localized to interaction points |

---

## Practical Interpretation

When K > 1, additional work is required:

* More precise obligation types
* Explicit handler ordering or composition laws
* Targeted tests for interaction boundaries

This is not a regression.
It is the *minimum necessary work* to preserve semantic correctness.

Traditional approaches appear simpler only because they discard information.

---

## Conclusion

The contribution of the GFR formulation is not that it makes complex systems simple.

It makes them **honest**.

* When assumptions hold, complexity scales linearly.
* When assumptions fail, the failure is explicit and localized.
* No semantic complexity is hidden behind combinatorial enumeration.

In System-of-Systems engineering, this distinction is decisive.

