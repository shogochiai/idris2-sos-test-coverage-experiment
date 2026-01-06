# Formal Specification: Test Complexity Reduction via GFR Monad

This document provides a rigorous foundation for the claim that GFR Monad + dependent types reduce test complexity from O(2^N) to O(N).

## 1. Definitions

### 1.1 Basic Structures

**Definition 1.1 (Service).**
A *service* is a function `S : I → GFR Φ O` where:
- `I` is the input type
- `O` is the output type
- `Φ ⊆ Obl` is a finite set of *obligations* (potential failure categories)

**Definition 1.2 (Obligation).**
An *obligation* `φ ∈ Obl` is a type-level marker representing an unhandled failure category. The set of all obligations is:
```
Obl = {NetworkObl, AuthObl, ValidationObl, ServiceObl, ...}
```

**Definition 1.3 (Failure Category).**
A *failure category* `κ ∈ Cat` is a runtime classification of failures:
```
Cat = {NetworkFail, AuthFail, ValidationFail, ServiceFail, ...}
```
There exists a bijection `obl : Cat → Obl` mapping each failure category to its corresponding obligation.

**Definition 1.4 (Handler).**
A *handler* for obligation `φ` is a function:
```
h_φ : ((Fail, Evidence) → GFR Ψ A) → GFR (φ :: Ψ) A → GFR Ψ A
```
that intercepts failures of category `obl⁻¹(φ)` and applies a recovery strategy.

**Definition 1.5 (Service Composition).**
Given services `S₁, S₂, ..., Sₙ`, their *sequential composition* is:
```
S₁ >=> S₂ >=> ... >=> Sₙ : I₁ → GFR (⋃ᵢ Φᵢ) Oₙ
```
where `>=>` is Kleisli composition for GFR.

### 1.2 Test Complexity Measures

**Definition 1.6 (Traditional Test Count).**
For a composition of N services, the *traditional test count* `T_trad(N)` is the number of test cases required to cover all success/failure combinations when testing at the integration level:
```
T_trad(N) = ∏ᵢ₌₁ⁿ (1 + |Fᵢ|)
```
where `|Fᵢ|` is the number of distinct failure modes for service `Sᵢ`.

**Definition 1.7 (GFR Test Count).**
The *GFR test count* `T_gfr(N, K)` is:
```
T_gfr(N, K) = T_handler + T_integration
```
where:
- `T_handler = ∑_φ T_φ` is the sum of handler unit tests
- `T_integration` is the number of distinct integration paths
- `K = max_i |Φᵢ|` is the maximum obligations per service

---

## 2. Axioms

The complexity reduction claim holds under the following axioms:

### Axiom 1 (Independence)
Services fail independently. Formally:
```
∀ i ≠ j : P(Sᵢ fails | Sⱼ fails) = P(Sᵢ fails)
```
The failure of service `Sᵢ` does not influence the failure probability or mode of service `Sⱼ`.

### Axiom 2 (Handler Completeness)
Each handler completely addresses its obligation. For handler `h_φ`:
```
∀ (f : Fail) where f.category = obl⁻¹(φ) :
  h_φ recovery (GFail f e) = recovery (f, e)  -- Always recovers
```

### Axiom 3 (Compositional Recovery)
Recovery from failure produces a valid continuation value. If `h_φ` recovers with default value `d`:
```
∀ subsequent services Sⱼ : Sⱼ(d) is well-defined
```

### Axiom 4 (Obligation Disjointness)
Each service's failure modes map to distinct obligations:
```
∀ S with failures F : |{obl(κ) | κ ∈ F}| = |F|
```
No two failure categories share the same obligation type.

### Axiom 5 (Bounded Failure Modes)
Each service has a bounded number of failure modes:
```
∃ K ∈ ℕ : ∀ i : |Fᵢ| ≤ K
```

---

## 3. Propositions

### Proposition 3.1 (Exponential Traditional Complexity)
Under no assumptions, for N services each with at least 2 outcomes (success, failure):
```
T_trad(N) ≥ 2^N
```

*Proof.* Each service contributes at least factor 2 to the product in Definition 1.6. □

### Proposition 3.2 (Linear GFR Complexity)
Under Axioms 1-5, for N services with at most K obligations each:
```
T_gfr(N, K) = O(N × K)
```
When K is constant, `T_gfr(N, K) = O(N)`.

*Proof sketch.*
1. By Axiom 1 (Independence), handler behaviors are orthogonal
2. By Axiom 2 (Handler Completeness), each handler needs testing once
3. By Axiom 4 (Obligation Disjointness), there are at most N × K distinct handlers
4. By Axiom 3 (Compositional Recovery), integration tests need only verify:
   - Happy path (1 test)
   - Each handler activation (N × K tests)
5. Total: `T_gfr(N, K) = N × K + 1 = O(N × K)` □

### Proposition 3.3 (Type-Level Guarantee)
If `runGFR : GFR [] A → Either (Fail, Evidence) (A, Evidence)` type-checks, then all obligations have been discharged by handlers.

*Proof.* By construction of the GFR type:
- `GFR Φ A` requires `Φ` obligations to be handled
- Each handler `h_φ` transforms `GFR (φ :: Ψ) A → GFR Ψ A`
- `runGFR` requires `GFR [] A`, meaning `Φ = []`
- Type checking ensures all handlers were applied □

---

## 4. Counterexamples (Boundary Conditions)

The following conditions cause the complexity to revert to O(2^N):

### Counterexample 4.1 (Correlated Failures)
**Violation of Axiom 1.**

If Service A's network failure causes Service B to fail differently:
```
P(B fails with Timeout | A failed with NetworkError) ≠ P(B fails with Timeout)
```

*Impact:* Must test combinations: A-success/B-success, A-success/B-fail, A-fail/B-fail-correlated, etc.

**Concrete example:**
```idris
-- Service B behaves differently based on A's failure
serviceB : GFR [NetworkObl] Result
serviceB =
  if globalNetworkDegraded  -- Set by A's failure
  then GFail (MkFail NetworkFail "cascade") ...
  else GOk result ...
```

### Counterexample 4.2 (State-Dependent Behavior)
**Violation of Axiom 3.**

If Service B's success path depends on *which* path Service A took, not just A's output:
```
Sᴮ(default_value) ≠ Sᴮ(actual_value) in observable behavior
```

*Impact:* Recovery paths and success paths must be tested separately.

**Concrete example:**
```idris
-- B validates that A's result has certain properties
serviceB : User -> GFR [ValidationObl] Order
serviceB user =
  if user.id == 0  -- Default user from recovery
  then GFail (MkFail ValidationFail "guest cannot order") ...
  else GOk (createOrder user) ...
```

### Counterexample 4.3 (Partial Handlers)
**Violation of Axiom 2.**

If a handler only recovers some failures of its category:
```
∃ (f : Fail) where f.category = obl⁻¹(φ) :
  h_φ recovery (GFail f e) = GFail f' e'  -- Re-fails
```

*Impact:* Must test which sub-cases the handler catches vs propagates.

### Counterexample 4.4 (Obligation Aliasing)
**Violation of Axiom 4.**

If two services share the same obligation but require different handling:
```
S₁ : GFR [NetworkObl] A  -- Wants retry
S₂ : GFR [NetworkObl] B  -- Wants fallback to cache
```

*Impact:* Single handler cannot satisfy both; composition requires case analysis.

### Counterexample 4.5 (Unbounded Failure Modes)
**Violation of Axiom 5.**

If failure modes grow with input or system state:
```
|Fᵢ| = f(input_size) where f is unbounded
```

*Impact:* K is not constant; complexity becomes O(N × f(n)).

---

## 5. Experimental Validation

### 5.1 This Repository's Model

| Parameter | Value | Satisfies Axiom |
|-----------|-------|-----------------|
| N (services) | 4 | - |
| K (max obligations/service) | 1 | Axiom 5 ✓ |
| Independence | Services are pure functions | Axiom 1 ✓ |
| Handler completeness | `handleAll` catches remaining | Axiom 2 ✓ |
| Recovery validity | Default values are valid inputs | Axiom 3 ✓ |
| Obligation disjointness | Single `NetworkObl` type | Axiom 4 ✓ |

### 5.2 Measured Results

| Metric | Traditional | GFR |
|--------|-------------|-----|
| Test cases | 2^4 = 16 | 7 |
| Formula | 2^N | N × K + 1 + 3 |
| Complexity | O(2^N) | O(N) |

Note: 7 = 4 services × 1 handler + 1 happy path + 2 handler behavior tests

### 5.3 Baseline Comparison

See `test/Baseline/` for a traditional test implementation covering all 16 combinations.

---

## 6. Conclusions

### 6.1 Validity Domain

The claim **"O(2^N) → O(N)"** is valid when:
1. Services fail independently (no cascading/correlated failures)
2. Handlers completely address their failure categories
3. Recovery produces valid continuation values
4. Obligations are disjoint across services
5. Failure modes per service are bounded by constant K

### 6.2 Practical Implications

For microservice architectures where:
- Services are stateless or state is properly isolated
- Failure recovery uses sensible defaults (circuit breaker patterns)
- Each service type has distinct failure handling requirements

The GFR approach provides **genuine complexity reduction**.

### 6.3 Limitations

This approach does **not** help when:
- Failures cascade across service boundaries
- Recovery requires context-specific logic
- The same failure type needs different handling in different contexts
- The system has inherent combinatorial state space

---

## References

1. "Recovery-Preserving Kleisli Semantics for World-Computer Virtual Machines" - FR Monad paper
2. Graded Monads and effect systems literature
3. Circuit breaker and bulkhead patterns in distributed systems
