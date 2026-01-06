# System of Systems Test Coverage Experiment

**Claim**: Under specific axioms, GFR Monad + Dependent Types reduce test complexity from O(2^N) to O(N).

> **Important**: This claim has a precise validity domain. See [FORMAL_SPEC.md](FORMAL_SPEC.md) for axioms, proofs, and counterexamples.

## TL;DR

| Metric | Traditional | GFR Approach |
|--------|-------------|--------------|
| Test cases (N=4) | 16 | 7 |
| Complexity | O(2^N) | O(N × K) |
| Validity | Always | Under Axioms 1-5 |

## Definitions

Before the claim makes sense, we must fix terminology:

- **N** = Number of services in composition (this experiment: N=4)
- **K** = Maximum failure categories per service (this experiment: K=1)
- **Traditional testing** = Enumerating all success/failure combinations at integration level
- **GFR testing** = Handler unit tests + integration path tests

## The Claim (Formal)

**Proposition**: Under Axioms 1-5 (see [FORMAL_SPEC.md](FORMAL_SPEC.md)), for N services with at most K obligations each:

```
T_gfr(N, K) = O(N × K)
```

When K is constant, this simplifies to **O(N)**.

### Required Axioms

1. **Independence**: Services fail independently (no correlated failures)
2. **Handler Completeness**: Each handler fully addresses its failure category
3. **Compositional Recovery**: Recovery produces valid continuation values
4. **Obligation Disjointness**: No two services share identical failure handling requirements
5. **Bounded Failure Modes**: Each service has ≤ K failure categories

**If any axiom is violated, complexity may revert to O(2^N).** See [FORMAL_SPEC.md § Counterexamples](FORMAL_SPEC.md#4-counterexamples-boundary-conditions).

## Experimental Evidence

### Baseline: Traditional O(2^N) Tests

See [`src/SoS/Tests/Baseline/TraditionalTests.idr`](src/SoS/Tests/Baseline/TraditionalTests.idr):

```
16 test cases covering all (Auth × Product × Order × Notify) combinations:
SSSS, SSSF, SSFS, SSFF, SFSS, SFSF, SFFS, SFFF,
FSSS, FSSF, FSFS, FSFF, FFSS, FFSF, FFFS, FFFF
```

### GFR: O(N) Tests

See [`src/SoS/Tests/AllTests.idr`](src/SoS/Tests/AllTests.idr):

```
7 test cases:
- 3 handler behavior tests (unit level)
- 4 integration path tests (happy + key failure scenarios)
```

### Measurement

```bash
$ idris2-cov .
Runtime Coverage:     51/42 (121%)
Canonical branches:   50
Bugs (UnhandledInput): 0
```

> **Note on 121%**: Numerator (Chez profiler BranchPoints) and denominator (dumpcases canonical cases) measure different granularities. This is a tooling artifact, not a flaw in the complexity argument.

## Validity Domain

This experiment satisfies all 5 axioms:

| Axiom | How Satisfied |
|-------|---------------|
| Independence | Services are pure functions with no shared state |
| Handler Completeness | `handleAll` catches all remaining failures |
| Compositional Recovery | Default values (`MkOrderResult 0 0`) are valid |
| Obligation Disjointness | Single `NetworkObl` type |
| Bounded Failure Modes | K=1 (only NetworkFail actively handled) |

### When This Approach Fails

The complexity reverts to O(2^N) when:

- **Cascading failures**: Service A's failure changes Service B's failure mode
- **Context-dependent recovery**: Different services need different handling for same failure type
- **Partial handlers**: Handler catches some but not all failures of its category
- **State dependencies**: Recovery value causes downstream validation failures

## Running the Experiment

```bash
# Build
pack build sos-experiment.ipkg

# Run GFR demo
./build/exec/sos-demo

# Run coverage analysis
idris2-cov .
```

## Project Structure

```
├── FORMAL_SPEC.md                    # Axioms, propositions, counterexamples
├── README.md                         # This file
├── sos-experiment.ipkg
└── src/SoS/
    ├── GFR.idr                       # Simplified GFR Monad
    ├── Services.idr                  # Mock services
    ├── Composition.idr               # 4-service workflow
    ├── Main.idr                      # CLI demo
    └── Tests/
        ├── AllTests.idr              # GFR tests (7 cases)
        └── Baseline/
            └── TraditionalTests.idr  # Traditional tests (16 cases)
```

## How It Works

### GFR Monad

```idris
data GFR : Obligations -> Type -> Type where
  GOk   : a -> Evidence -> GFR obs a
  GFail : Fail -> Evidence -> GFR obs a
```

- Type parameter `Obligations` tracks unhandled failure categories
- Handlers transform `GFR (φ :: obs) a → GFR obs a`
- `runGFR : GFR [] a → Either ...` requires all obligations discharged

### Why Fewer Tests Suffice

Traditional testing must cover all 2^N combinations because failures are opaque at runtime.

GFR makes failures **transparent at the type level**:
1. Compiler verifies all obligations are handled
2. Each handler is tested once (unit level)
3. Integration tests verify composition, not combinations

The type system provides the "glue" that traditional testing must cover manually.

## Related Work

- [FR Monad Paper](https://example.com) - "Recovery-Preserving Kleisli Semantics for World-Computer Virtual Machines"
- [idris2-coverage](https://github.com/shogochiai/idris2-coverage) - Proof-aware coverage tool
- [idris2-cdk](https://github.com/AdrianLxM/idris2-cdk) - Full GFR implementation for ICP/EVM

## Conclusion

The claim **"O(2^N) → O(N)"** is:

- ✅ **Valid** under the 5 axioms (independence, completeness, recovery, disjointness, boundedness)
- ❌ **Invalid** when services have correlated failures, context-dependent recovery, or shared obligations

This repository provides:
1. Formal specification of validity domain ([FORMAL_SPEC.md](FORMAL_SPEC.md))
2. Baseline comparison (16 traditional tests vs 7 GFR tests)
3. Reproducible measurement via `idris2-cov`

The value is not "magic complexity reduction" but **making the required assumptions explicit** and **leveraging the type system to enforce them**.
