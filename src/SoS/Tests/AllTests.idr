||| Test module demonstrating linear test complexity
|||
||| Key claim: For N services, test count is O(N) not O(2^N)
|||
||| With idris2-coverage:
||| - Only reachable branches are coverage targets
||| - Unreachable paths (eliminated by dependent types) don't inflate coverage requirements
module SoS.Tests.AllTests

import SoS.GFR
import SoS.Services
import SoS.Composition

%default total

-- =============================================================================
-- Test infrastructure
-- =============================================================================

record TestResult where
  constructor MkTestResult
  name   : String
  passed : Bool
  detail : String

Show TestResult where
  show t = (if t.passed then "[PASS]" else "[FAIL]") ++ " " ++ t.name ++ ": " ++ t.detail

assertRight : String -> Either e a -> TestResult
assertRight name (Right _) = MkTestResult name True "got Right"
assertRight name (Left _)  = MkTestResult name False "expected Right, got Left"

assertLeft : String -> Either e a -> TestResult
assertLeft name (Left _)  = MkTestResult name True "got Left"
assertLeft name (Right _) = MkTestResult name False "expected Left, got Right"

-- =============================================================================
-- Handler tests (O(N) tests for N obligation types)
-- =============================================================================

-- Test 1: Network handler recovers network failures
testNetworkHandler : TestResult
testNetworkHandler =
  let input : GFR [NetworkObl] String
      input = GFail (MkFail NetworkFail "timeout") emptyEvidence
      result : GFR [] String
      result = handleNetwork (\(_, e) => GOk "recovered" e) input
  in case result of
       GOk _ _ => MkTestResult "network handler recovers" True "recovered"
       GFail _ _ => MkTestResult "network handler" False "should have recovered"

-- Test 2: Network handler passes through non-network failures
testNonNetworkPassthrough : TestResult
testNonNetworkPassthrough =
  let input : GFR [NetworkObl] String
      input = GFail (MkFail AuthFail "wrong type") emptyEvidence
      result : GFR [] String
      result = handleNetwork (\(_, e) => GOk "recovered" e) input
  in case result of
       GOk _ _ => MkTestResult "non-network passthrough" False "should have failed"
       GFail f _ => MkTestResult "non-network passes through" True (show f.category)

-- Test 3: Success passes through handler unchanged
testSuccessPassthrough : TestResult
testSuccessPassthrough =
  let input : GFR [NetworkObl] String
      input = GOk "original" emptyEvidence
      result : GFR [] String
      result = handleNetwork (\(_, e) => GOk "recovered" e) input
  in case result of
       GOk v _ => MkTestResult "success passthrough" True v
       GFail _ _ => MkTestResult "success passthrough" False "should have succeeded"

-- =============================================================================
-- Integration tests (happy path + key scenarios)
-- =============================================================================

testHappyPath : TestResult
testHappyPath =
  assertRight "happy path" (runGFR (safePlaceOrder "admin" "secret" 42 2))

testAuthFallback : TestResult
testAuthFallback =
  -- Invalid credentials -> handled, returns default
  assertRight "auth fallback" (runGFR (safePlaceOrder "wrong" "wrong" 42 2))

testNetworkError : TestResult
testNetworkError =
  -- Empty username triggers network error -> handled
  assertRight "network error handled" (runGFR (safePlaceOrder "" "" 42 2))

testProductNotFound : TestResult
testProductNotFound =
  -- Product ID > 100 -> service fail -> handled
  assertRight "product not found handled" (runGFR (safePlaceOrder "admin" "secret" 999 2))

-- =============================================================================
-- Coverage analysis
--
-- Traditional approach for 4 services:
--   Each service: success/fail = 2 outcomes
--   Total combinations: 2^4 = 16 test cases
--
-- GFR approach:
--   Handler tests: 3 (network handler behavior)
--   Integration tests: 4 (key scenarios)
--   Total: 7 tests
--
-- Growth: O(N) vs O(2^N)
-- =============================================================================

||| All tests
export
allTests : List TestResult
allTests =
  [ testNetworkHandler        -- Handler test 1
  , testNonNetworkPassthrough -- Handler test 2
  , testSuccessPassthrough    -- Handler test 3
  , testHappyPath             -- Integration 1
  , testAuthFallback          -- Integration 2
  , testNetworkError          -- Integration 3
  , testProductNotFound       -- Integration 4
  ]
  -- Total: 7 tests for 4-service composition
  -- Traditional: would need 16+ tests

||| Run all tests - required by idris2-cov
export
runAllTests : IO ()
runAllTests = do
  putStrLn "=== SoS Test Suite ==="
  putStrLn ""
  traverse_ (putStrLn . show) allTests
  putStrLn ""
  putStrLn $ "Results: " ++ show (length (filter (.passed) allTests)) ++ "/" ++ show (length allTests) ++ " passed"
  putStrLn ""
  putStrLn "=== Coverage Analysis ==="
  putStrLn "Services composed: 4"
  putStrLn "Traditional test cases needed: 2^4 = 16"
  putStrLn "GFR test cases written: 7"
  putStrLn "Reduction: 56%"
