||| Traditional Testing Baseline
|||
||| This module demonstrates the O(2^N) test complexity of traditional integration testing.
||| For 4 services, we need 2^4 = 16 test cases to cover all success/failure combinations.
|||
||| Compare with GFR approach in AllTests.idr which achieves the same coverage with 7 tests.
module SoS.Tests.Baseline.TraditionalTests

import SoS.GFR
import SoS.Services
import SoS.Composition

%default total

-- =============================================================================
-- Test Infrastructure
-- =============================================================================

record TestResult where
  constructor MkTestResult
  name   : String
  passed : Bool
  detail : String

Show TestResult where
  show t = (if t.passed then "[PASS]" else "[FAIL]") ++ " " ++ t.name

-- =============================================================================
-- Service Simulators with Controllable Failure
--
-- To test all combinations, we need to control each service's success/failure.
-- =============================================================================

||| Auth service with controllable outcome
authSim : Bool -> String -> String -> GFR [NetworkObl] User
authSim True _ _ = GOk (MkUser 1 "admin") (MkEvidence ["auth: success"])
authSim False _ _ = GFail (MkFail NetworkFail "auth failed") (MkEvidence ["auth: fail"])

||| Product service with controllable outcome
productSim : Bool -> Nat -> GFR [NetworkObl] Product
productSim True pid = GOk (MkProduct pid "Product" 100) (MkEvidence ["product: success"])
productSim False _ = GFail (MkFail NetworkFail "product failed") (MkEvidence ["product: fail"])

||| Order service with controllable outcome
orderSim : Bool -> Order -> GFR [NetworkObl] OrderResult
orderSim True o = GOk (MkOrderResult 1 100) (MkEvidence ["order: success"])
orderSim False _ = GFail (MkFail NetworkFail "order failed") (MkEvidence ["order: fail"])

||| Notify service with controllable outcome
notifySim : Bool -> Nat -> String -> GFR [NetworkObl] ()
notifySim True _ _ = GOk () (MkEvidence ["notify: success"])
notifySim False _ _ = GFail (MkFail NetworkFail "notify failed") (MkEvidence ["notify: fail"])

||| Compose 4 services with controllable outcomes
||| Parameters: (authOk, productOk, orderOk, notifyOk)
compose4 : (Bool, Bool, Bool, Bool) -> GFR [NetworkObl] OrderResult
compose4 (a, p, o, n) =
  authSim a "" "" >>= \user =>
  productSim p 1 >>= \product =>
  orderSim o (MkOrder user.id product.id 1) >>= \result =>
  notifySim n user.id "done" >>= \_ =>
  GOk result emptyEvidence

||| Run with all handlers applied
runCompose4 : (Bool, Bool, Bool, Bool) -> Either (Fail, Evidence) (OrderResult, Evidence)
runCompose4 cfg =
  runGFR $ handleAll (\(_, e) => GOk (MkOrderResult 0 0) e) $
           handleNetwork (\(_, e) => GOk (MkOrderResult 0 0) e) $
           compose4 cfg

-- =============================================================================
-- All 16 Combinations (2^4)
--
-- Encoding: (Auth, Product, Order, Notify) where True=Success, False=Fail
--
-- This is the essence of O(2^N): we must enumerate all combinations.
-- =============================================================================

||| Test case 0: SSSS (all succeed)
test0000 : TestResult
test0000 = case runCompose4 (True, True, True, True) of
  Right _ => MkTestResult "SSSS: all succeed" True "ok"
  Left _ => MkTestResult "SSSS" False "unexpected fail"

||| Test case 1: SSSF (notify fails)
test0001 : TestResult
test0001 = case runCompose4 (True, True, True, False) of
  Right _ => MkTestResult "SSSF: notify fails, recovered" True "ok"
  Left _ => MkTestResult "SSSF" False "should recover"

||| Test case 2: SSFS (order fails)
test0010 : TestResult
test0010 = case runCompose4 (True, True, False, True) of
  Right _ => MkTestResult "SSFS: order fails, recovered" True "ok"
  Left _ => MkTestResult "SSFS" False "should recover"

||| Test case 3: SSFF (order+notify fail)
test0011 : TestResult
test0011 = case runCompose4 (True, True, False, False) of
  Right _ => MkTestResult "SSFF: order+notify fail, recovered" True "ok"
  Left _ => MkTestResult "SSFF" False "should recover"

||| Test case 4: SFSS (product fails)
test0100 : TestResult
test0100 = case runCompose4 (True, False, True, True) of
  Right _ => MkTestResult "SFSS: product fails, recovered" True "ok"
  Left _ => MkTestResult "SFSS" False "should recover"

||| Test case 5: SFSF (product+notify fail)
test0101 : TestResult
test0101 = case runCompose4 (True, False, True, False) of
  Right _ => MkTestResult "SFSF: product+notify fail, recovered" True "ok"
  Left _ => MkTestResult "SFSF" False "should recover"

||| Test case 6: SFFS (product+order fail)
test0110 : TestResult
test0110 = case runCompose4 (True, False, False, True) of
  Right _ => MkTestResult "SFFS: product+order fail, recovered" True "ok"
  Left _ => MkTestResult "SFFS" False "should recover"

||| Test case 7: SFFF (product+order+notify fail)
test0111 : TestResult
test0111 = case runCompose4 (True, False, False, False) of
  Right _ => MkTestResult "SFFF: product+order+notify fail, recovered" True "ok"
  Left _ => MkTestResult "SFFF" False "should recover"

||| Test case 8: FSSS (auth fails)
test1000 : TestResult
test1000 = case runCompose4 (False, True, True, True) of
  Right _ => MkTestResult "FSSS: auth fails, recovered" True "ok"
  Left _ => MkTestResult "FSSS" False "should recover"

||| Test case 9: FSSF (auth+notify fail)
test1001 : TestResult
test1001 = case runCompose4 (False, True, True, False) of
  Right _ => MkTestResult "FSSF: auth+notify fail, recovered" True "ok"
  Left _ => MkTestResult "FSSF" False "should recover"

||| Test case 10: FSFS (auth+order fail)
test1010 : TestResult
test1010 = case runCompose4 (False, True, False, True) of
  Right _ => MkTestResult "FSFS: auth+order fail, recovered" True "ok"
  Left _ => MkTestResult "FSFS" False "should recover"

||| Test case 11: FSFF (auth+order+notify fail)
test1011 : TestResult
test1011 = case runCompose4 (False, True, False, False) of
  Right _ => MkTestResult "FSFF: auth+order+notify fail, recovered" True "ok"
  Left _ => MkTestResult "FSFF" False "should recover"

||| Test case 12: FFSS (auth+product fail)
test1100 : TestResult
test1100 = case runCompose4 (False, False, True, True) of
  Right _ => MkTestResult "FFSS: auth+product fail, recovered" True "ok"
  Left _ => MkTestResult "FFSS" False "should recover"

||| Test case 13: FFSF (auth+product+notify fail)
test1101 : TestResult
test1101 = case runCompose4 (False, False, True, False) of
  Right _ => MkTestResult "FFSF: auth+product+notify fail, recovered" True "ok"
  Left _ => MkTestResult "FFSF" False "should recover"

||| Test case 14: FFFS (auth+product+order fail)
test1110 : TestResult
test1110 = case runCompose4 (False, False, False, True) of
  Right _ => MkTestResult "FFFS: auth+product+order fail, recovered" True "ok"
  Left _ => MkTestResult "FFFS" False "should recover"

||| Test case 15: FFFF (all fail)
test1111 : TestResult
test1111 = case runCompose4 (False, False, False, False) of
  Right _ => MkTestResult "FFFF: all fail, recovered" True "ok"
  Left _ => MkTestResult "FFFF" False "should recover"

-- =============================================================================
-- Summary
-- =============================================================================

||| All 16 traditional tests
export
allTraditionalTests : List TestResult
allTraditionalTests =
  [ test0000, test0001, test0010, test0011  -- 0-3
  , test0100, test0101, test0110, test0111  -- 4-7
  , test1000, test1001, test1010, test1011  -- 8-11
  , test1100, test1101, test1110, test1111  -- 12-15
  ]

||| Run all traditional tests
export
runTraditionalTests : IO ()
runTraditionalTests = do
  putStrLn "=== Traditional Test Suite (O(2^N) = 16 tests) ==="
  putStrLn ""
  traverse_ (putStrLn . show) allTraditionalTests
  putStrLn ""
  putStrLn $ "Results: " ++ show (length (filter (.passed) allTraditionalTests)) ++ "/" ++ show (length allTraditionalTests) ++ " passed"
  putStrLn ""
  putStrLn "=== Complexity Analysis ==="
  putStrLn "Services: 4"
  putStrLn "Test cases: 2^4 = 16"
  putStrLn "Each additional service DOUBLES test count"
  putStrLn ""
  putStrLn "Compare with GFR approach: 7 tests (see AllTests.idr)"
