||| System of Systems composition
|||
||| Key insight: When composing N services, traditional testing requires O(2^N) test cases
||| (each service can succeed or fail). With GFR + dependent types:
||| - Unreachable paths are eliminated at compile time
||| - Only reachable failure modes need testing
||| - Test complexity grows linearly with handled obligations
module SoS.Composition

import SoS.GFR
import SoS.Services

%default total

-- =============================================================================
-- Simple composition using same obligation type
-- This avoids the weaken complexity for the demo
-- =============================================================================

||| Unified obligation type for simplicity
public export
Obs : Obligations
Obs = [NetworkObl]

||| Lift auth service to unified obligations
authServiceU : String -> String -> GFR Obs User
authServiceU username password =
  if username == "admin" && password == "secret"
    then GOk (MkUser 1 "admin") (MkEvidence ["auth: success"])
    else if username == ""
      then GFail (MkFail NetworkFail "connection timeout") (MkEvidence ["auth: network error"])
      else GFail (MkFail AuthFail "invalid credentials") (MkEvidence ["auth: auth failed"])

||| Lift product service to unified obligations
productServiceU : Nat -> GFR Obs Product
productServiceU productId =
  if productId == 0
    then GFail (MkFail NetworkFail "service unavailable") (MkEvidence ["product: network error"])
    else if productId > 100
      then GFail (MkFail ServiceFail "product not found") (MkEvidence ["product: not found"])
      else GOk (MkProduct productId ("Product-" ++ show productId) (productId * 10))
               (MkEvidence ["product: found"])

||| Lift order service to unified obligations
orderServiceU : Order -> GFR Obs OrderResult
orderServiceU order =
  if order.quantity == 0
    then GFail (MkFail ValidationFail "quantity must be > 0") (MkEvidence ["order: validation error"])
    else if order.productId == 0
      then GFail (MkFail NetworkFail "order service down") (MkEvidence ["order: network error"])
      else GOk (MkOrderResult (order.userId * 1000 + order.productId) (order.quantity * 10))
               (MkEvidence ["order: created"])

||| Lift notification service to unified obligations
notifyServiceU : Nat -> String -> GFR Obs ()
notifyServiceU userId msg =
  if userId == 0
    then GFail (MkFail NetworkFail "notification service timeout") (MkEvidence ["notify: timeout"])
    else GOk () (MkEvidence ["notify: sent to user " ++ show userId])

-- =============================================================================
-- Composition: Full order workflow (4 services)
-- Auth -> Product -> Order -> Notify
--
-- Traditional testing: 2^4 = 16 test cases (each service success/fail)
-- GFR approach: Test per handler + happy path = O(N) cases
-- =============================================================================

||| Complete order workflow
||| All 4 services composed with single obligation type
public export
placeOrder : String -> String -> Nat -> Nat -> GFR Obs OrderResult
placeOrder username password productId quantity =
  authServiceU username password >>= \user =>
  productServiceU productId >>= \product =>
  orderServiceU (MkOrder user.id productId quantity) >>= \result =>
  notifyServiceU user.id ("Order " ++ show result.orderId ++ " placed") >>= \_ =>
  GOk result emptyEvidence

-- =============================================================================
-- Handlers
-- =============================================================================

||| Default values for fallback
defaultUser : User
defaultUser = MkUser 0 "guest"

defaultProduct : Product
defaultProduct = MkProduct 0 "unavailable" 0

defaultResult : OrderResult
defaultResult = MkOrderResult 0 0

||| Network handler with retry info
retryOnNetwork : (Fail, Evidence) -> GFR obs a
retryOnNetwork (f, e) = GFail f (addEntry "network: giving up after retry" e)

||| Recovery handler that provides defaults
recoverWithDefault : a -> (Fail, Evidence) -> GFR obs a
recoverWithDefault val (_, e) = GOk val (addEntry "recovered with default" e)

-- =============================================================================
-- Safe composition: All obligations handled
-- =============================================================================

||| Safe order placement with all failures handled
public export
safePlaceOrder : String -> String -> Nat -> Nat -> GFR [] OrderResult
safePlaceOrder username password productId quantity =
  handleAll (recoverWithDefault defaultResult) $
  handleNetwork (recoverWithDefault defaultResult) $
  placeOrder username password productId quantity

||| Safe with retry
public export
safePlaceOrderWithRetry : String -> String -> Nat -> Nat -> GFR [] OrderResult
safePlaceOrderWithRetry username password productId quantity =
  handleNetwork (recoverWithDefault defaultResult) $
  gretry 3 (placeOrder username password productId quantity)

-- =============================================================================
-- Key observation for test coverage:
--
-- placeOrder has 4 services, each with ~2 failure modes = 8 potential failures
-- Traditional: Need to test 2^8 = 256 combinations
--
-- GFR approach:
-- 1. Type guarantees composition is valid (compile-time)
-- 2. Each handler is tested independently (~4 tests)
-- 3. Unreachable combinations eliminated by type system
-- 4. Total tests needed: O(number of handlers) = O(N), not O(2^N)
-- =============================================================================

||| Execute and show result
public export
executeOrder : String -> String -> Nat -> Nat -> String
executeOrder u p prod qty =
  case runGFR (safePlaceOrder u p prod qty) of
    Right (result, ev) => "Success: " ++ show result ++
                          "\nEvidence: " ++ show (length ev.entries) ++ " entries"
    Left (fail, ev) => "Failed: " ++ show fail ++
                       "\nEvidence: " ++ show (length ev.entries) ++ " entries"
