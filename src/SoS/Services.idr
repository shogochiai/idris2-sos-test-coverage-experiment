||| Mock external services for SoS experiment
||| Each service returns GFR with appropriate obligations
module SoS.Services

import SoS.GFR

%default total

-- =============================================================================
-- Domain types
-- =============================================================================

public export
record User where
  constructor MkUser
  id   : Nat
  name : String

public export
Show User where
  show u = "User(" ++ show u.id ++ ", " ++ u.name ++ ")"

public export
record Product where
  constructor MkProduct
  id    : Nat
  name  : String
  price : Nat

public export
Show Product where
  show p = "Product(" ++ show p.id ++ ", " ++ p.name ++ ", $" ++ show p.price ++ ")"

public export
record Order where
  constructor MkOrder
  userId    : Nat
  productId : Nat
  quantity  : Nat

public export
Show Order where
  show o = "Order(user=" ++ show o.userId ++ ", product=" ++ show o.productId ++ ", qty=" ++ show o.quantity ++ ")"

public export
record OrderResult where
  constructor MkOrderResult
  orderId    : Nat
  totalPrice : Nat

public export
Show OrderResult where
  show r = "OrderResult(id=" ++ show r.orderId ++ ", total=$" ++ show r.totalPrice ++ ")"

-- =============================================================================
-- Service A: Auth Service (external)
-- Obligation: NetworkObl, AuthObl
-- =============================================================================

||| Authenticate user - may fail with network or auth errors
public export
authService : String -> String -> GFR [NetworkObl, AuthObl] User
authService username password =
  if username == "admin" && password == "secret"
    then GOk (MkUser 1 "admin") (MkEvidence ["auth: success"])
    else if username == ""
      then GFail (MkFail NetworkFail "connection timeout") (MkEvidence ["auth: network error"])
      else GFail (MkFail AuthFail "invalid credentials") (MkEvidence ["auth: auth failed"])

-- =============================================================================
-- Service B: Product Service (external)
-- Obligation: NetworkObl, ServiceObl
-- =============================================================================

||| Get product info - may fail with network or service errors
public export
productService : Nat -> GFR [NetworkObl, ServiceObl] Product
productService productId =
  if productId == 0
    then GFail (MkFail NetworkFail "service unavailable") (MkEvidence ["product: network error"])
    else if productId > 100
      then GFail (MkFail ServiceFail "product not found") (MkEvidence ["product: not found"])
      else GOk (MkProduct productId ("Product-" ++ show productId) (productId * 10))
               (MkEvidence ["product: found"])

-- =============================================================================
-- Service C: Order Service (external)
-- Obligation: NetworkObl, ServiceObl
-- =============================================================================

||| Create order - may fail with network or service errors
public export
orderService : Order -> GFR [NetworkObl, ServiceObl] OrderResult
orderService order =
  if order.quantity == 0
    then GFail (MkFail ValidationFail "quantity must be > 0") (MkEvidence ["order: validation error"])
    else if order.productId == 0
      then GFail (MkFail NetworkFail "order service down") (MkEvidence ["order: network error"])
      else GOk (MkOrderResult (order.userId * 1000 + order.productId) (order.quantity * 10))
               (MkEvidence ["order: created"])

-- =============================================================================
-- Service D: Notification Service (external)
-- Obligation: NetworkObl
-- =============================================================================

||| Send notification - may fail with network errors
public export
notifyService : Nat -> String -> GFR [NetworkObl] ()
notifyService userId msg =
  if userId == 0
    then GFail (MkFail NetworkFail "notification service timeout") (MkEvidence ["notify: timeout"])
    else GOk () (MkEvidence ["notify: sent to user " ++ show userId])
