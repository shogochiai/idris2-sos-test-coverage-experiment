||| Simplified GFR (Graded Failure-Recovery) Monad for SoS experiment
||| Based on idris2-cdk's FRMonad.Graded
module SoS.GFR

import Data.List

%default total

-- =============================================================================
-- Failure types
-- =============================================================================

public export
data FailCategory = NetworkFail | AuthFail | ValidationFail | ServiceFail

public export
Eq FailCategory where
  NetworkFail == NetworkFail = True
  AuthFail == AuthFail = True
  ValidationFail == ValidationFail = True
  ServiceFail == ServiceFail = True
  _ == _ = False

public export
Show FailCategory where
  show NetworkFail = "Network"
  show AuthFail = "Auth"
  show ValidationFail = "Validation"
  show ServiceFail = "Service"

public export
record Fail where
  constructor MkFail
  category : FailCategory
  message  : String

public export
Show Fail where
  show f = show f.category ++ ": " ++ f.message

public export
isRetryable : Fail -> Bool
isRetryable f = f.category == NetworkFail

-- =============================================================================
-- Evidence (simplified)
-- =============================================================================

public export
record Evidence where
  constructor MkEvidence
  entries : List String

public export
emptyEvidence : Evidence
emptyEvidence = MkEvidence []

public export
addEntry : String -> Evidence -> Evidence
addEntry s (MkEvidence es) = MkEvidence (s :: es)

public export
combineEvidence : Evidence -> Evidence -> Evidence
combineEvidence (MkEvidence e1) (MkEvidence e2) = MkEvidence (e1 ++ e2)

-- =============================================================================
-- Obligations
-- =============================================================================

public export
data Obligation = NetworkObl | AuthObl | ValidationObl | ServiceObl

public export
Eq Obligation where
  NetworkObl == NetworkObl = True
  AuthObl == AuthObl = True
  ValidationObl == ValidationObl = True
  ServiceObl == ServiceObl = True
  _ == _ = False

public export
Obligations : Type
Obligations = List Obligation

-- =============================================================================
-- GFR Monad
-- =============================================================================

public export
data GFR : Obligations -> Type -> Type where
  GOk   : a -> Evidence -> GFR obs a
  GFail : Fail -> Evidence -> GFR obs a

public export
Show a => Show (GFR obs a) where
  show (GOk v e) = "GOk(" ++ show v ++ ") [" ++ show (length e.entries) ++ " entries]"
  show (GFail f e) = "GFail(" ++ show f ++ ") [" ++ show (length e.entries) ++ " entries]"

public export
gpure : a -> GFR [] a
gpure v = GOk v emptyEvidence

public export
gbind : GFR obs a -> (a -> GFR obs b) -> GFR obs b
gbind (GOk v e1) f = case f v of
  GOk v' e2  => GOk v' (combineEvidence e1 e2)
  GFail x e2 => GFail x (combineEvidence e1 e2)
gbind (GFail x e) _ = GFail x e

public export
(>>=) : GFR obs a -> (a -> GFR obs b) -> GFR obs b
(>>=) = gbind

-- =============================================================================
-- Obligation handlers
-- =============================================================================

public export
handleNetwork : ((Fail, Evidence) -> GFR obs a) -> GFR (NetworkObl :: obs) a -> GFR obs a
handleNetwork _ (GOk v e) = GOk v e
handleNetwork h (GFail f e) =
  if f.category == NetworkFail then h (f, e) else GFail f e

public export
handleAuth : ((Fail, Evidence) -> GFR obs a) -> GFR (AuthObl :: obs) a -> GFR obs a
handleAuth _ (GOk v e) = GOk v e
handleAuth h (GFail f e) =
  if f.category == AuthFail then h (f, e) else GFail f e

public export
handleService : ((Fail, Evidence) -> GFR obs a) -> GFR (ServiceObl :: obs) a -> GFR obs a
handleService _ (GOk v e) = GOk v e
handleService h (GFail f e) =
  if f.category == ServiceFail then h (f, e) else GFail f e

||| Catch-all handler for any remaining failures (simplifies demo)
public export
handleAll : ((Fail, Evidence) -> GFR obs a) -> GFR obs a -> GFR obs a
handleAll _ (GOk v e) = GOk v e
handleAll h (GFail f e) = h (f, e)

-- =============================================================================
-- Weaken (add obligations)
-- =============================================================================

public export
weaken : GFR obs a -> GFR (o :: obs) a
weaken (GOk v e) = GOk v e
weaken (GFail f e) = GFail f e

-- =============================================================================
-- Run (only when all obligations discharged)
-- =============================================================================

public export
runGFR : GFR [] a -> Either (Fail, Evidence) (a, Evidence)
runGFR (GOk v e) = Right (v, e)
runGFR (GFail f e) = Left (f, e)

-- =============================================================================
-- Retry with evidence
-- =============================================================================

gretryLoop : Nat -> GFR obs a -> Evidence -> GFR obs a
gretryLoop Z comp acc = case comp of
  GOk v e => GOk v (combineEvidence acc e)
  GFail f e => GFail f (combineEvidence acc e)
gretryLoop (S n) comp acc = case comp of
  GOk v e => GOk v (combineEvidence acc e)
  GFail f e =>
    if isRetryable f
      then gretryLoop n comp (addEntry ("retry: " ++ show f) (combineEvidence acc e))
      else GFail f (combineEvidence acc e)

public export
gretry : Nat -> GFR obs a -> GFR obs a
gretry n comp = gretryLoop n comp emptyEvidence
