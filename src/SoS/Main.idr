||| CLI demo for System of Systems experiment
module SoS.Main

import SoS.GFR
import SoS.Services
import SoS.Composition

%default total

||| Demo scenarios
demo : IO ()
demo = do
  putStrLn "=== System of Systems GFR Demo ==="
  putStrLn ""

  putStrLn "--- Scenario 1: Happy path ---"
  putStrLn $ executeOrder "admin" "secret" 42 2
  putStrLn ""

  putStrLn "--- Scenario 2: Auth failure (falls back to guest) ---"
  putStrLn $ executeOrder "unknown" "wrong" 42 2
  putStrLn ""

  putStrLn "--- Scenario 3: Network failure simulation ---"
  putStrLn $ executeOrder "" "" 42 2
  putStrLn ""

  putStrLn "--- Scenario 4: Product not found ---"
  putStrLn $ executeOrder "admin" "secret" 999 2
  putStrLn ""

  putStrLn "=== Key Insight ==="
  putStrLn "4 services composed, each with multiple failure modes"
  putStrLn "Traditional testing: O(2^N) = 16+ test cases"
  putStrLn "GFR approach: O(N) = 4 handler tests + happy path"
  putStrLn ""
  putStrLn "Type system eliminates unreachable combinations!"

main : IO ()
main = demo
