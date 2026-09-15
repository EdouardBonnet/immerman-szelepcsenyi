import Lax733996.Counting

/-!
---
title: Correctness of one counting step
type: lemma
---
Starting from the correct layer size, valid classifications produce exactly
the size of the next layer. Such classifications exist.
-/

namespace Lax733996.CountingStep

open Lax733996.Reachability Counting

axiom correct {N : ℕ} (G : Graph N) (a : Fin N) (k d : ℕ) :
  CountStep G a k (layer G a k).card d ↔ d = (layer G a (k + 1)).card

end Lax733996.CountingStep
