import Lax733996.Counting

/-!
---
title: Correctness of the count sequence
type: lemma
---
The initial layer consists of the source. Inductive counting certifies
exactly the successive layer sizes, including the final size after $N$ steps.
-/

namespace Lax733996.CountingTrace

open Lax733996.Reachability Counting

axiom correct {N : ℕ} (G : Graph N) (a : Fin N) (counts : ℕ → ℕ) :
  CountTrace G a counts ↔ ∀ k ≤ N, counts k = (layer G a k).card

end Lax733996.CountingTrace
