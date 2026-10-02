import Lax362205.Counting

/-!
---
title: Correctness of the count sequence
type: lemma
---
The initial layer consists of the source. Inductive counting certifies
exactly the successive layer sizes, including the final size after $N$ steps.
-/

namespace Lax362205.CountingTrace

open Lax362205.Reachability Counting

axiom correct {N : ℕ} (G : Graph N) (a : Fin N) (counts : ℕ → ℕ) :
  CountTrace G a counts ↔ ∀ k ≤ N, counts k = (layer G a k).card

end Lax362205.CountingTrace
