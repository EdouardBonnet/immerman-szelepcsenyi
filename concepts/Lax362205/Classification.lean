import Lax362205.Counting

/-!
---
title: Correctness of vertex classification
type: lemma
---
With the correct current count, a vertex has a valid positive or negative
classification exactly according to its membership in the next layer.
-/

namespace Lax362205.Classification

open Lax362205.Reachability Counting

axiom correct {N : ℕ} (G : Graph N) (a v : Fin N) (k : ℕ) (b : Bool) :
  Classify G a k (layer G a k).card v b ↔
    (b = true ↔ v ∈ layer G a (k + 1))

end Lax362205.Classification
