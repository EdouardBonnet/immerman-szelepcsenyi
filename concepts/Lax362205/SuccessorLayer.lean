import Lax362205.Counting

/-!
---
title: The next reachable layer
type: lemma
---
A vertex belongs to the next layer precisely when it is the source or has
an incoming edge from the current layer.
-/

namespace Lax362205.SuccessorLayer

open Lax362205.Reachability Counting

axiom successor {N : ℕ} (G : Graph N) (a v : Fin N) (k : ℕ) :
  v ∈ layer G a (k + 1) ↔ v = a ∨ ∃ u ∈ layer G a k, G u v = true

end Lax362205.SuccessorLayer
