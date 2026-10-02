import Lax362205.Counting

/-!
---
title: Exact censuses enumerate the whole layer
type: lemma
---
A census of reachable vertices with the correct cardinality contains every
vertex of the layer. Distinctness is enforced by the finite-set representation.
-/

namespace Lax362205.ExactCensus

open Lax362205.Reachability Counting

axiom complete {N : ℕ} (G : Graph N) (a : Fin N) (k : ℕ) (S : Finset (Fin N)) :
  Census G a k (layer G a k).card S → S = layer G a k

end Lax362205.ExactCensus
