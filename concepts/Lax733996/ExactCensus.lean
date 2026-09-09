import Lax733996.Counting

/-!
---
title: Exact censuses enumerate the whole layer
type: lemma
---
A census of reachable vertices with the correct cardinality contains every
vertex of the layer. Distinctness is enforced by the finite-set representation.
-/

namespace Lax733996.ExactCensus

open Lax307052.Reachability Counting

axiom complete {N : ℕ} (G : Graph N) (a : Fin N) (k : ℕ) (S : Finset (Fin N)) :
  Census G a k (layer G a k).card S → S = layer G a k

end Lax733996.ExactCensus
