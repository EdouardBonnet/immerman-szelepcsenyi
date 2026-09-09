import Lax733996.ConfigurationCounting
import Lax434930.SpaceBounds

/-!
---
title: Logarithmic space for inductive counting
type: lemma
---
For a machine using logarithmic space, a nondeterministic machine implements
its configuration counting predicate in logarithmic space. Vertices and
bounded paths are generated sequentially. Every branch halts.
-/

namespace Lax733996.CountMachine

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930.SpaceBounds
open ConfigurationCounting

axiom implement (M : Machine) (c : ℕ) (hc : 0 < c)
    (hM : ∀ w, M.UsesSpace w (c * logSpace w.length)) :
  ∃ (d : ℕ) (D : Machine), 0 < d ∧
    (∀ w, D.HaltsOn w ∧ (D.Accepts w ↔ RejectsByCounting M w (c * logSpace w.length))) ∧
    ∀ w, D.UsesSpace w (d * logSpace w.length)

end Lax733996.CountMachine
