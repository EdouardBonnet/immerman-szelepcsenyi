import Lax733996.ConfigurationCounting
import Lax434930.SpaceBounds

/-!
---
title: Logarithmic space for inductive counting
type: lemma
---
A nondeterministic machine implements the configuration counting predicate
in logarithmic space. It enumerates vertices in order, guesses bounded paths,
and retains only a fixed number of vertices and counters. Every branch
halts. This machine construction is an open proof obligation.
-/

namespace Lax733996.CountMachine

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930.SpaceBounds
open ConfigurationCounting

axiom implement (M : Machine) (c : ℕ) (hc : 0 < c) :
  ∃ (d : ℕ) (D : Machine), 0 < d ∧
    (∀ w, D.HaltsOn w ∧ (D.Accepts w ↔ RejectsByCounting M w (c * logSpace w.length))) ∧
    ∀ w, D.UsesSpace w (d * logSpace w.length)

end Lax733996.CountMachine
