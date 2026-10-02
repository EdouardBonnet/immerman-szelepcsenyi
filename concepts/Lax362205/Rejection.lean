import Lax362205.ConfigurationCounting

/-!
---
title: Correctness of rejection by counting
type: lemma
---
On a space-bounded computation, counting certifies rejection precisely when
there is no accepting computation.
-/

namespace Lax362205.Rejection

open Lax434930.PolynomialTime Lax434930.SpaceMachines ConfigurationCounting

axiom correct (M : Machine) (w : Word) (s : ℕ) (hs : M.UsesSpace w s) :
  RejectsByCounting M w s ↔ ¬ M.Accepts w

end Lax362205.Rejection
