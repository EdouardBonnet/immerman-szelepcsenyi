import Lax733996.ConfigurationGraph
import Lax733996.Counting

/-!
---
title: Counting on the configuration graph
type: definition
---
For every terminal accepting configuration, certify that it cannot be
reached from the initial configuration. The implementation must generate
the witnesses sequentially; this predicate alone makes no space claim.
-/

namespace Lax733996.ConfigurationCounting

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax733996.BoundedConfigurations Lax733996.ConfigurationGraph Counting

def RejectsByCounting (M : Machine) (w : Word) (s : ℕ) : Prop :=
  ∀ a b : Config M w.length s, expand a = M.initial →
    M.Terminal w (expand b) → M.accept b.state = true →
    NonreachCertificate (graph M w s) (numbering M w.length s a) (numbering M w.length s b)

end Lax733996.ConfigurationCounting
