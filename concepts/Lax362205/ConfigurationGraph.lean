import Lax362205.BoundedConfigurations
import Lax362205.Reachability
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Log

set_option backward.isDefEq.respectTransparency false

/-!
---
title: The bounded configuration graph
type: definition
---
Vertices are configurations whose work tape has a fixed finite bound.
Edges are machine transitions. Acceptance is reachability from the initial
configuration to a terminal accepting configuration. The search predicate
replaces reachability by the recursive finite graph test.
-/

namespace Lax362205.ConfigurationGraph

open scoped Classical

open Lax434930.PolynomialTime Lax434930.SpaceMachines BoundedConfigurations Reachability

/-- Label all bounded configurations consecutively from zero. -/
noncomputable def numbering (M : Machine) (n s : ℕ) :
    Config M n s ≃ Fin (Fintype.card (Config M n s)) := Fintype.equivFin _

/-- Connect two numbered configurations exactly when the machine can move from the first to the second. -/
noncomputable def graph (M : Machine) (w : Word) (s : ℕ) :
    Graph (Fintype.card (Config M w.length s)) :=
  fun a b => decide (M.Step w (expand ((numbering M w.length s).symm a))
    (expand ((numbering M w.length s).symm b)))

/-- Some accepting terminal configuration is reachable from the initial configuration within the tape bound. -/
def AcceptsBounded (M : Machine) (w : Word) (s : ℕ) : Prop :=
  ∃ a b : Config M w.length s,
    expand a = M.initial ∧ M.Terminal w (expand b) ∧ M.accept b.state = true ∧
    Reachable (graph M w s) (numbering M w.length s a) (numbering M w.length s b)

/-- The finite reachability search finds a path from the initial configuration to an accepting terminal one. -/
def SearchAccepts (M : Machine) (w : Word) (s : ℕ) : Prop :=
  ∃ a b : Config M w.length s,
    expand a = M.initial ∧ M.Terminal w (expand b) ∧ M.accept b.state = true ∧
    search (graph M w s) (Nat.clog 2 (Fintype.card (Config M w.length s)))
      (numbering M w.length s a) (numbering M w.length s b) = true

end Lax362205.ConfigurationGraph
