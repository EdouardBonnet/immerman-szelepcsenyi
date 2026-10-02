import Lax362205.Reachability
import Mathlib.Data.Fintype.Powerset

/-!
---
title: Inductive counting certificates
type: definition
---
The $k$th reachable layer contains vertices at distance at most $k$ from the
source. A census lists distinct reachable vertices and their path witnesses.
Given the correct census size, a negative classification checks that no
listed vertex has an edge to the target. A counting step classifies every
vertex and counts the positive answers.
-/

namespace Lax362205.Counting

open scoped Classical

open Lax362205.Reachability

/-- The vertices reachable from `a` using at most `k` directed edges. -/
noncomputable def layer {N : ℕ} (G : Graph N) (a : Fin N) (k : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun v => Within (fun u v => G u v = true) k a v)

/-- A set of `c` distinct vertices, each reachable within `k` steps. -/
def Census {N : ℕ} (G : Graph N) (a : Fin N) (k c : ℕ) (S : Finset (Fin N)) : Prop :=
  S.card = c ∧ ∀ v ∈ S, Within (fun u v => G u v = true) k a v

/-- A positive answer supplies a path; a negative answer supplies a census that has no edge to `v`. -/
def Classify {N : ℕ} (G : Graph N) (a : Fin N) (k c : ℕ) (v : Fin N) : Bool → Prop
  | true => Within (fun u v => G u v = true) (k + 1) a v
  | false => ∃ S, Census G a k c S ∧ v ≠ a ∧ ∀ u ∈ S, G u v = false

/-- Classify every vertex for the next layer and count exactly `d` positive answers. -/
def CountStep {N : ℕ} (G : Graph N) (a : Fin N) (k c d : ℕ) : Prop :=
  ∃ answers : Fin N → Bool, (∀ v, Classify G a k c v (answers v)) ∧
    (Finset.univ.filter (fun v => answers v = true)).card = d

/-- Start with the source alone and certify the size of each successive reachable layer. -/
def CountTrace {N : ℕ} (G : Graph N) (a : Fin N) (counts : ℕ → ℕ) : Prop :=
  counts 0 = 1 ∧ ∀ k < N, CountStep G a k (counts k) (counts (k + 1))

/-- A certified sequence of layer counts whose final census omits the target `b`. -/
def NonreachCertificate {N : ℕ} (G : Graph N) (a b : Fin N) : Prop :=
  ∃ counts, CountTrace G a counts ∧
    ∃ S, Census G a N (counts N) S ∧ b ∉ S

end Lax362205.Counting
