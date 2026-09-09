import Lax307052.Reachability
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

namespace Lax733996.Counting

open Lax307052.Reachability

noncomputable def layer {N : ℕ} (G : Graph N) (a : Fin N) (k : ℕ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun v => Within (fun u v => G u v = true) k a v)

def Census {N : ℕ} (G : Graph N) (a : Fin N) (k c : ℕ) (S : Finset (Fin N)) : Prop :=
  S.card = c ∧ ∀ v ∈ S, Within (fun u v => G u v = true) k a v

def Classify {N : ℕ} (G : Graph N) (a : Fin N) (k c : ℕ) (v : Fin N) : Bool → Prop
  | true => Within (fun u v => G u v = true) (k + 1) a v
  | false => ∃ S, Census G a k c S ∧ v ≠ a ∧ ∀ u ∈ S, G u v = false

def CountStep {N : ℕ} (G : Graph N) (a : Fin N) (k c d : ℕ) : Prop :=
  ∃ answers : Fin N → Bool, (∀ v, Classify G a k c v (answers v)) ∧
    (Finset.univ.filter (fun v => answers v = true)).card = d

def CountTrace {N : ℕ} (G : Graph N) (a : Fin N) (counts : ℕ → ℕ) : Prop :=
  counts 0 = 1 ∧ ∀ k < N, CountStep G a k (counts k) (counts (k + 1))

def NonreachCertificate {N : ℕ} (G : Graph N) (a b : Fin N) : Prop :=
  ∃ counts, CountTrace G a counts ∧
    ∃ S, Census G a N (counts N) S ∧ b ∉ S

end Lax733996.Counting
