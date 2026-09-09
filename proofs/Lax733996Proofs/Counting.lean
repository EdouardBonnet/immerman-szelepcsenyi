import Lax733996.ExactCensus
import Lax733996.SuccessorLayer
import Lax733996.Classification
import Lax733996.CountingStep
import Lax733996.CountingTrace
import Lax733996.Nonreachability
import Lax307052.ShortPaths
import Mathlib.Tactic

namespace Lax733996Proofs

open Lax733996 Lax733996.Counting Lax307052.Reachability

@[simp] lemma mem_layer {N : ℕ} (G : Graph N) (a v : Fin N) (k : ℕ) :
    v ∈ layer G a k ↔ Within (fun u v => G u v = true) k a v := by
  classical
  simp [layer]

lemma layer_zero {N : ℕ} (G : Graph N) (a : Fin N) : layer G a 0 = {a} := by
  ext v
  rw [mem_layer, Finset.mem_singleton]
  constructor
  · rintro ⟨k, hk, h⟩
    have : k = 0 := by omega
    subst k
    cases h
    rfl
  · rintro rfl
    exact ⟨0, le_rfl, Walk.nil a⟩

/--
---
conclusion: Lax733996.ExactCensus.complete
assumptions:
---
A finite subset with the same cardinality is the entire layer.
-/
lemma exact_census {N : ℕ} (G : Graph N) (a : Fin N) (k : ℕ) (S : Finset (Fin N)) :
    Census G a k (layer G a k).card S → S = layer G a k := by
  rintro ⟨hc, hs⟩
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    exact (mem_layer G a v k).mpr (hs v hv)
  · exact hc.symm.le

/--
---
conclusion: Lax733996.SuccessorLayer.successor
assumptions:
---
Remove the last edge of a nonempty walk; the empty walk ends at the source.
-/
lemma successor_layer {N : ℕ} (G : Graph N) (a v : Fin N) (k : ℕ) :
    v ∈ layer G a (k + 1) ↔ v = a ∨ ∃ u ∈ layer G a k, G u v = true := by
  rw [mem_layer]
  constructor
  · rintro ⟨l, hl, hw⟩
    cases hw with
    | nil => exact Or.inl rfl
    | @tail l a u v hp he =>
      exact Or.inr ⟨u, (mem_layer G a u k).mpr ⟨l, by omega, hp⟩, he⟩
  · rintro (rfl | ⟨u, hu, he⟩)
    · exact ⟨0, Nat.zero_le _, Walk.nil a⟩
    · obtain ⟨l, hl, hw⟩ := (mem_layer G a u k).mp hu
      exact ⟨l + 1, by omega, Walk.tail hw he⟩

/--
---
conclusion: Lax733996.Classification.correct
assumptions:
  - Lax733996.ExactCensus.complete
  - Lax733996.SuccessorLayer.successor
---
An exact census makes the negative test exhaustive.
-/
lemma classification {N : ℕ} (G : Graph N) (a v : Fin N) (k : ℕ) (b : Bool) :
    Classify G a k (layer G a k).card v b ↔
      (b = true ↔ v ∈ layer G a (k + 1)) := by
  classical
  cases b with
  | true => simp [Classify]
  | false =>
    simp only [Classify, Bool.false_eq_true, false_iff]
    constructor
    · rintro ⟨S, hc, hv, he⟩ hnext
      have hS := ExactCensus.complete G a k S hc
      subst S
      rcases (SuccessorLayer.successor G a v k).mp hnext with h | ⟨u, hu, h⟩
      · exact hv h
      · have := he u hu
        simp_all
    · intro hn
      refine ⟨layer G a k, ⟨rfl, ?_⟩, ?_, ?_⟩
      · intro u hu
        exact (mem_layer G a u k).mp hu
      · intro heq
        exact hn ((SuccessorLayer.successor G a v k).mpr (Or.inl heq))
      · intro u hu
        apply Bool.eq_false_iff.mpr
        intro he
        exact hn ((SuccessorLayer.successor G a v k).mpr (Or.inr ⟨u, hu, he⟩))

/--
---
conclusion: Lax733996.CountingStep.correct
assumptions:
  - Lax733996.Classification.correct
---
The vertices classified positively are exactly the next layer.
-/
lemma counting_step {N : ℕ} (G : Graph N) (a : Fin N) (k d : ℕ) :
    CountStep G a k (layer G a k).card d ↔ d = (layer G a (k + 1)).card := by
  classical
  constructor
  · rintro ⟨answers, ha, hd⟩
    have heq : Finset.univ.filter (fun v => answers v = true) = layer G a (k + 1) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Classification.correct G a v k (answers v)).mp (ha v)
    exact hd.symm.trans (congrArg Finset.card heq)
  · rintro rfl
    refine ⟨fun v => decide (v ∈ layer G a (k + 1)), ?_, ?_⟩
    · intro v
      exact (Classification.correct G a v k _).mpr (by simp)
    · simp

/--
---
conclusion: Lax733996.CountingTrace.correct
assumptions:
  - Lax733996.CountingStep.correct
---
Induct from the singleton initial layer through the certified counting steps.
-/
lemma counting_trace {N : ℕ} (G : Graph N) (a : Fin N) (counts : ℕ → ℕ) :
    CountTrace G a counts ↔ ∀ k ≤ N, counts k = (layer G a k).card := by
  constructor
  · rintro ⟨hzero, hstep⟩ k hk
    induction k with
    | zero => simpa [layer_zero] using hzero
    | succ k ih =>
      have ih' := ih (by omega)
      have h := hstep k (by omega)
      rw [ih'] at h
      exact (CountingStep.correct G a k _).mp h
  · intro h
    constructor
    · simpa [layer_zero] using h 0 (Nat.zero_le _)
    · intro k hk
      rw [h k (by omega), h (k + 1) (by omega)]
      exact (CountingStep.correct G a k _).mpr rfl

lemma final_layer {N : ℕ} (G : Graph N) (a b : Fin N) :
    b ∈ layer G a N ↔ Reachable G a b := by
  rw [mem_layer]
  constructor
  · rintro ⟨k, _, hw⟩
    induction hw with
    | nil => exact .refl
    | tail _ he ih => exact ih.tail he
  · intro hr
    obtain ⟨k, hk, hw⟩ := (Lax307052.ShortPaths.short_path G a b).mp hr
    exact ⟨k, Nat.le_of_lt hk, hw⟩

/--
---
conclusion: Lax733996.Nonreachability.correct
assumptions:
  - Lax307052.ShortPaths.short_path
  - Lax733996.CountingTrace.correct
  - Lax733996.ExactCensus.complete
---
The final exact census contains every reachable vertex, so omitting the target certifies nonreachability.
-/
lemma nonreachability {N : ℕ} (G : Graph N) (a b : Fin N) :
    NonreachCertificate G a b ↔ ¬ Reachable G a b := by
  classical
  constructor
  · rintro ⟨counts, ht, S, hc, hb⟩ hr
    have hcount := (CountingTrace.correct G a counts).mp ht N le_rfl
    rw [hcount] at hc
    have hS := ExactCensus.complete G a N S hc
    apply hb
    rw [hS]
    exact (final_layer G a b).mpr hr
  · intro hn
    refine ⟨fun k => (layer G a k).card, (CountingTrace.correct G a _).mpr (by simp),
      layer G a N, ⟨rfl, ?_⟩, ?_⟩
    · intro v hv
      exact (mem_layer G a v N).mp hv
    · exact fun hb => hn ((final_layer G a b).mp hb)

end Lax733996Proofs
