import Lax362205Proofs.Counting

/-! The invariant for an ordered census needs only a running count and
a Boolean recording whether a predecessor has been found. -/

namespace Lax362205Proofs.StreamingCensus

open Lax362205.Reachability Lax362205.Counting
open scoped Classical

noncomputable section

def visited (N i : ℕ) : Finset (Fin N) := Finset.univ.filter (fun v => v.val < i)

def Invariant {N : ℕ} (G : Graph N) (a v : Fin N) (k i c : ℕ) (found : Bool) : Prop :=
  ∃ S : Finset (Fin N), S ⊆ visited N i ∧ Census G a k c S ∧
    (found = true ↔ v = a ∨ ∃ u ∈ S, G u v = true)

lemma count_le {N : ℕ} (G : Graph N) (a v : Fin N) (k i c : ℕ) (found : Bool)
    (h : Invariant G a v k i c found) : c ≤ i := by
  obtain ⟨S, hs, hc, _⟩ := h
  let f : {u // u ∈ S} → Fin i := fun u => ⟨u.val.val, by simpa [visited] using hs u.property⟩
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun z : Fin i => z.val) huv
  simpa [hc.1] using Fintype.card_le_of_injective f hf

lemma initial {N : ℕ} (G : Graph N) (a v : Fin N) (k : ℕ) :
    Invariant G a v k 0 0 (decide (v = a)) := by
  refine ⟨∅, Finset.empty_subset _, ⟨rfl, ?_⟩, ?_⟩ <;> simp

lemma skip {N : ℕ} (G : Graph N) (a v : Fin N) (k i c : ℕ) (found : Bool)
    (h : Invariant G a v k i c found) : Invariant G a v k (i + 1) c found := by
  obtain ⟨S, hp, hc, hf⟩ := h
  refine ⟨S, ?_, hc, hf⟩
  intro u hu
  have hh := hp hu
  simp only [visited, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
  omega

lemma take {N : ℕ} (G : Graph N) (a v : Fin N) (k i c : ℕ) (found : Bool)
    (h : Invariant G a v k i c found) (hi : i < N)
    (hr : Within (fun u v => G u v = true) k a ⟨i, hi⟩) :
    Invariant G a v k (i + 1) (c + 1) (found || G ⟨i, hi⟩ v) := by
  obtain ⟨S, hp, hc, hf⟩ := h
  have hnot : (⟨i, hi⟩ : Fin N) ∉ S := by
    intro hs
    have hh := hp hs
    simpa [visited] using hh
  refine ⟨insert ⟨i, hi⟩ S, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · simp [visited]
    · have hh := hp hu
      simp only [visited, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
      omega
  · rw [Finset.card_insert_of_notMem hnot, hc.1]
  · intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hr
    · exact hc.2 u hu
  · simp only [Bool.or_eq_true, hf, Finset.mem_insert, exists_eq_or_imp]
    simp only [or_assoc, or_left_comm, or_comm]

lemma complete {N : ℕ} (G : Graph N) (a v : Fin N) (k : ℕ) (found : Bool)
    (h : Invariant G a v k N (layer G a k).card found) :
    found = true ↔ v ∈ layer G a (k + 1) := by
  obtain ⟨S, _, hc, hf⟩ := h
  have hS := exact_census G a k S hc
  rw [hS] at hf
  exact hf.trans (successor_layer G a v k).symm

lemma canonical {N : ℕ} (G : Graph N) (a v : Fin N) (k i : ℕ) :
    Invariant G a v k i ((layer G a k ∩ visited N i).card)
      (decide (v = a ∨ ∃ u ∈ layer G a k ∩ visited N i, G u v = true)) := by
  refine ⟨layer G a k ∩ visited N i, Finset.inter_subset_right,
    ⟨rfl, ?_⟩, by simp⟩
  intro u hu
  exact (mem_layer G a u k).mp (Finset.mem_inter.mp hu).1

lemma canonical_zero {N : ℕ} (G : Graph N) (a : Fin N) (k : ℕ) :
    layer G a k ∩ visited N 0 = ∅ := by simp [visited]

lemma canonical_next {N : ℕ} (G : Graph N) (a : Fin N) (k i : ℕ) (hi : i < N) :
    layer G a k ∩ visited N (i + 1) =
      if (⟨i, hi⟩ : Fin N) ∈ layer G a k then insert ⟨i, hi⟩ (layer G a k ∩ visited N i)
      else layer G a k ∩ visited N i := by
  ext u
  by_cases hu : u = ⟨i, hi⟩
  · subst u
    by_cases hm : (⟨i, hi⟩ : Fin N) ∈ layer G a k <;> simp [hm, visited]
  · have hval : u.val ≠ i := by intro h; exact hu (Fin.ext h)
    have hlt : u.val < i + 1 ↔ u.val < i := by omega
    split <;> simp only [Finset.mem_inter, visited, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert, hu, false_or, hlt]

lemma canonical_final {N : ℕ} (G : Graph N) (a : Fin N) (k : ℕ) :
    layer G a k ∩ visited N N = layer G a k := by
  ext u
  simp [visited, u.isLt]

lemma canonical_card_next {N : ℕ} (G : Graph N) (a : Fin N) (k i : ℕ) (hi : i < N) :
    (layer G a k ∩ visited N (i + 1)).card =
      (layer G a k ∩ visited N i).card + if (⟨i, hi⟩ : Fin N) ∈ layer G a k then 1 else 0 := by
  rw [canonical_next G a k i hi]
  have hn : (⟨i, hi⟩ : Fin N) ∉ layer G a k ∩ visited N i := by simp [visited]
  by_cases hh : (⟨i, hi⟩ : Fin N) ∈ layer G a k <;> simp [hh, hn]

end

end Lax362205Proofs.StreamingCensus
