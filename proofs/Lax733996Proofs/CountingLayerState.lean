import Lax733996Proofs.CountingLayerStep

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax733996Proofs.ConfigurationProofs
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

def LastBit (w : Word) (m k i : ℕ) (d : Data M) : Prop :=
  ∀ v : Fin (2 ^ m), v.val + 1 = i → (d.state.user.overflow = true ↔
    v ∈ Lax733996.Counting.layer (EncodedGraph.graph M w m) (EncodedGraph.first m) (k + 1))

structure LayerState (w : Word) (bound m k i : ℕ) (d : Data M) : Prop where
  good : Good w bound d
  width : reg d .width = SearchProgram.unary m
  depth : reg d .depth = SearchProgram.word m k
  count : reg d .middle = SearchProgram.word (m + 1) (layerCount M w m k)
  clock : LayerClock M m i d
  progress : ∃ c, c ≤ i ∧ reg d .frameA = SearchProgram.word (m + 1) c ∧
    (valid M d.state = true → c = canonicalCount M w m (k + 1) i ∧ LastBit M w m k i d)

lemma small_count (m i c : ℕ) (hi : i ≤ 2 ^ m) (hc : c ≤ i) : c < 2 ^ (m + 1) := by
  have hp : 0 < 2 ^ m := by positivity
  rw [pow_succ]
  omega

lemma layerState_body_total (w : Word) (bound m k i : ℕ) (hk : k < 2 ^ m) (hi : i < 2 ^ m)
    (hm : m + 1 < bound) (d : Data M) (hd : LayerState M w bound m k i d) :
    Total w bound (layerStep M) d := by
  obtain ⟨c, hc, hcnt, _⟩ := hd.progress
  exact layerStep_total M w bound m k i c hk hi (small_count m i c (by omega) hc)
    d hd.good hd.width hd.depth hd.clock.1 hm hd.count hcnt

lemma layerState_step (w : Word) (bound m k i : ℕ) (hk : k < 2 ^ m) (hi : i < 2 ^ m)
    (hm : m + 1 < bound) (d e : Data M) (hd : LayerState M w bound m k i d)
    (h : Exec w bound (layerStep M) d e) :
    LayerState M w bound m k (i + 1) e ∧ Keeps layerWrites d e ∧
      (valid M e.state = true → valid M d.state = true) := by
  obtain ⟨c, hc, hcnt, hspec⟩ := hd.progress
  obtain ⟨hclock, hnext, hkeep, hlive⟩ := layerStep_sound M w bound m k i c hk hi
    (small_count m i c (by omega) hc) d e hd.good hd.width hd.depth hd.clock.1 hm hd.count hcnt h
  refine ⟨⟨h.good.2, (hkeep .width (by simp [layerWrites])).trans hd.width,
    (hkeep .depth (by simp [layerWrites])).trans hd.depth,
    (hkeep .middle (by simp [layerWrites])).trans hd.count, hclock,
    ⟨c + e.state.user.overflow.toNat, ?_, hnext, ?_⟩⟩, hkeep, fun hl => (hlive hl).1⟩
  · cases e.state.user.overflow <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  · intro hl
    obtain ⟨hdl, hclassification⟩ := hlive hl
    obtain ⟨hcanonical, _⟩ := hspec hdl
    refine ⟨?_, ?_⟩
    · have hb : e.state.user.overflow = decide ((⟨i, hi⟩ : Fin (2 ^ m)) ∈
          Lax733996.Counting.layer (EncodedGraph.graph M w m) (EncodedGraph.first m) (k + 1)) :=
        Bool.eq_iff_iff.mpr (by simpa using hclassification)
      have hn := StreamingCensus.canonical_card_next (EncodedGraph.graph M w m) (EncodedGraph.first m) (k + 1) i hi
      change canonicalCount M w m (k + 1) (i + 1) = canonicalCount M w m (k + 1) i + _ at hn
      rw [hcanonical, hn, hb]
      split <;> simp_all
    · intro v hv
      have heq : v = (⟨i, hi⟩ : Fin (2 ^ m)) := Fin.ext (by change v.val = i; omega)
      exact heq ▸ hclassification

lemma layerState_complete_step (w : Word) (bound m k i : ℕ) (hk : k < 2 ^ m) (hi : i < 2 ^ m)
    (hm : m + 1 < bound) (d : Data M) (hd : LayerState M w bound m k i d) (hl : valid M d.state = true) :
    ∃ e, Exec w bound (layerStep M) d e ∧ LayerState M w bound m k (i + 1) e ∧ valid M e.state = true := by
  obtain ⟨c, hc, hcnt, _⟩ := hd.progress
  obtain ⟨e, he, _, hel⟩ := layerStep_complete M w bound m k i c hk hi (small_count m i c (by omega) hc)
    d hd.good hd.width hd.depth hd.clock.1 hm hd.count hcnt hl
  exact ⟨e, he, (layerState_step M w bound m k i hk hi hm d e hd he).1, hel⟩

end

end Lax733996Proofs.CountingProgram
