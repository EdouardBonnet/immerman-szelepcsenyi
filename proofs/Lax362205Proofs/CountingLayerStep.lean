import Lax362205Proofs.CountingCensus
import Lax362205Proofs.CountingLayerRecord

namespace Lax362205Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax362205Proofs.ConfigurationProofs
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

def layerWrites : Finset SearchProgram.Register := {.a, .b, .kinds, .aux, .frameDepth, .frameMiddle, .frameA, .frameB}

def layerCount (w : Word) (m k : ℕ) : ℕ :=
  (Lax362205.Counting.layer (EncodedGraph.graph M w m) (EncodedGraph.first m) k).card

def LayerStepPost (w : Word) (m k i c : ℕ) (hi : i < 2 ^ m) (d e : Data M) : Prop :=
  LayerClock M m (i + 1) e ∧
    reg e .frameA = SearchProgram.word (m + 1) (c + e.state.user.overflow.toNat) ∧ Keeps layerWrites d e ∧
    (valid M e.state = true → valid M d.state = true ∧
      (e.state.user.overflow = true ↔ (⟨i, hi⟩ : Fin (2 ^ m)) ∈
        Lax362205.Counting.layer (EncodedGraph.graph M w m) (EncodedGraph.first m) (k + 1)))

lemma layerStep_total (w : Word) (bound m k i c : ℕ) (hk : k < 2 ^ m) (hi : i < 2 ^ m)
    (hc : c < 2 ^ (m + 1)) (d : Data M) (hd : Good w bound d)
    (hw : reg d .width = SearchProgram.unary m) (hdepth : reg d .depth = SearchProgram.word m k)
    (hv : reg d .frameB = SearchProgram.word m i) (hm : m + 1 < bound)
    (hcnt : reg d .middle = SearchProgram.word (m + 1) (layerCount M w m k))
    (hnext : reg d .frameA = SearchProgram.word (m + 1) c) : Total w bound (layerStep M) d := by
  apply Total.seq (census_total M w bound m k hk d hd hw hdepth ⟨i, hi⟩ hv hm)
  intro f hf
  obtain ⟨hkeep, _⟩ := census_sound M w bound m k hk d f hd hw hdepth ⟨i, hi⟩ hv hm hcnt hf
  have hg := (layerRecord_spec M w bound m i c hi hc f
    ((hkeep .frameB (by simp [censusWrites])).trans hv)
    ((hkeep .frameA (by simp [censusWrites])).trans hnext)).1
  exact .det ((layerRecord M).correct w bound f hf.good.2 hg)

lemma layerStep_sound (w : Word) (bound m k i c : ℕ) (hk : k < 2 ^ m) (hi : i < 2 ^ m)
    (hc : c < 2 ^ (m + 1)) (d e : Data M) (hd : Good w bound d)
    (hw : reg d .width = SearchProgram.unary m) (hdepth : reg d .depth = SearchProgram.word m k)
    (hv : reg d .frameB = SearchProgram.word m i) (hm : m + 1 < bound)
    (hcnt : reg d .middle = SearchProgram.word (m + 1) (layerCount M w m k))
    (hnext : reg d .frameA = SearchProgram.word (m + 1) c)
    (h : Exec w bound (layerStep M) d e) : LayerStepPost M w m k i c hi d e := by
  cases h with
  | @seq _ _ _ f _ hcen hrecord =>
    obtain ⟨hkeep, hlive⟩ := census_sound M w bound m k hk d f hd hw hdepth ⟨i, hi⟩ hv hm hcnt hcen
    obtain ⟨hg, hclock, hcount, hkeep', huser⟩ := layerRecord_spec M w bound m i c hi hc f
      ((hkeep .frameB (by simp [censusWrites])).trans hv)
      ((hkeep .frameA (by simp [censusWrites])).trans hnext)
    obtain rfl := (ChoiceLanguage.det_exec_iff ((layerRecord M).correct w bound f hcen.good.2 hg)).mp hrecord
    refine ⟨hclock, ?_, ?_, ?_⟩
    · simpa only [huser] using hcount
    · exact (hkeep.mono (by intro r hr; simp [censusWrites, layerWrites] at hr ⊢; tauto)).trans
        (hkeep'.mono (by intro r hr; simp [layerWrites] at hr ⊢; tauto))
    · simpa only [valid, huser] using hlive

lemma layerStep_complete (w : Word) (bound m k i c : ℕ) (hk : k < 2 ^ m) (hi : i < 2 ^ m)
    (hc : c < 2 ^ (m + 1)) (d : Data M) (hd : Good w bound d)
    (hw : reg d .width = SearchProgram.unary m) (hdepth : reg d .depth = SearchProgram.word m k)
    (hv : reg d .frameB = SearchProgram.word m i) (hm : m + 1 < bound)
    (hcnt : reg d .middle = SearchProgram.word (m + 1) (layerCount M w m k))
    (hnext : reg d .frameA = SearchProgram.word (m + 1) c) (hl : valid M d.state = true) :
    ∃ e, Exec w bound (layerStep M) d e ∧ LayerStepPost M w m k i c hi d e ∧ valid M e.state = true := by
  obtain ⟨f, hcen, ⟨hkeep, _⟩, hfl⟩ := census_complete M w bound m k hk d hd hw hdepth ⟨i, hi⟩ hv hm hcnt hl
  obtain ⟨hg, _, _, _, huser⟩ := layerRecord_spec M w bound m i c hi hc f
    ((hkeep .frameB (by simp [censusWrites])).trans hv)
    ((hkeep .frameA (by simp [censusWrites])).trans hnext)
  have he := (layerRecord M).correct w bound f hcen.good.2 hg
  have hall : Exec w bound (layerStep M) d _ := .seq hcen (.det he)
  refine ⟨_, hall, layerStep_sound M w bound m k i c hk hi hc d _ hd hw hdepth hv hm hcnt hnext hall, ?_⟩
  simpa only [valid, huser] using hfl

end

end Lax362205Proofs.CountingProgram
