import Lax733996Proofs.CountingLayerState

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax307052Proofs
open StackMacros (Macro)
open ChoiceLanguage (Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

lemma layerSetup_spec (w : Word) (bound m : ℕ) (d : Data M)
    (hw : reg d .width = SearchProgram.unary m) (hm : m + 1 < bound) :
    (layerSetup M).guard w bound d ∧ LayerClock M m 0 ((layerSetup M).result w d) ∧
      reg ((layerSetup M).result w d) .frameA = SearchProgram.word (m + 1) 0 ∧
      Keeps layerWrites d ((layerSetup M).result w d) ∧
      ((layerSetup M).result w d).state.user = d.state.user := by
  have hg₁ := (fill_spec M w bound m .frameB (by decide) none d hw hm).1
  obtain ⟨hk₁, hv₁, hs₁⟩ := fill_effect w bound m .frameB (by decide) none d hw hm
  let d₁ := (fill M .frameB).result w d
  have hw₁ := (hk₁ .width (by simp)).trans hw
  have hg₂ := (fill_spec M w bound m .frameA (by decide) (some false) d₁ hw₁ hm).1
  obtain ⟨hk₂, hc₂, hs₂⟩ := fill_effect w bound m .frameA (by decide) (some false) d₁ hw₁ hm
  refine ⟨⟨hg₁, hg₂, trivial⟩, ⟨?_, ?_⟩, hc₂.trans (filledWord_some M m false), ?_, hs₂.trans hs₁⟩
  · exact (hk₂ .frameB (by simp)).trans (hv₁.trans (filledWord_none M m))
  · change false = decide (0 = 2 ^ m)
    simp [Nat.ne_of_lt (show 0 < 2 ^ m by positivity)]
  · exact (hk₁.mono (by intro r hr; simp [layerWrites] at hr ⊢; tauto)).trans
      (hk₂.mono (by intro r hr; simp [layerWrites] at hr ⊢; tauto))

lemma layerSetup_state (w : Word) (bound m k : ℕ) (d : Data M) (hd : Good w bound d)
    (hw : reg d .width = SearchProgram.unary m) (hdepth : reg d .depth = SearchProgram.word m k)
    (hcnt : reg d .middle = SearchProgram.word (m + 1) (layerCount M w m k)) (hm : m + 1 < bound) :
    LayerState M w bound m k 0 ((layerSetup M).result w d) ∧
      Keeps layerWrites d ((layerSetup M).result w d) ∧
      valid M ((layerSetup M).result w d).state = valid M d.state := by
  obtain ⟨hg, hclock, hcount, hkeep, huser⟩ := layerSetup_spec M w bound m d hw hm
  have he := (layerSetup M).correct w bound d hd hg
  refine ⟨⟨he.good.2, (hkeep .width (by simp [layerWrites])).trans hw,
    (hkeep .depth (by simp [layerWrites])).trans hdepth,
    (hkeep .middle (by simp [layerWrites])).trans hcnt, hclock, ⟨0, le_rfl, hcount, ?_⟩⟩, hkeep, ?_⟩
  · intro _
    refine ⟨?_, ?_⟩
    · simp [canonicalCount, StreamingCensus.canonical_zero]
    · intro v hv
      omega
  · unfold valid
    rw [huser]

end

end Lax733996Proofs.CountingProgram
