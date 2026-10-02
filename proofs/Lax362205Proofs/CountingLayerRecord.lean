import Lax362205Proofs.CountingFrames

namespace Lax362205Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax362205Proofs.ConfigurationProofs
open StackMacros (Macro)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

def LayerClock (m i : ℕ) (d : Data M) : Prop :=
  reg d .frameB = SearchProgram.word m i ∧ d.state.flag = decide (i = 2 ^ m)

lemma layerClock_stop (m : ℕ) (d : Data M) (hc : LayerClock M m (2 ^ m) d) :
    running M d.state = false := by simp [running, hc.2]

lemma layerClock_running (m i : ℕ) (hi : i < 2 ^ m) (d : Data M) (hc : LayerClock M m i d) :
    running M d.state = valid M d.state := by simp [running, hc.2, Nat.ne_of_lt hi]

lemma layerRecord_spec (w : Word) (bound m i c : ℕ) (hi : i < 2 ^ m) (hc : c < 2 ^ (m + 1))
    (d : Data M) (hv : reg d .frameB = SearchProgram.word m i)
    (hcnt : reg d .frameA = SearchProgram.word (m + 1) c) :
    (layerRecord M).guard w bound d ∧ LayerClock M m (i + 1) ((layerRecord M).result w d) ∧
      reg ((layerRecord M).result w d) .frameA = SearchProgram.word (m + 1) (c + d.state.user.overflow.toNat) ∧
      Keeps {.frameA, .frameB} d ((layerRecord M).result w d) ∧
      ((layerRecord M).result w d).state.user = d.state.user := by
  cases hb : d.state.user.overflow with
  | false =>
    have hg := (increment_spec M w bound m i hi .frameB d hv).1
    obtain ⟨hkeep, hidx, huser, hflag⟩ := increment_effect w bound m i hi .frameB d hv
    have heq : (layerRecord M).result w d = (increment M .frameB).result w d := by
      simp [layerRecord, Macro.seq, Macro.branch, hb, Macro.skip]
    refine ⟨?_, ?_⟩
    · simpa [layerRecord, Macro.seq, Macro.branch, hb, Macro.skip] using hg
    · rw [heq]
      refine ⟨⟨hidx, hflag⟩, ?_, hkeep.mono (by intro r hr; simp at hr ⊢; tauto), huser⟩
      simpa [hb] using (hkeep .frameA (by simp)).trans hcnt
  | true =>
    have hg₁ := (increment_spec M w bound (m + 1) c hc .frameA d hcnt).1
    obtain ⟨hk₁, hc₁, hs₁, _⟩ := increment_effect w bound (m + 1) c hc .frameA d hcnt
    let d₁ := (increment M .frameA).result w d
    have hv₁ : reg d₁ .frameB = SearchProgram.word m i := (hk₁ .frameB (by simp)).trans hv
    have hg₂ := (increment_spec M w bound m i hi .frameB d₁ hv₁).1
    obtain ⟨hk₂, hv₂, hs₂, hf₂⟩ := increment_effect w bound m i hi .frameB d₁ hv₁
    have heq : (layerRecord M).result w d = (increment M .frameB).result w d₁ := by
      simp [layerRecord, Macro.seq, Macro.branch, hb, d₁]
    refine ⟨?_, ?_⟩
    · simpa [layerRecord, Macro.seq, Macro.branch, hb, d₁] using And.intro hg₁ hg₂
    · rw [heq]
      refine ⟨⟨hv₂, hf₂⟩, ?_, ?_, hs₂.trans hs₁⟩
      · simpa [hb] using (hk₂ .frameA (by simp)).trans hc₁
      · exact (hk₁.mono (by intro r hr; simp at hr ⊢; tauto)).trans
          (hk₂.mono (by intro r hr; simp at hr ⊢; tauto))

end

end Lax362205Proofs.CountingProgram
