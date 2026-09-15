import Lax733996Proofs.CountingCensusState

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax733996Proofs.ConfigurationProofs
open StackMacros (Macro)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

lemma censusSetup_spec (w : Word) (bound m : ℕ) (d : Data M) (v : Fin (2 ^ m))
    (hw : reg d .width = SearchProgram.unary m) (hv : reg d .frameB = SearchProgram.word m v.val)
    (hm : m + 1 < bound) :
    (censusSetup M).guard w bound d ∧ CensusClock M m 0 ((censusSetup M).result w d) ∧
      reg ((censusSetup M).result w d) .frameDepth = SearchProgram.word (m + 1) 0 ∧
      Keeps censusWrites d ((censusSetup M).result w d) ∧
      valid M ((censusSetup M).result w d).state = valid M d.state ∧
      ((censusSetup M).result w d).state.user.overflow = decide (v = EncodedGraph.first m) := by
  have hg₁ := (fill_spec M w bound m .frameMiddle (by decide) none d hw hm).1
  obtain ⟨hk₁, hu₁, hs₁⟩ := fill_effect w bound m .frameMiddle (by decide) none d hw hm
  let d₁ := (fill M .frameMiddle).result w d
  have hw₁ := (hk₁ .width (by simp)).trans hw
  have hg₂ := (fill_spec M w bound m .frameDepth (by decide) (some false) d₁ hw₁ hm).1
  obtain ⟨hk₂, hc₂, hs₂⟩ := fill_effect w bound m .frameDepth (by decide) (some false) d₁ hw₁ hm
  let d₂ := (fill M .frameDepth (some false)).result w d₁
  have hw₂ := (hk₂ .width (by simp)).trans hw₁
  have hg₃ := (fill_spec M w bound m .a (by decide) none d₂ hw₂ hm).1
  obtain ⟨hk₃, ha₃, hs₃⟩ := fill_effect w bound m .a (by decide) none d₂ hw₂ hm
  let d₃ := (fill M .a).result w d₂
  have hv₃ : reg d₃ .frameB = SearchProgram.word m v.val :=
    (hk₃ .frameB (by simp)).trans ((hk₂ .frameB (by simp)).trans ((hk₁ .frameB (by simp)).trans hv))
  have hg₄ := (compare_spec M w bound .frameB .a d₃).1
  obtain ⟨hk₄, hs₄, hf₄⟩ := compare_effect w bound .frameB .a d₃
  let d₄ := (compare M .frameB .a).result w d₃
  refine ⟨⟨hg₁, hg₂, hg₃, hg₄, trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact (hk₄ .frameMiddle (by simp)).trans ((hk₃ .frameMiddle (by simp)).trans
      ((hk₂ .frameMiddle (by simp)).trans (hu₁.trans (filledWord_none M m))))
  · change false = decide (0 = 2 ^ m)
    simp [Nat.ne_of_lt (show 0 < 2 ^ m by positivity)]
  · exact (hk₄ .frameDepth (by simp)).trans ((hk₃ .frameDepth (by simp)).trans
      (hc₂.trans (filledWord_some M m false)))
  · exact (hk₁.mono (by intro r hr; simp [censusWrites] at hr ⊢; tauto)).trans
      ((hk₂.mono (by intro r hr; simp [censusWrites] at hr ⊢; tauto)).trans
      ((hk₃.mono (by intro r hr; simp [censusWrites] at hr ⊢; tauto)).trans
      (hk₄.mono (Finset.empty_subset _))))
  · unfold valid
    change decide (d₄.state.user.phase ≠ .done) = _
    rw [hs₄, hs₃, hs₂, hs₁]
  · change d₄.state.flag = _
    rw [hf₄, hv₃, ha₃, filledWord_none]
    change decide (SearchProgram.word m v.val = SearchProgram.word m (EncodedGraph.first m).val) = _
    simp only [SearchProgram.word_eq_fin_iff]

lemma censusFinish_guard (w : Word) (bound : ℕ) (d : Data M) :
    (censusFinish M).guard w bound d := ⟨(compare_spec M w bound .frameDepth .middle d).1, trivial⟩

lemma censusFinish_spec (w : Word) (bound : ℕ) (d : Data M) :
    Keeps ∅ d ((censusFinish M).result w d) ∧
      ((censusFinish M).result w d).state.user.overflow = d.state.user.overflow ∧
      valid M ((censusFinish M).result w d).state =
        (valid M d.state && decide (reg d .frameDepth = reg d .middle)) := by
  obtain ⟨hk, huser, hflag⟩ := compare_effect w bound .frameDepth .middle d
  refine ⟨hk, congrArg (fun s => s.overflow) huser, ?_⟩
  change valid M ((requireFlag M).result w ((compare M .frameDepth .middle).result w d)).state = _
  rw [requireFlag_valid, hflag]
  unfold valid
  rw [huser]

end

end Lax733996Proofs.CountingProgram
