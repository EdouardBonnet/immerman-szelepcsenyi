import Lax733996Proofs.CountingPathBody

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax733996Proofs.ConfigurationProofs
open StackMacros (Macro)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

lemma pathSetup_spec (w : Word) (bound m k : ℕ) (hk : k < 2 ^ m) (d : Data M)
    (hw : reg d .width = SearchProgram.unary m) (hd : reg d .depth = SearchProgram.word m k)
    (hm : m + 1 < bound) :
    (pathSetup M).guard w bound d ∧
      reg ((pathSetup M).result w d) .a = SearchProgram.word m 0 ∧
      PathClock M m k ((pathSetup M).result w d) ∧
      Keeps pathWrites d ((pathSetup M).result w d) ∧
      ((pathSetup M).result w d).state.user = d.state.user := by
  have hg₁ := (fill_spec M w bound m .a (by decide) none d hw hm).1
  obtain ⟨hf₁, ha₁, hu₁⟩ := fill_effect w bound m .a (by decide) none d hw hm
  let d₁ := (fill M .a).result w d
  have hd₁ : reg d₁ .depth = SearchProgram.word m k := (hf₁ .depth (by simp)).trans hd
  have hg₂ := (copy_spec M w bound .depth .kinds (by decide) d₁).1
  obtain ⟨hf₂, hk₂, hu₂⟩ := copy_effect w bound .depth .kinds (by decide) d₁
  let d₂ := (copy M .depth .kinds).result w d₁
  have hd₂ : reg d₂ .kinds = SearchProgram.word m k := hk₂.trans hd₁
  have hg₃ := (decrement_spec M w bound m k hk .kinds d₂ hd₂).1
  obtain ⟨hf₃, hk₃, hu₃, hflag⟩ := decrement_effect w bound m k hk .kinds d₂ hd₂
  refine ⟨⟨hg₁, hg₂, hg₃⟩, ?_, ⟨hk₃, hflag⟩, ?_, hu₃.trans (hu₂.trans hu₁)⟩
  · exact (hf₃ .a (by simp)).trans ((hf₂ .a (by simp)).trans (ha₁.trans (filledWord_none M m)))
  · exact (hf₁.mono (by intro r hr; simp [pathWrites] at hr ⊢; tauto)).trans
      ((hf₂.mono (by intro r hr; simp [pathWrites] at hr ⊢; tauto)).trans
      (hf₃.mono (by intro r hr; simp [pathWrites] at hr ⊢; tauto)))

lemma pathFinish_guard (w : Word) (bound : ℕ) (d : Data M) :
    (pathFinish M).guard w bound d := ⟨(compare_spec M w bound .a .frameMiddle d).1, trivial⟩

lemma pathFinish_spec (w : Word) (bound m : ℕ) (d : Data M) (x u : Fin (2 ^ m))
    (ha : reg d .a = SearchProgram.word m x.val) (hu : reg d .frameMiddle = SearchProgram.word m u.val) :
    Keeps ∅ d ((pathFinish M).result w d) ∧
      ((pathFinish M).result w d).state.user.overflow = d.state.user.overflow ∧
      valid M ((pathFinish M).result w d).state = (valid M d.state && decide (x = u)) := by
  obtain ⟨hk, huser, hflag⟩ := compare_effect w bound .a .frameMiddle d
  refine ⟨hk, congrArg (fun s => s.overflow) huser, ?_⟩
  change valid M ((requireFlag M).result w ((compare M .a .frameMiddle).result w d)).state = _
  rw [requireFlag_valid, hflag, ha, hu]
  have hl : valid M ((compare M .a .frameMiddle).result w d).state = valid M d.state := by
    unfold valid
    rw [huser]
  simp only [hl, SearchProgram.word_eq_fin_iff]

end

end Lax733996Proofs.CountingProgram
