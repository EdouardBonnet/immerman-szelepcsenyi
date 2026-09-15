import Lax733996Proofs.CountingFrames

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax733996Proofs.ConfigurationProofs
open StackMacros (Macro)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

lemma censusRecord_spec (w : Word) (bound m c : ℕ) (hc : c < 2 ^ (m + 1))
    (d : Data M) (u v : Fin (2 ^ m))
    (hu : reg d .frameMiddle = SearchProgram.word m u.val)
    (hv : reg d .frameB = SearchProgram.word m v.val)
    (hcnt : reg d .frameDepth = SearchProgram.word (m + 1) c) (hm : m + 1 < bound) :
    (censusRecord M).guard w bound d ∧
      Keeps {.a, .b, .frameDepth} d ((censusRecord M).result w d) ∧
      reg ((censusRecord M).result w d) .frameDepth = SearchProgram.word (m + 1) (c + 1) ∧
      ((censusRecord M).result w d).state.user.overflow =
        (d.state.user.overflow || EncodedGraph.graph M w m u v) ∧
      valid M ((censusRecord M).result w d).state = valid M d.state := by
  have hg₁ := (copy_spec M w bound .frameMiddle .a (by decide) d).1
  obtain ⟨hk₁, ha₁, hs₁⟩ := copy_effect w bound .frameMiddle .a (by decide) d
  let d₁ := (copy M .frameMiddle .a).result w d
  have hb₁ : reg d₁ .frameB = SearchProgram.word m v.val := (hk₁ .frameB (by simp)).trans hv
  have hc₁ : reg d₁ .frameDepth = SearchProgram.word (m + 1) c := (hk₁ .frameDepth (by simp)).trans hcnt
  have hg₂ := (copy_spec M w bound .frameB .b (by decide) d₁).1
  obtain ⟨hk₂, hb₂, hs₂⟩ := copy_effect w bound .frameB .b (by decide) d₁
  let d₂ := (copy M .frameB .b).result w d₁
  have ha₂ : reg d₂ .a = SearchProgram.word m u.val := (hk₂ .a (by simp)).trans (ha₁.trans hu)
  have hb₂' : reg d₂ .b = SearchProgram.word m v.val := hb₂.trans hb₁
  have hc₂ : reg d₂ .frameDepth = SearchProgram.word (m + 1) c := (hk₂ .frameDepth (by simp)).trans hc₁
  obtain ⟨hg₃, hp₃, ho₃, hk₃, hq₃⟩ := CountingQuery.procedure_state M Unit w bound d₂
    (BinaryCounter.word m u.val) (BinaryCounter.word m v.val) ha₂ hb₂' (by simp) (by simpa using hm)
  let d₃ := (GraphQuery.procedure M Unit).result w d₂
  let d₄ := StackLanguage.assigned d₃
    {d₃.state with user := {d₃.state.user with overflow := d₃.state.user.overflow || d₃.state.user.answer}}
  have hc₄ : reg d₄ .frameDepth = SearchProgram.word (m + 1) c := (hk₃ .frameDepth).trans hc₂
  have hg₅ := (increment_spec M w bound (m + 1) c hc .frameDepth d₄ hc₄).1
  obtain ⟨hk₅, hc₅, hs₅, _⟩ := increment_effect w bound (m + 1) c hc .frameDepth d₄ hc₄
  refine ⟨⟨hg₁, hg₂, hg₃, trivial, hg₅⟩, ?_, hc₅, ?_, ?_⟩
  · intro r hr
    have hn : r ≠ .a ∧ r ≠ .b ∧ r ≠ .frameDepth := by simpa using hr
    exact (hk₅ r (by simpa using hn.2.2)).trans ((hk₃ r).trans
      ((hk₂ r (by simpa using hn.2.1)).trans (hk₁ r (by simpa using hn.1))))
  · change ((increment M .frameDepth).result w d₄).state.user.overflow = _
    rw [hs₅]
    change (d₃.state.user.overflow || d₃.state.user.answer) = _
    rw [ho₃, hq₃, hs₂, hs₁]
    rfl
  · change valid M ((increment M .frameDepth).result w d₄).state = _
    unfold valid
    rw [hs₅]
    change decide (d₃.state.user.phase ≠ .done) = _
    rw [hp₃, hs₂, hs₁]

end

end Lax733996Proofs.CountingProgram
