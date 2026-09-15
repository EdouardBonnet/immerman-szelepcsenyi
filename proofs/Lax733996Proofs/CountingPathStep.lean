import Lax733996Proofs.CountingGuess

set_option backward.isDefEq.respectTransparency false

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax733996Proofs.ConfigurationProofs
open SearchProgram (Register)
open StackMacros (Macro)
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

variable (M : Machine)

lemma pathMove_spec (w : Word) (bound m : ℕ) (d : Data M) (x y : Fin (2 ^ m))
    (ha : reg d .a = SearchProgram.word m x.val) (hb : reg d .b = SearchProgram.word m y.val)
    (hm : m + 1 < bound) :
    (pathMove M).guard w bound d ∧
      reg ((pathMove M).result w d) .a = SearchProgram.word m y.val ∧
      Keeps {.a} d ((pathMove M).result w d) ∧
      ((pathMove M).result w d).state.user.overflow = d.state.user.overflow ∧
      valid M ((pathMove M).result w d).state =
        (valid M d.state && EncodedGraph.graph M w m x y) := by
  obtain ⟨hg, hp, ho, hk, hq⟩ := CountingQuery.procedure_state M Unit w bound d
    (BinaryCounter.word m x.val) (BinaryCounter.word m y.val) ha hb (by simp) (by simpa using! hm)
  let dq := (GraphQuery.procedure M Unit).result w d
  let dr := (requireAnswer M).result w dq
  have hc := copy_spec M w bound .b .a (by decide) dr
  have hb' : reg dr .b = SearchProgram.word m y.val := (hk .b).trans hb
  refine ⟨⟨hg, trivial, hc.1⟩, ?_, ?_, ?_, ?_⟩
  all_goals change _
  all_goals dsimp only [pathMove, Macro.seq]; rw [hc.2]
  · simpa [reg] using! hb'
  · intro r hr
    simp only [Finset.mem_singleton] at hr
    simpa [reg, GraphQuery.key, SearchProgram.key, hr] using! hk r
  · exact ho
  · change valid M dr.state = _
    rw [requireAnswer_valid]
    have hp' : valid M dq.state = valid M d.state := by unfold valid; rw [hp]
    rw [hp', hq]
    rfl

def PathStepPost (w : Word) (m : ℕ) (d e : Data M) (x y : Fin (2 ^ m)) : Prop :=
  reg e .a = SearchProgram.word m y.val ∧ Keeps {.a, .b, .aux} d e ∧
    e.state.user.overflow = d.state.user.overflow ∧
    (valid M e.state = true → valid M d.state = true ∧ (x = y ∨ EncodedGraph.graph M w m x y = true))

lemma pathStep_total (w : Word) (bound m : ℕ) (d : Data M) (hd : Good w bound d)
    (hw : reg d .width = SearchProgram.unary m) (x : Fin (2 ^ m))
    (ha : reg d .a = SearchProgram.word m x.val) (hm : m + 1 < bound) :
    Total w bound (pathStep M) d := by
  apply Total.seq (.choose d _ hd)
  intro e he
  cases he with
  | choose _ _ b _ =>
    cases b with
    | false => exact .branch_false rfl (.det (.skip _ hd))
    | true =>
      apply Total.branch_true rfl
      let dc := StackLanguage.assigned d {d.state with flag := true}
      apply Total.seq (guess_total M w bound m .b (by decide) (by decide) dc hd hw)
      intro f hf
      obtain ⟨y, hy, hk, _⟩ := guess_sound M w bound m .b (by decide) (by decide) dc f hd hw hf
      have hfa : reg f .a = SearchProgram.word m x.val := (hk .a (by simp)).trans ha
      have hg := (pathMove_spec M w bound m f x y hfa hy hm).1
      exact .det ((pathMove M).correct w bound f hf.good.2 hg)

lemma pathStep_sound (w : Word) (bound m : ℕ) (d e : Data M) (hd : Good w bound d)
    (hw : reg d .width = SearchProgram.unary m) (x : Fin (2 ^ m))
    (ha : reg d .a = SearchProgram.word m x.val) (hm : m + 1 < bound)
    (h : Exec w bound (pathStep M) d e) :
    ∃ y, PathStepPost M w m d e x y := by
  cases h with
  | seq hc hb =>
    cases hc with
    | choose _ _ b _ =>
      cases b with
      | false =>
        cases hb with
        | branch_true ht _ => simp [StackLanguage.assigned] at ht
        | branch_false _ hs =>
          cases hs with
          | det he =>
            cases he
            exact ⟨x, ha, Keeps.refl _ _, rfl, fun hv => ⟨hv, Or.inl rfl⟩⟩
      | true =>
        cases hb with
        | branch_false ht _ => simp [StackLanguage.assigned] at ht
        | branch_true _ hs =>
          cases hs with
          | @seq _ _ _ f _ hg hmoving =>
            let dc := StackLanguage.assigned d {d.state with flag := true}
            obtain ⟨y, hy, hk, hu⟩ := guess_sound M w bound m .b (by decide) (by decide) dc f hd hw hg
            have hfa : reg _ .a = SearchProgram.word m x.val := (hk .a (by simp)).trans ha
            obtain ⟨hguard, hya, hkeep, hfound, hvalid⟩ := pathMove_spec M w bound m _ x y hfa hy hm
            have he := (pathMove M).correct w bound _ hg.good.2 hguard
            obtain rfl := (ChoiceLanguage.det_exec_iff he).mp hmoving
            refine ⟨y, hya, ?_, ?_, ?_⟩
            · exact hk.mono (by intro r hr; simp at hr ⊢; tauto) |>.trans
                (hkeep.mono (by intro r hr; simp at hr ⊢; tauto))
            · exact hfound.trans (congrArg (fun u => u.overflow) hu)
            · intro hv
              rw [hvalid, Bool.and_eq_true] at hv
              have hl : valid M f.state = valid M d.state := by unfold valid; rw [hu]; rfl
              exact ⟨hl ▸ hv.1, Or.inr hv.2⟩

lemma pathStep_complete (w : Word) (bound m : ℕ) (d : Data M) (hd : Good w bound d)
    (hw : reg d .width = SearchProgram.unary m) (x y : Fin (2 ^ m))
    (ha : reg d .a = SearchProgram.word m x.val) (hm : m + 1 < bound)
    (hv : valid M d.state = true) (hxy : x = y ∨ EncodedGraph.graph M w m x y = true) :
    ∃ e, Exec w bound (pathStep M) d e ∧ PathStepPost M w m d e x y ∧ valid M e.state = true := by
  rcases hxy with rfl | hedge
  · refine ⟨_, .seq (.choose d _ false hd) (.branch_false rfl (.det (.skip _ hd))), ?_, hv⟩
    exact ⟨ha, Keeps.refl _ _, rfl, fun h => ⟨h, Or.inl rfl⟩⟩
  · let dc := StackLanguage.assigned d {d.state with flag := true}
    obtain ⟨dg, hg, hgy, hk, hu⟩ := guess_complete M w bound m .b (by decide) (by decide) dc hd hw y
    have hga : reg dg .a = SearchProgram.word m x.val := (hk .a (by simp)).trans ha
    obtain ⟨hguard, hya, hkeep, hfound, hvalid⟩ := pathMove_spec M w bound m dg x y hga hgy hm
    have he := (pathMove M).correct w bound dg hg.good.2 hguard
    have hall : Exec w bound (pathStep M) d _ :=
      .seq (.choose d _ true hd) (.branch_true rfl (.seq hg (.det he)))
    refine ⟨_, hall, ⟨hya, ?_, ?_, ?_⟩, ?_⟩
    · exact hk.mono (by intro r hr; simp at hr ⊢; tauto) |>.trans
        (hkeep.mono (by intro r hr; simp at hr ⊢; tauto))
    · exact hfound.trans (congrArg (fun u => u.overflow) hu)
    · exact fun _ => ⟨hv, Or.inr hedge⟩
    · rw [hvalid, hedge]
      simpa [valid, hu, dc, StackLanguage.assigned] using! hv

end

end Lax733996Proofs.CountingProgram
