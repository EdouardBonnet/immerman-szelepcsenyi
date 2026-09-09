import Lax733996Proofs.CountingPrimitives
import Lax733996Proofs.CountingBounds

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930.SpaceBounds
open Lax307052Proofs
open StackLanguage (Exec Good)
open StackMacros (Macro)
open scoped Classical

noncomputable section

variable (M : Machine)

lemma expandWidth_spec (c len : ℕ) (w : Word) (bound : ℕ) (d : Data M)
    (hs : d.store (GraphQuery.key .bound) = SearchProgram.unary len)
    (hw : d.store (SearchProgram.key .width) = [])
    (ha : d.store (GraphQuery.key .aux) = [])
    (hb : (2 * letterWidth M * c) * len + 3 * letterWidth M < bound) :
    (expandWidth M c).guard w bound d ∧
    (expandWidth M c).result w d =
      ⟨{d.state with value := none}, d.inputHead,
        Function.update (Function.update d.store (SearchProgram.key .width)
          (SearchProgram.unary ((2 * letterWidth M * c) * len + 3 * letterWidth M)))
          (GraphQuery.key .bound) []⟩ := by
  obtain ⟨hg, hr⟩ := Macro.appendCopies_spec w bound
    (GraphQuery.key .bound) (SearchProgram.key .width) (GraphQuery.key .aux)
    (by simp [GraphQuery.key, SearchProgram.key]) (by simp [GraphQuery.key])
    (by simp [GraphQuery.key, SearchProgram.key]) (SearchProgram.symbol .tally)
    (2 * letterWidth M * c) len d hs ha (by rw [hw]; simp only [List.length_nil]; omega)
  constructor
  · refine ⟨hg, ?_, trivial⟩
    change (List.replicate (3 * letterWidth M) (SearchProgram.symbol .tally)).length +
      (((Macro.appendCopies (GraphQuery.key .bound) (SearchProgram.key .width) (GraphQuery.key .aux)
        (2 * letterWidth M * c)).result w d).store (SearchProgram.key .width)).length < bound
    rw [hr]
    simpa [Macro.putWord, hw, Nat.add_comm] using hb
  · dsimp only [expandWidth, Macro.seq]
    rw [hr]
    simp only [Macro.putWord, Macro.clear, StackRoutines.cleared, hw, List.append_nil]
    congr 1
    funext k
    by_cases hb' : k = GraphQuery.key .bound <;> by_cases hw' : k = SearchProgram.key .width <;>
      simp_all [Function.update_apply, SearchProgram.unary, GraphQuery.key, SearchProgram.key,
        ← List.replicate_add, Nat.add_comm]

lemma initialization (c : ℕ) (hc : 0 < c) (w : Word) :
    ∃ e : Data M, Exec w (spaceBound M c w.length) (initializeCode M c)
        ⟨initial M, 0, fun _ => []⟩ e ∧
      e.store (SearchProgram.key .width) = SearchProgram.unary (wordWidth M c w.length) ∧
      e.store (SearchProgram.key .middle) = SearchProgram.word (wordWidth M c w.length + 1) 1 ∧
      e.store (SearchProgram.key .depth) = SearchProgram.word (wordWidth M c w.length) 0 ∧
      e.state.user = (initial M).user ∧ e.state.flag = false ∧ e.inputHead = w.length + 1 := by
  let bound := spaceBound M c w.length
  let m := wordWidth M c w.length
  let d : Data M := ⟨initial M, 0, fun _ => []⟩
  have hd : Good w bound d := ⟨by simp [d], by intro k; simp [d, bound, spaceBound]⟩
  obtain ⟨d₁, he₁, hw₁, _, hf₁, hi₁, hu₁⟩ := LogarithmicWidth.execute w bound
    (GraphQuery.key .constructorLeft) (GraphQuery.key .constructorRight) (GraphQuery.key .bound)
    (by simp [GraphQuery.key]) (by simp [GraphQuery.key]) (by simp [GraphQuery.key])
    SearchProgram.bit SearchProgram.readBit (fun _ => rfl) (SearchProgram.symbol .tally)
    d hd rfl rfl rfl (initialization_bound M c w.length hc)
  have hm₁ : d₁.store (SearchProgram.key .width) = [] := by
    rw [hf₁ _ (by simp [GraphQuery.key, SearchProgram.key]) (by simp [GraphQuery.key, SearchProgram.key])]
  have ha₁ : d₁.store (GraphQuery.key .aux) = [] := by
    rw [hf₁ _ (by simp [GraphQuery.key]) (by simp [GraphQuery.key])]
  obtain ⟨hg₂, hr₂⟩ := expandWidth_spec M c (logSpace w.length) w bound d₁ hw₁ hm₁ ha₁ (by
    rw [← width_eq]
    change m < m + 3
    omega)
  let d₂ := (expandWidth M c).result w d₁
  have he₂ : Exec w bound (expandWidth M c).code d₁ d₂ := (expandWidth M c).correct w bound d₁ he₁.good.2 hg₂
  have hw₂ : d₂.store (SearchProgram.key .width) = SearchProgram.unary m := by
    simp [d₂, hr₂, GraphQuery.key, SearchProgram.key, m, width_eq]
  have hbudget : m + 1 < bound := by dsimp [bound, spaceBound, m]; omega
  obtain ⟨hg₃, hr₃⟩ := fill_spec M w bound m .middle (by decide) (some true) d₂ hw₂ hbudget
  let d₃ := (fill M .middle (some true)).result w d₂
  have he₃ : Exec w bound (fill M .middle (some true)).code d₂ d₃ :=
    (fill M .middle (some true)).correct w bound d₂ he₂.good.2 hg₃
  have hw₃ : d₃.store (SearchProgram.key .width) = SearchProgram.unary m := by
    simpa [d₃, hr₃, GraphQuery.key, SearchProgram.key] using hw₂
  obtain ⟨hg₄, hr₄⟩ := fill_spec M w bound m .depth (by decide) none d₃ hw₃ hbudget
  let d₄ := (fill M .depth).result w d₃
  have he₄ : Exec w bound (fill M .depth).code d₃ d₄ := (fill M .depth).correct w bound d₃ he₃.good.2 hg₄
  have he₅ := (beginLoop M).correct w bound d₄ he₄.good.2 trivial
  refine ⟨_, .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ he₅))), ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simpa [beginLoop, Macro.assign, StackLanguage.assigned, d₄, hr₄, GraphQuery.key, SearchProgram.key] using hw₃
  · simp [beginLoop, Macro.assign, StackLanguage.assigned, d₄, hr₄, d₃, hr₃,
      GraphQuery.key, SearchProgram.key, filledWord_some, m]
  · simp [beginLoop, Macro.assign, StackLanguage.assigned, d₄, hr₄, filledWord_none, m]
  · simpa [beginLoop, Macro.assign, StackLanguage.assigned, d₄, hr₄, d₃, hr₃, d₂, hr₂, d] using hu₁
  · simpa [beginLoop, Macro.assign, StackLanguage.assigned, d₄, hr₄, d₃, hr₃, d₂, hr₂] using hi₁

end

end Lax733996Proofs.CountingProgram
