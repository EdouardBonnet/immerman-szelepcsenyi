import Lax733996Proofs.CountingProgram

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax307052Proofs
open SearchProgram (Register)
open StackMacros (Macro)
open scoped Classical

noncomputable section

variable (M : Machine)

lemma copy_spec (w : Word) (bound : ℕ) (src dst : Register) (hne : src ≠ dst) (d : Data M) :
    (copy M src dst).guard w bound d ∧
    (copy M src dst).result w d =
      ⟨{d.state with value := none}, d.inputHead,
        Function.update (Function.update d.store (GraphQuery.key .aux) [])
          (SearchProgram.key dst) (d.store (SearchProgram.key src))⟩ := by
  constructor
  · simp [copy, Macro.seq, Macro.clear, Macro.copy, StackRoutines.cleared,
      GraphQuery.key, SearchProgram.key, hne]
  · simp [copy, Macro.seq, Macro.clear, Macro.copy, StackRoutines.cleared,
      GraphQuery.key, SearchProgram.key]
    funext j
    by_cases ha : j = Sum.inr GraphQuery.Scratch.aux <;> by_cases hd : j = Sum.inl dst <;>
      simp [Function.update_apply, ha, hd]

def filledWord (m : ℕ) (extra : Option Bool) : List (GraphQuery.Alphabet M Unit) :=
  extra.toList.map SearchProgram.bit ++ List.replicate m (SearchProgram.bit false)

lemma filledWord_length (m : ℕ) (extra : Option Bool) :
    (filledWord M m extra).length ≤ m + 1 := by
  cases extra <;> simp [filledWord]

lemma filledWord_none (m : ℕ) : filledWord M m none = SearchProgram.word m 0 := by
  simp [filledWord]

lemma filledWord_some (m : ℕ) (b : Bool) : filledWord M m (some b) = SearchProgram.word (m + 1) b.toNat := by
  cases b <;> simp [filledWord, SearchProgram.word, BinaryCounter.word, BinaryCounter.word_zero]

lemma fill_spec (w : Word) (bound m : ℕ) (dst : Register) (hne : dst ≠ .width)
    (extra : Option Bool) (d : Data M)
    (hw : d.store (SearchProgram.key .width) = SearchProgram.unary m) (hb : m + 1 < bound) :
    (fill M dst extra).guard w bound d ∧
    (fill M dst extra).result w d =
      ⟨{d.state with value := none}, d.inputHead,
        Function.update (Function.update d.store (GraphQuery.key .aux) [])
          (SearchProgram.key dst) (filledWord M m extra)⟩ := by
  dsimp only [SearchProgram.key, SearchProgram.unary] at hw
  have hmap : ((Function.update d.store (GraphQuery.key .aux) []) (SearchProgram.key .width)).map
      (fun _ => (SearchProgram.bit false : GraphQuery.Alphabet M Unit)) =
      List.replicate m (SearchProgram.bit false) := by
    simp [GraphQuery.key, SearchProgram.key, hw, SearchProgram.unary]
  constructor
  · cases extra <;>
      simp [fill, Macro.seq, Macro.clear, Macro.copyMap, Macro.skip, Macro.push,
        StackRoutines.cleared, GraphQuery.key, SearchProgram.key, Ne.symm hne, hw,
        SearchProgram.unary, hb]
  · cases extra <;>
      simp [fill, Macro.seq, Macro.clear, Macro.copyMap, Macro.skip, Macro.push,
        StackRoutines.cleared, StackLanguage.pushed, filledWord, GraphQuery.key, SearchProgram.key, hw]
    all_goals
      funext j
      by_cases ha : j = Sum.inr GraphQuery.Scratch.aux <;> by_cases hd : j = Sum.inl dst <;>
        simp [Function.update_apply, ha, hd]

lemma increment_spec (w : Word) (bound k n : ℕ) (hn : n < 2 ^ k) (r : Register) (d : Data M)
    (hr : d.store (SearchProgram.key r) = SearchProgram.word k n) :
    (increment M r).guard w bound d ∧
    (increment M r).result w d =
      ⟨{d.state with value := none, flag := decide (n + 1 = 2 ^ k)}, d.inputHead,
        Function.update (Function.update d.store (GraphQuery.key .aux) [])
          (SearchProgram.key r) (SearchProgram.word k (n + 1))⟩ := by
  dsimp only [SearchProgram.key, SearchProgram.word] at hr
  constructor
  · simp [increment, Macro.seq, Macro.clear, Macro.increment, StackRoutines.cleared,
      GraphQuery.key, SearchProgram.key, hr, SearchProgram.word, List.map_map, Function.comp_def]
  · simp [increment, Macro.seq, Macro.clear, Macro.increment, StackRoutines.cleared,
      GraphQuery.key, SearchProgram.key, hr, SearchProgram.word, List.map_map, Function.comp_def,
      BinaryCounter.word_increment, BinaryCounter.word_carry k n hn]
    funext j
    by_cases ha : j = Sum.inr GraphQuery.Scratch.aux <;> by_cases hr : j = Sum.inl r <;>
      simp [Function.update_apply, ha, hr]

lemma decrement_spec (w : Word) (bound k n : ℕ) (hn : n < 2 ^ k) (r : Register) (d : Data M)
    (hr : d.store (SearchProgram.key r) = SearchProgram.word k n) :
    (decrement M r).guard w bound d ∧
    (decrement M r).result w d =
      ⟨{d.state with value := none, flag := decide (n = 0)}, d.inputHead,
        Function.update (Function.update d.store (GraphQuery.key .aux) [])
          (SearchProgram.key r) (SearchProgram.word k (if n = 0 then 2 ^ k - 1 else n - 1))⟩ := by
  let dc := (Macro.clear (GraphQuery.key .aux)).result w d
  have hc : dc.store (SearchProgram.key r) = (BinaryCounter.word k n).map SearchProgram.bit := by
    simpa [dc, Macro.clear, StackRoutines.cleared, GraphQuery.key, SearchProgram.key] using hr
  have haux : dc.store (GraphQuery.key .aux) = [] := by simp [dc, Macro.clear, StackRoutines.cleared]
  refine ⟨⟨trivial, ?_⟩, ?_⟩
  · exact BinaryCounter.decrement_guard w bound _ _ (by simp [GraphQuery.key, SearchProgram.key])
      SearchProgram.bit SearchProgram.readBit (fun _ => rfl) k n dc hc haux
  · change (BinaryCounter.decrement (SearchProgram.key r) (GraphQuery.key .aux)
      SearchProgram.bit SearchProgram.readBit).result w dc = _
    rw [BinaryCounter.decrement_result w _ _ SearchProgram.bit SearchProgram.readBit (fun _ => rfl) k n hn dc hc]
    simp only [dc, Macro.clear, StackRoutines.cleared, SearchProgram.word]
    congr 1
    funext j
    by_cases ha : j = GraphQuery.key .aux <;> by_cases hr : j = SearchProgram.key r <;>
      simp [Function.update_apply, ha, hr]

lemma compare_spec (w : Word) (bound : ℕ) (src dst : Register) (d : Data M) :
    (compare M src dst).guard w bound d ∧
    (compare M src dst).result w d =
      ⟨{d.state with
          value := none
          other := none
          flag := decide (d.store (SearchProgram.key src) = d.store (SearchProgram.key dst))}, d.inputHead,
        Function.update (Function.update (Function.update d.store (GraphQuery.key .aux) [])
          (GraphQuery.key .left) []) (GraphQuery.key .right) []⟩ := by
  constructor
  · simp [compare, Macro.seq, Macro.clear, Macro.copy, Macro.compare,
      StackRoutines.cleared, GraphQuery.key, SearchProgram.key]
  · simp only [compare, Macro.seq, Macro.clear, Macro.copy, Macro.compare, StackRoutines.cleared]
    congr 1
    · simp [GraphQuery.key, SearchProgram.key]
    · funext k
      by_cases h₁ : k = GraphQuery.key .aux <;>
        by_cases h₂ : k = GraphQuery.key .left <;>
        by_cases h₃ : k = GraphQuery.key .right <;>
        simp_all [Function.update_apply, GraphQuery.key, SearchProgram.key]

end

end Lax733996Proofs.CountingProgram
