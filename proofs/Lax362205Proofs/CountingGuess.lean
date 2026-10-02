import Lax362205Proofs.CountingFrames

namespace Lax362205Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax362205Proofs.ConfigurationProofs
open SearchProgram (Register)
open StackMacros (Macro)
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

variable (M : Machine)

lemma guessSetup_spec (w : Word) (bound m : ℕ) (dst : Register)
    (hdw : dst ≠ .width) (hda : dst ≠ .aux) (d : Data M)
    (hw : reg d .width = SearchProgram.unary m) :
    (guessSetup M dst).guard w bound d ∧
      reg ((guessSetup M dst).result w d) .aux = SearchProgram.unary m ∧
      reg ((guessSetup M dst).result w d) dst = [] ∧
      Keeps {dst, .aux} d ((guessSetup M dst).result w d) ∧
      ((guessSetup M dst).result w d).state.user = d.state.user := by
  let dc := (Macro.clear (SearchProgram.key dst) : Routine M).result w d
  have hc := copy_spec M w bound .width .aux (by decide) dc
  refine ⟨⟨trivial, hc.1⟩, ?_, ?_, ?_, ?_⟩
  all_goals change _
  all_goals dsimp only [guessSetup, Macro.seq]; change _ at hc
  all_goals rw [hc.2]
  · simpa [reg, dc, Macro.clear, StackRoutines.cleared, GraphQuery.key, SearchProgram.key,
      Ne.symm hdw] using hw
  · simp [reg, dc, Macro.clear, StackRoutines.cleared, GraphQuery.key, SearchProgram.key, hda]
  · intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
    simp [reg, dc, Macro.clear, StackRoutines.cleared, GraphQuery.key, SearchProgram.key, hr.1, hr.2]
  · rfl

lemma guess_total (w : Word) (bound m : ℕ) (dst : Register)
    (hdw : dst ≠ .width) (hda : dst ≠ .aux) (d : Data M)
    (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m) :
    Total w bound (guess M dst) d := by
  obtain ⟨hg, hs, ht, _, _⟩ := guessSetup_spec M w bound m dst hdw hda d hw
  have he := (guessSetup M dst).correct w bound d hd hg
  apply ChoiceLanguage.total_det_seq he
  apply GuessWord.total w bound _ _ (by simpa [SearchProgram.key] using Ne.symm hda)
    SearchProgram.bit _ he.good.2
  change (reg _ .aux).length + (reg _ dst).length < bound
  rw [hs, ht]
  simpa [← hw] using hd.2 (SearchProgram.key .width)

def GuessPost (m : ℕ) (dst : Register) (d e : Data M) (x : Fin (2 ^ m)) : Prop :=
  reg e dst = SearchProgram.word m x.val ∧ Keeps {dst, .aux} d e ∧
    e.state.user = d.state.user

lemma guess_result (w : Word) (bound m : ℕ) (dst : Register)
    (hdw : dst ≠ .width) (hda : dst ≠ .aux) (d : Data M)
    (hw : reg d .width = SearchProgram.unary m) (xs : List Bool) (hx : xs.length = m) :
    GuessPost M m dst d
      (GuessWord.result ((guessSetup M dst).result w d) (SearchProgram.key .aux)
        (SearchProgram.key dst) SearchProgram.bit xs)
      ⟨BinaryCounter.value xs.reverse, by simpa [hx] using BinaryCounter.value_lt xs.reverse⟩ := by
  obtain ⟨_, _, ht, hk, hu⟩ := guessSetup_spec M w bound m dst hdw hda d hw
  refine ⟨?_, ?_, hu⟩
  · change _ = (BinaryCounter.word m (BinaryCounter.value xs.reverse)).map SearchProgram.bit
    rw [← hx, ← List.length_reverse (as := xs), BinaryCounter.word_of_value]
    simp [reg, GuessWord.result, ht]
  · intro r hr
    have hn := hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simpa [reg, GuessWord.result, SearchProgram.key, hn.1, hn.2] using hk r hr

lemma guess_sound (w : Word) (bound m : ℕ) (dst : Register)
    (hdw : dst ≠ .width) (hda : dst ≠ .aux) (d e : Data M)
    (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (h : Exec w bound (guess M dst) d e) :
    ∃ x : Fin (2 ^ m), GuessPost M m dst d e x := by
  obtain ⟨hg, hs, ht, _, _⟩ := guessSetup_spec M w bound m dst hdw hda d hw
  have he := (guessSetup M dst).correct w bound d hd hg
  cases h with
  | seq hp hg =>
    obtain rfl := (ChoiceLanguage.det_exec_iff he).mp hp
    have hb : (reg ((guessSetup M dst).result w d) .aux).length +
        (reg ((guessSetup M dst).result w d) dst).length < bound := by
      rw [hs, ht]
      simpa [← hw] using hd.2 (SearchProgram.key .width)
    obtain ⟨xs, hxs, rfl⟩ := GuessWord.execution_sound w bound _ _
      (by simpa [SearchProgram.key] using Ne.symm hda) SearchProgram.bit _ _ he.good.2 hb hg
    have hx : xs.length = m := by simpa [hs] using hxs
    exact ⟨_, guess_result M w bound m dst hdw hda d hw xs hx⟩

lemma guess_complete (w : Word) (bound m : ℕ) (dst : Register)
    (hdw : dst ≠ .width) (hda : dst ≠ .aux) (d : Data M)
    (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (x : Fin (2 ^ m)) : ∃ e, Exec w bound (guess M dst) d e ∧ GuessPost M m dst d e x := by
  obtain ⟨hg, hs, ht, _, _⟩ := guessSetup_spec M w bound m dst hdw hda d hw
  have he := (guessSetup M dst).correct w bound d hd hg
  let xs := (BinaryCounter.word m x.val).reverse
  have hx : xs.length = m := by simp [xs]
  have hxs : xs.length = (reg ((guessSetup M dst).result w d) .aux).length := by simp [hx, hs]
  have hb : (reg ((guessSetup M dst).result w d) .aux).length +
      (reg ((guessSetup M dst).result w d) dst).length < bound := by
    rw [hs, ht]
    simpa [← hw] using hd.2 (SearchProgram.key .width)
  have hguess := GuessWord.execution w bound _ _ (by simpa [SearchProgram.key] using Ne.symm hda)
    SearchProgram.bit _ he.good.2 hb xs hxs
  refine ⟨_, .seq (.det he) hguess, ?_⟩
  have hpost := guess_result M w bound m dst hdw hda d hw xs hx
  have hxval : (⟨BinaryCounter.value xs.reverse, by simpa [hx] using BinaryCounter.value_lt xs.reverse⟩ : Fin (2 ^ m)) = x := by
    apply Fin.ext
    simp [xs, BinaryCounter.word_value, Nat.mod_eq_of_lt x.isLt]
  exact hxval ▸ hpost

end

end Lax362205Proofs.CountingProgram
