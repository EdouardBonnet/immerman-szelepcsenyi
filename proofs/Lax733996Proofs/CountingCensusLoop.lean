import Lax733996Proofs.CountingCensusState

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax307052Proofs
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

lemma censusLoop_total (w : Word) (bound m k i : ℕ) (hk : k < 2 ^ m) (hi : i ≤ 2 ^ m)
    (hm : m + 1 < bound) (v : Fin (2 ^ m)) (d : Data M) (hd : CensusState M w bound m k i v d) :
    Total w bound (censusLoop M) d := by
  apply ChoiceLanguage.bounded_loop_total w bound (2 ^ m) (running M) (censusStep M)
    (fun j e => CensusState M w bound m k j v e) (fun _ _ h => h.good)
    (fun e h => censusClock_stop M m e h.clock) ?_ ?_ i d hi hd
  · intro j e hj he _
    exact censusState_body_total M w bound m k j hk hj hm v e he
  · intro j e f hj he _ hbody
    exact (censusState_step M w bound m k j hk hj hm v e f he hbody).1

lemma censusLoop_sound (w : Word) (bound m k i : ℕ) (hk : k < 2 ^ m) (hi : i ≤ 2 ^ m)
    (hm : m + 1 < bound) (v : Fin (2 ^ m)) (d e : Data M) (hd : CensusState M w bound m k i v d)
    (h : Exec w bound (censusLoop M) d e) :
    Keeps censusWrites d e ∧
      (valid M e.state = true → valid M d.state = true ∧ CensusState M w bound m k (2 ^ m) v e) := by
  let I := fun j f => CensusState M w bound m k j v f ∧ Keeps censusWrites d f ∧
    (valid M f.state = true → valid M d.state = true)
  have hnext : ∀ j f g, j < 2 ^ m → I j f → running M f.state = true →
      Exec w bound (censusStep M) f g → I (j + 1) g := by
    intro j f g hj ⟨hf, hkf, hlf⟩ _ he
    obtain ⟨hg, hkg, hlg⟩ := censusState_step M w bound m k j hk hj hm v f g hf he
    exact ⟨hg, hkf.trans hkg, fun hl => hlf (hlg hl)⟩
  obtain ⟨⟨j, hj, hje, hkeep, hlive⟩, hstop⟩ := ChoiceLanguage.bounded_loop_sound w bound (2 ^ m)
    (running M) (censusStep M) I (fun f hf => censusClock_stop M m f hf.1.clock) hnext
    i d e hi ⟨hd, Keeps.refl _ _, fun hl => hl⟩ h
  refine ⟨hkeep, fun hl => ⟨hlive hl, ?_⟩⟩
  have heq : j = 2 ^ m := by
    by_contra hn
    have hlt : j < 2 ^ m := by omega
    rw [censusClock_running M m j hlt e hje.clock, hl] at hstop
    contradiction
  exact heq ▸ hje

end

end Lax733996Proofs.CountingProgram
