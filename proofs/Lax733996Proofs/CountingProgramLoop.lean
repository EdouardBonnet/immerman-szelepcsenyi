import Lax733996Proofs.CountingProgramState

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax733996Proofs.ConfigurationProofs
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

lemma programLoop_total (w : Word) (bound m k : ℕ) (hk : k ≤ 2 ^ m) (hm : m + 1 < bound)
    (d : Data M) (hd : ProgramState M w bound m k d) : Total w bound (programLoop M) d := by
  apply ChoiceLanguage.bounded_loop_total w bound (2 ^ m) (running M) (programBody M)
    (fun j e => ProgramState M w bound m j e) (fun _ _ h => h.good)
    (fun e h => programState_stop M w bound m e h) ?_ ?_ k d hk hd
  · intro j e hj he ht
    rw [programState_running M w bound m j hj e he] at ht
    exact programState_body_total M w bound m j hj hm e he ht
  · intro j e f hj he ht hbody
    rw [programState_running M w bound m j hj e he] at ht
    exact programState_step M w bound m j hj hm e f he ht hbody

lemma programLoop_sound (w : Word) (bound m k : ℕ) (hk : k ≤ 2 ^ m) (hm : m + 1 < bound)
    (d e : Data M) (hd : ProgramState M w bound m k d) (h : Exec w bound (programLoop M) d e)
    (hl : valid M e.state = true) : ProgramState M w bound m (2 ^ m) e := by
  let I := fun j f => ProgramState M w bound m j f
  have hnext : ∀ j f g, j < 2 ^ m → I j f → running M f.state = true →
      Exec w bound (programBody M) f g → I (j + 1) g := by
    intro j f g hj hf ht he
    rw [programState_running M w bound m j hj f hf] at ht
    exact programState_step M w bound m j hj hm f g hf ht he
  obtain ⟨⟨j, hj, hje⟩, hstop⟩ := ChoiceLanguage.bounded_loop_sound w bound (2 ^ m)
    (running M) (programBody M) I (fun f hf => programState_stop M w bound m f hf) hnext k d e hk hd h
  have heq : j = 2 ^ m := by
    by_contra hn
    have hlt : j < 2 ^ m := by omega
    rw [programState_running M w bound m j hlt e hje, hl] at hstop
    contradiction
  exact heq ▸ hje

lemma programLoop_complete (w : Word) (bound m k : ℕ) (hk : k ≤ 2 ^ m) (hm : m + 1 < bound)
    (d : Data M) (hd : ProgramState M w bound m k d) (hl : valid M d.state = true) :
    ∃ e, Exec w bound (programLoop M) d e ∧ ProgramState M w bound m (2 ^ m) e ∧ valid M e.state = true := by
  let I := fun j f => ProgramState M w bound m j f ∧ valid M f.state = true
  have hstep : ∀ j f, j < 2 ^ m → I j f → running M f.state = true ∧
      ∃ g, Exec w bound (programBody M) f g ∧ I (j + 1) g := by
    intro j f hj ⟨hf, hfl⟩
    exact ⟨(programState_running M w bound m j hj f hf).trans hfl,
      programState_complete_step M w bound m j hj hm f hf hfl⟩
  exact ChoiceLanguage.bounded_loop_complete w bound (2 ^ m) (running M) (programBody M) I
    (fun _ _ h => h.1.good) (fun f h => programState_stop M w bound m f h.1) hstep k d hk ⟨hd, hl⟩

end

end Lax733996Proofs.CountingProgram
