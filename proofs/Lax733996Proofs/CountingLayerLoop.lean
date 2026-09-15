import Lax733996Proofs.CountingLayerState

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax733996Proofs.ConfigurationProofs
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

lemma layerLoop_total (w : Word) (bound m k i : ℕ) (hk : k < 2 ^ m) (hi : i ≤ 2 ^ m)
    (hm : m + 1 < bound) (d : Data M) (hd : LayerState M w bound m k i d) :
    Total w bound (layerLoop M) d := by
  apply ChoiceLanguage.bounded_loop_total w bound (2 ^ m) (running M) (layerStep M)
    (fun j e => LayerState M w bound m k j e) (fun _ _ h => h.good)
    (fun e h => layerClock_stop M m e h.clock) ?_ ?_ i d hi hd
  · intro j e hj he _
    exact layerState_body_total M w bound m k j hk hj hm e he
  · intro j e f hj he _ hbody
    exact (layerState_step M w bound m k j hk hj hm e f he hbody).1

lemma layerLoop_sound (w : Word) (bound m k i : ℕ) (hk : k < 2 ^ m) (hi : i ≤ 2 ^ m)
    (hm : m + 1 < bound) (d e : Data M) (hd : LayerState M w bound m k i d)
    (h : Exec w bound (layerLoop M) d e) :
    Keeps layerWrites d e ∧
      (valid M e.state = true → valid M d.state = true ∧ LayerState M w bound m k (2 ^ m) e) := by
  let I := fun j f => LayerState M w bound m k j f ∧ Keeps layerWrites d f ∧
    (valid M f.state = true → valid M d.state = true)
  have hnext : ∀ j f g, j < 2 ^ m → I j f → running M f.state = true →
      Exec w bound (layerStep M) f g → I (j + 1) g := by
    intro j f g hj ⟨hf, hkf, hlf⟩ _ he
    obtain ⟨hg, hkg, hlg⟩ := layerState_step M w bound m k j hk hj hm f g hf he
    exact ⟨hg, hkf.trans hkg, fun hl => hlf (hlg hl)⟩
  obtain ⟨⟨j, hj, hje, hkeep, hlive⟩, hstop⟩ := ChoiceLanguage.bounded_loop_sound w bound (2 ^ m)
    (running M) (layerStep M) I (fun f hf => layerClock_stop M m f hf.1.clock) hnext
    i d e hi ⟨hd, Keeps.refl _ _, fun hl => hl⟩ h
  refine ⟨hkeep, fun hl => ⟨hlive hl, ?_⟩⟩
  have heq : j = 2 ^ m := by
    by_contra hn
    have hlt : j < 2 ^ m := by omega
    rw [layerClock_running M m j hlt e hje.clock, hl] at hstop
    contradiction
  exact heq ▸ hje

lemma layerLoop_complete (w : Word) (bound m k i : ℕ) (hk : k < 2 ^ m) (hi : i ≤ 2 ^ m)
    (hm : m + 1 < bound) (d : Data M) (hd : LayerState M w bound m k i d) (hl : valid M d.state = true) :
    ∃ e, Exec w bound (layerLoop M) d e ∧ LayerState M w bound m k (2 ^ m) e ∧ valid M e.state = true := by
  let I := fun j f => LayerState M w bound m k j f ∧ valid M f.state = true
  have hstep : ∀ j f, j < 2 ^ m → I j f → running M f.state = true ∧
      ∃ g, Exec w bound (layerStep M) f g ∧ I (j + 1) g := by
    intro j f hj ⟨hf, hfl⟩
    exact ⟨(layerClock_running M m j hj f hf.clock).trans hfl,
      layerState_complete_step M w bound m k j hk hj hm f hf hfl⟩
  exact ChoiceLanguage.bounded_loop_complete w bound (2 ^ m) (running M) (layerStep M) I
    (fun _ _ h => h.1.good) (fun f h => layerClock_stop M m f h.1.clock) hstep i d hi ⟨hd, hl⟩

end

end Lax733996Proofs.CountingProgram
