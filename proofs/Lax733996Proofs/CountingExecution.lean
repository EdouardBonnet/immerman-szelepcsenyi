import Lax733996Proofs.CountingProgramLoop
import Lax733996Proofs.CountingSetup

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax307052Proofs
open Lax307052.Reachability
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

lemma initialized_state (c : ℕ) (hc : 0 < c) (w : Word) :
    ∃ d : Data M, StackLanguage.Exec w (spaceBound M c w.length) (initializeCode M c)
        ⟨initial M, 0, fun _ => []⟩ d ∧
      ProgramState M w (spaceBound M c w.length) (wordWidth M c w.length) 0 d ∧ valid M d.state = true := by
  obtain ⟨d, he, hw, hcount, hdepth, huser, hflag, _⟩ := initialization M c hc w
  refine ⟨d, he, ⟨he.good.2, hw, hdepth, ?_, ?_⟩, ?_⟩
  · rw [hflag]
    simp [Nat.ne_of_lt (show 0 < 2 ^ wordWidth M c w.length by positivity)]
  · intro _
    refine ⟨?_, by omega⟩
    simpa only [layerCount, Lax733996Proofs.layer_zero, Finset.card_singleton] using hcount
  · simp [valid, huser, initial]

lemma program_total (c : ℕ) (hc : 0 < c) (w : Word) :
    Total w (spaceBound M c w.length) (program M c) ⟨initial M, 0, fun _ => []⟩ := by
  obtain ⟨d, he, hd, _⟩ := initialized_state M c hc w
  apply ChoiceLanguage.total_det_seq he
  exact programLoop_total M w (spaceBound M c w.length) (wordWidth M c w.length) 0 (Nat.zero_le _)
    (by unfold spaceBound; omega) d hd

lemma final_answer (w : Word) (bound m : ℕ) (d : Data M)
    (hd : ProgramState M w bound m (2 ^ m) d) (hl : valid M d.state = true) :
    (d.state.user.overflow = true ↔ Reachable (EncodedGraph.graph M w m) (EncodedGraph.first m) (EncodedGraph.last m)) := by
  have hf := (hd.progress hl).2 (by positivity)
  exact hf.trans (final_layer _ _ _)

lemma program_correct (c : ℕ) (hc : 0 < c) (w : Word) :
    (∃ e, Exec w (spaceBound M c w.length) (program M c) ⟨initial M, 0, fun _ => []⟩ e ∧
      (valid M e.state && !e.state.user.overflow) = true) ↔
      ¬ Reachable (EncodedGraph.graph M w (wordWidth M c w.length)) (EncodedGraph.first _) (EncodedGraph.last _) := by
  obtain ⟨d, hinitexec, hd, hl⟩ := initialized_state M c hc w
  have hm : wordWidth M c w.length + 1 < spaceBound M c w.length := by unfold spaceBound; omega
  constructor
  · rintro ⟨e, h, ha⟩
    have hsplit : valid M e.state = true ∧ (!e.state.user.overflow) = true := by
      simpa only [Bool.and_eq_true] using ha
    have hvalid := hsplit.1
    have hfalse := hsplit.2
    cases h with
    | seq hinit hloop =>
      obtain rfl := (ChoiceLanguage.det_exec_iff hinitexec).mp hinit
      have he := programLoop_sound M w _ _ 0 (Nat.zero_le _) hm _ e hd hloop hvalid
      intro hr
      have ht := (final_answer M w _ _ e he hvalid).mpr hr
      simp [ht] at hfalse
  · intro hn
    obtain ⟨e, hloop, he, hel⟩ := programLoop_complete M w _ _ 0 (Nat.zero_le _) hm d hd hl
    refine ⟨e, .seq (.det hinitexec) hloop, ?_⟩
    have hf : e.state.user.overflow ≠ true := fun ht => hn ((final_answer M w _ _ e he hel).mp ht)
    simp [hel, Bool.eq_false_iff.mpr hf]

end

end Lax733996Proofs.CountingProgram
