import Lax362205Proofs.CountingExecution

namespace Lax362205Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930.SpaceBounds Lax362205Proofs.ConfigurationProofs
open Lax362205.Reachability
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

lemma machine_spec (M : Machine) (c : ℕ) (hc : 0 < c) (w : Word) :
    (machine M c).HaltsOn w ∧ (machine M c).UsesSpace w (spaceBound M c w.length) ∧
      ((machine M c).Accepts w ↔
        ¬ Reachable (EncodedGraph.graph M w (wordWidth M c w.length)) (EncodedGraph.first _) (EncodedGraph.last _)) := by
  have hh := ChoiceLanguage.machine_total (program M c) (initial M)
    (fun s => valid M s && !s.user.overflow) w (spaceBound M c w.length)
    (by unfold spaceBound; omega) (program_total M c hc w)
  exact ⟨hh.1, hh.2.1, hh.2.2.trans (program_correct M c hc w)⟩

/--
---
conclusion: Lax362205.CountMachine.implement
assumptions:
  - Lax362205.Nonreachability.correct
---
Compile the sequential path and census loops to a finite Turing machine.
Every branch halts and every register has logarithmic length.
-/
lemma counting_machine_implementation (M : Machine) (c : ℕ) (hc : 0 < c)
    (hM : ∀ w, M.UsesSpace w (c * logSpace w.length)) :
    ∃ (d : ℕ) (D : Machine), 0 < d ∧
      (∀ w, D.HaltsOn w ∧ (D.Accepts w ↔ Lax362205.ConfigurationCounting.RejectsByCounting M w (c * logSpace w.length))) ∧
      ∀ w, D.UsesSpace w (d * logSpace w.length) := by
  refine ⟨spaceFactor M c, machine M c, spaceFactor_pos M c, ?_, ?_⟩
  · intro w
    have hh := machine_spec M c hc w
    exact ⟨hh.1, hh.2.2.trans (graph_rejection M c hc w (hM w))⟩
  · intro w n q hrun
    exact ((machine_spec M c hc w).2.1 n q hrun).trans_le (bound_le M c w.length)

end

end Lax362205Proofs.CountingProgram
