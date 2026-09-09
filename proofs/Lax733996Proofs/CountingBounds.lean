import Lax733996Proofs.CountingProgram
import Lax733996Proofs.Complement

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930.SpaceBounds
open Lax307052Proofs Lax307052.Reachability
open scoped Classical

noncomputable section

def wordWidth (M : Machine) (c n : ℕ) : ℕ :=
  letterWidth M * ((c * logSpace n + 1) + c * logSpace n + 2)

def spaceBound (M : Machine) (c n : ℕ) : ℕ := wordWidth M c n + 3

def spaceFactor (M : Machine) (c : ℕ) : ℕ := 2 * letterWidth M * c + 3 * letterWidth M + 3

lemma log_pos (n : ℕ) : 0 < logSpace n := by
  apply Nat.lt_of_lt_of_le (by decide : 0 < 1)
  exact Nat.le_log_of_pow_le (by decide) (by simp)

lemma letterWidth_ge (M : Machine) : 2 ≤ letterWidth M := by
  simp [letterWidth, FiniteCoding.width]

lemma spaceFactor_pos (M : Machine) (c : ℕ) : 0 < spaceFactor M c := by
  unfold spaceFactor
  omega

lemma width_eq (M : Machine) (c n : ℕ) :
    wordWidth M c n = (2 * letterWidth M * c) * logSpace n + 3 * letterWidth M := by
  unfold wordWidth
  ring

lemma bound_le (M : Machine) (c n : ℕ) : spaceBound M c n ≤ spaceFactor M c * logSpace n := by
  have hlog : 1 ≤ logSpace n := log_pos n
  have hh := Nat.mul_le_mul_left (3 * letterWidth M + 3) hlog
  dsimp only [spaceBound, spaceFactor]
  rw [width_eq]
  nlinarith

lemma initialization_bound (M : Machine) (c n : ℕ) (hc : 0 < c) :
    logSpace n + 2 < spaceBound M c n := by
  have hr := letterWidth_ge M
  have hl := log_pos n
  have hm : logSpace n ≤ c * logSpace n := by nlinarith
  have hh : c * logSpace n ≤ letterWidth M * (c * logSpace n) := by nlinarith
  unfold spaceBound wordWidth
  nlinarith

lemma input_width (c n : ℕ) (hc : 0 < c) : n + 1 < 2 ^ (c * logSpace n + 1) := by
  have hl := log_pos n
  have hpow := Nat.lt_pow_succ_log_self (b := 2) (by decide) (n + 2)
  have hm : logSpace n + 1 ≤ c * logSpace n + 1 := by nlinarith
  have he := Nat.pow_le_pow_right (by decide : 0 < 2) hm
  change 2 ^ (logSpace n + 1) ≤ _ at he
  change n + 2 < 2 ^ (logSpace n + 1) at hpow
  omega

lemma graph_acceptance (M : Machine) (c : ℕ) (hc : 0 < c) (w : Word)
    (hs : M.UsesSpace w (c * logSpace w.length)) :
    Reachable (EncodedGraph.graph M w (wordWidth M c w.length)) (EncodedGraph.first _) (EncodedGraph.last _) ↔
      M.Accepts w := by
  constructor
  · exact EncodedGraph.reachable_sound M w _ (by omega)
  · exact EncodedGraph.reachable_complete M w _ _ (input_width c w.length hc) hs

lemma graph_rejection (M : Machine) (c : ℕ) (hc : 0 < c) (w : Word)
    (hs : M.UsesSpace w (c * logSpace w.length)) :
    (¬ Reachable (EncodedGraph.graph M w (wordWidth M c w.length)) (EncodedGraph.first _) (EncodedGraph.last _)) ↔
      Lax733996.ConfigurationCounting.RejectsByCounting M w (c * logSpace w.length) := by
  exact (not_congr (graph_acceptance M c hc w hs)).trans (counting_rejection M w _ hs).symm

end

end Lax733996Proofs.CountingProgram
