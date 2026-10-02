import Lax362205Proofs.CountingCensusStep
import Lax362205Proofs.BoundedLoop

namespace Lax362205Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax362205Proofs.ConfigurationProofs
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

structure CensusState (w : Word) (bound m k i : ℕ) (v : Fin (2 ^ m)) (d : Data M) : Prop where
  good : Good w bound d
  width : reg d .width = SearchProgram.unary m
  depth : reg d .depth = SearchProgram.word m k
  target : reg d .frameB = SearchProgram.word m v.val
  clock : CensusClock M m i d
  progress : CensusProgress M w m k i v d

lemma census_count_bound (w : Word) (m k i : ℕ) (v : Fin (2 ^ m)) (d : Data M)
    (hi : i ≤ 2 ^ m) (h : CensusProgress M w m k i v d) :
    ∃ c, c < 2 ^ (m + 1) ∧ reg d .frameDepth = SearchProgram.word (m + 1) c ∧
      StreamingCensus.Invariant (EncodedGraph.graph M w m) (EncodedGraph.first m) v k i c d.state.user.overflow := by
  obtain ⟨c, hc, hI⟩ := h
  have hci := StreamingCensus.count_le _ _ v k i c _ hI
  have hpos : 0 < 2 ^ m := by positivity
  refine ⟨c, ?_, hc, hI⟩
  rw [pow_succ]
  omega

lemma censusState_body_total (w : Word) (bound m k i : ℕ) (hk : k < 2 ^ m) (hi : i < 2 ^ m)
    (hm : m + 1 < bound) (v : Fin (2 ^ m)) (d : Data M) (hd : CensusState M w bound m k i v d) :
    Total w bound (censusStep M) d := by
  obtain ⟨c, hc, hcnt, _⟩ := census_count_bound M w m k i v d (by omega) hd.progress
  exact censusStep_total M w bound m k i c hk hi hc d hd.good hd.width hd.depth hm v hd.clock.1 hd.target hcnt

lemma censusState_step (w : Word) (bound m k i : ℕ) (hk : k < 2 ^ m) (hi : i < 2 ^ m)
    (hm : m + 1 < bound) (v : Fin (2 ^ m)) (d e : Data M) (hd : CensusState M w bound m k i v d)
    (h : Exec w bound (censusStep M) d e) :
    CensusState M w bound m k (i + 1) v e ∧ Keeps censusWrites d e ∧
      (valid M e.state = true → valid M d.state = true) := by
  obtain ⟨c, hc, hcnt, hI⟩ := census_count_bound M w m k i v d (by omega) hd.progress
  obtain ⟨hclock, hkeep, hlive, hprogress⟩ := censusStep_sound M w bound m k i c hk hi hc
    d e hd.good hd.width hd.depth hm v hd.clock.1 hd.target hcnt hI h
  exact ⟨⟨h.good.2, (hkeep .width (by simp [censusWrites])).trans hd.width,
    (hkeep .depth (by simp [censusWrites])).trans hd.depth,
    (hkeep .frameB (by simp [censusWrites])).trans hd.target, hclock, hprogress⟩, hkeep, hlive⟩

end

end Lax362205Proofs.CountingProgram
