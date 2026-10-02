import Lax362205Proofs.CountingCensusLoop

namespace Lax362205Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax362205Proofs.ConfigurationProofs
open Lax362205.Counting
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

def canonicalCount (w : Word) (m k i : ℕ) : ℕ :=
  (Lax362205.Counting.layer (EncodedGraph.graph M w m) (EncodedGraph.first m) k ∩ StreamingCensus.visited (2 ^ m) i).card

lemma canonicalCount_bound (w : Word) (m k i : ℕ) : canonicalCount M w m k i < 2 ^ (m + 1) := by
  have hle := Finset.card_le_univ (s := Lax362205.Counting.layer (EncodedGraph.graph M w m) (EncodedGraph.first m) k ∩
    StreamingCensus.visited (2 ^ m) i)
  simp only [Fintype.card_fin] at hle
  have hp : 0 < 2 ^ m := by positivity
  dsimp [canonicalCount]
  rw [pow_succ]
  omega

lemma censusState_complete_step (w : Word) (bound m k i : ℕ) (hk : k < 2 ^ m) (hi : i < 2 ^ m)
    (hm : m + 1 < bound) (v : Fin (2 ^ m)) (d : Data M) (hd : CensusState M w bound m k i v d)
    (hcnt : reg d .frameDepth = SearchProgram.word (m + 1) (canonicalCount M w m k i))
    (hl : valid M d.state = true) :
    ∃ e, Exec w bound (censusStep M) d e ∧ CensusState M w bound m k (i + 1) v e ∧
      reg e .frameDepth = SearchProgram.word (m + 1) (canonicalCount M w m k (i + 1)) ∧ valid M e.state = true := by
  have hnext := StreamingCensus.canonical_card_next (EncodedGraph.graph M w m) (EncodedGraph.first m) k i hi
  change canonicalCount M w m k (i + 1) = canonicalCount M w m k i + _ at hnext
  by_cases hmem : (⟨i, hi⟩ : Fin (2 ^ m)) ∈ Lax362205.Counting.layer (EncodedGraph.graph M w m) (EncodedGraph.first m) k
  · obtain ⟨e, he, hcnt', hel⟩ := censusStep_take M w bound m k i (canonicalCount M w m k i) hk hi
      (canonicalCount_bound M w m k i) d hd.good hd.width hd.depth hm v hd.clock.1 hd.target hcnt hl
      ((mem_layer _ _ _ k).mp hmem)
    refine ⟨e, he, (censusState_step M w bound m k i hk hi hm v d e hd he).1, ?_, hel⟩
    simpa only [hnext, if_pos hmem] using hcnt'
  · obtain ⟨e, he, hcnt', hel⟩ := censusStep_skip M w bound m i (canonicalCount M w m k i)
      hi d hd.good hd.clock.1 hcnt
    refine ⟨e, he, (censusState_step M w bound m k i hk hi hm v d e hd he).1, ?_, hel.trans hl⟩
    simpa only [hnext, if_neg hmem, Nat.add_zero] using hcnt'

lemma censusLoop_complete (w : Word) (bound m k i : ℕ) (hk : k < 2 ^ m) (hi : i ≤ 2 ^ m)
    (hm : m + 1 < bound) (v : Fin (2 ^ m)) (d : Data M) (hd : CensusState M w bound m k i v d)
    (hcnt : reg d .frameDepth = SearchProgram.word (m + 1) (canonicalCount M w m k i))
    (hl : valid M d.state = true) :
    ∃ e, Exec w bound (censusLoop M) d e ∧ CensusState M w bound m k (2 ^ m) v e ∧
      reg e .frameDepth = SearchProgram.word (m + 1) (Lax362205.Counting.layer (EncodedGraph.graph M w m) (EncodedGraph.first m) k).card ∧
      valid M e.state = true := by
  let I := fun j f => CensusState M w bound m k j v f ∧
    reg f .frameDepth = SearchProgram.word (m + 1) (canonicalCount M w m k j) ∧ valid M f.state = true
  have hstep : ∀ j f, j < 2 ^ m → I j f → running M f.state = true ∧
      ∃ g, Exec w bound (censusStep M) f g ∧ I (j + 1) g := by
    intro j f hj ⟨hf, hfc, hfl⟩
    refine ⟨(censusClock_running M m j hj f hf.clock).trans hfl, ?_⟩
    exact censusState_complete_step M w bound m k j hk hj hm v f hf hfc hfl
  obtain ⟨e, he, hstate, hcount, hel⟩ := ChoiceLanguage.bounded_loop_complete w bound (2 ^ m)
    (running M) (censusStep M) I (fun _ _ h => h.1.good)
    (fun f h => censusClock_stop M m f h.1.clock) hstep i d hi ⟨hd, hcnt, hl⟩
  refine ⟨e, he, hstate, ?_, hel⟩
  simpa only [canonicalCount, StreamingCensus.canonical_final] using hcount

end

end Lax362205Proofs.CountingProgram
