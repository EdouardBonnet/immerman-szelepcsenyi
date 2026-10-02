import Lax362205Proofs.CountingSelect
import Lax362205Proofs.StreamingCensus

namespace Lax362205Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax362205Proofs.ConfigurationProofs
open Lax362205.Reachability
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

def censusWrites : Finset SearchProgram.Register := {.a, .b, .kinds, .aux, .frameDepth, .frameMiddle}

def CensusClock (m i : ℕ) (d : Data M) : Prop :=
  reg d .frameMiddle = SearchProgram.word m i ∧ d.state.flag = decide (i = 2 ^ m)

lemma censusClock_stop (m : ℕ) (d : Data M) (hc : CensusClock M m (2 ^ m) d) :
    running M d.state = false := by simp [running, hc.2]

lemma censusClock_running (m i : ℕ) (hi : i < 2 ^ m) (d : Data M) (hc : CensusClock M m i d) :
    running M d.state = valid M d.state := by simp [running, hc.2, Nat.ne_of_lt hi]

def CensusProgress (w : Word) (m k i : ℕ) (v : Fin (2 ^ m)) (d : Data M) : Prop :=
  ∃ c, reg d .frameDepth = SearchProgram.word (m + 1) c ∧
    StreamingCensus.Invariant (EncodedGraph.graph M w m) (EncodedGraph.first m) v k i c d.state.user.overflow

lemma censusStep_total (w : Word) (bound m k i c : ℕ) (hk : k < 2 ^ m) (hi : i < 2 ^ m)
    (hc : c < 2 ^ (m + 1)) (d : Data M) (hd : Good w bound d)
    (hw : reg d .width = SearchProgram.unary m) (hdepth : reg d .depth = SearchProgram.word m k)
    (hm : m + 1 < bound) (v : Fin (2 ^ m)) (hu : reg d .frameMiddle = SearchProgram.word m i)
    (hv : reg d .frameB = SearchProgram.word m v.val)
    (hcnt : reg d .frameDepth = SearchProgram.word (m + 1) c) :
    Total w bound (censusStep M) d := by
  apply Total.seq (censusSelect_total M w bound m k c hk hc d hd hw hdepth hm ⟨i, hi⟩ v hu hv hcnt)
  intro f hf
  obtain ⟨hkeep, _, _⟩ := censusSelect_sound M w bound m k c hk hc d f hd hw hdepth hm ⟨i, hi⟩ v hu hv hcnt hf
  have hfu : reg f .frameMiddle = SearchProgram.word m i := (hkeep .frameMiddle (by simp [censusTakeWrites])).trans hu
  exact .det ((increment M .frameMiddle).correct w bound f hf.good.2
    (increment_spec M w bound m i hi .frameMiddle f hfu).1)

lemma censusStep_sound (w : Word) (bound m k i c : ℕ) (hk : k < 2 ^ m) (hi : i < 2 ^ m)
    (hc : c < 2 ^ (m + 1)) (d e : Data M) (hd : Good w bound d)
    (hw : reg d .width = SearchProgram.unary m) (hdepth : reg d .depth = SearchProgram.word m k)
    (hm : m + 1 < bound) (v : Fin (2 ^ m)) (hu : reg d .frameMiddle = SearchProgram.word m i)
    (hv : reg d .frameB = SearchProgram.word m v.val)
    (hcnt : reg d .frameDepth = SearchProgram.word (m + 1) c)
    (hI : StreamingCensus.Invariant (EncodedGraph.graph M w m) (EncodedGraph.first m) v k i c d.state.user.overflow)
    (h : Exec w bound (censusStep M) d e) :
    CensusClock M m (i + 1) e ∧ Keeps censusWrites d e ∧
      (valid M e.state = true → valid M d.state = true) ∧ CensusProgress M w m k (i + 1) v e := by
  cases h with
  | @seq _ _ _ f _ hs he =>
    obtain ⟨hkeep, hlive, hcases⟩ := censusSelect_sound M w bound m k c hk hc d f hd hw hdepth hm ⟨i, hi⟩ v hu hv hcnt hs
    have hfu : reg f .frameMiddle = SearchProgram.word m i := (hkeep .frameMiddle (by simp [censusTakeWrites])).trans hu
    have he₀ := (increment M .frameMiddle).correct w bound f hs.good.2
      (increment_spec M w bound m i hi .frameMiddle f hfu).1
    obtain rfl := (ChoiceLanguage.det_exec_iff he₀).mp he
    obtain ⟨hkeep', hidx, huser, hflag⟩ := increment_effect w bound m i hi .frameMiddle f hfu
    refine ⟨⟨hidx, hflag⟩, ?_, ?_, ?_⟩
    · exact (hkeep.mono (by intro r hr; simp [censusTakeWrites, censusWrites] at hr ⊢; tauto)).trans
        (hkeep'.mono (by intro r hr; simp [censusWrites] at hr ⊢; tauto))
    · simpa only [valid, huser] using hlive
    · rcases hcases with ⟨hcnt', hfound⟩ | ⟨hcnt', hfound, hreach⟩
      · refine ⟨c, (hkeep' .frameDepth (by simp)).trans hcnt', ?_⟩
        simpa only [huser, hfound] using StreamingCensus.skip _ _ v k i c _ hI
      · refine ⟨c + 1, (hkeep' .frameDepth (by simp)).trans hcnt', ?_⟩
        simpa only [huser, hfound] using StreamingCensus.take _ _ v k i c _ hI hi hreach

lemma censusStep_skip (w : Word) (bound m i c : ℕ) (hi : i < 2 ^ m)
    (d : Data M) (hd : Good w bound d) (hu : reg d .frameMiddle = SearchProgram.word m i)
    (hcnt : reg d .frameDepth = SearchProgram.word (m + 1) c) :
    ∃ e, Exec w bound (censusStep M) d e ∧
      reg e .frameDepth = SearchProgram.word (m + 1) c ∧ valid M e.state = valid M d.state := by
  let f := StackLanguage.assigned d {d.state with flag := false}
  have hs : Exec w bound (censusSelect M) d f := censusSelect_skip M w bound d hd
  have he := (increment M .frameMiddle).correct w bound f hd
    (increment_spec M w bound m i hi .frameMiddle f hu).1
  obtain ⟨hkeep, _, huser, _⟩ := increment_effect w bound m i hi .frameMiddle f hu
  refine ⟨_, .seq hs (.det he), (hkeep .frameDepth (by simp)).trans hcnt, ?_⟩
  unfold valid
  rw [huser]
  rfl

lemma censusStep_take (w : Word) (bound m k i c : ℕ) (hk : k < 2 ^ m) (hi : i < 2 ^ m)
    (hc : c < 2 ^ (m + 1)) (d : Data M) (hd : Good w bound d)
    (hw : reg d .width = SearchProgram.unary m) (hdepth : reg d .depth = SearchProgram.word m k)
    (hm : m + 1 < bound) (v : Fin (2 ^ m)) (hu : reg d .frameMiddle = SearchProgram.word m i)
    (hv : reg d .frameB = SearchProgram.word m v.val)
    (hcnt : reg d .frameDepth = SearchProgram.word (m + 1) c) (hl : valid M d.state = true)
    (hreach : Within (fun x y => EncodedGraph.graph M w m x y = true) k (EncodedGraph.first m) ⟨i, hi⟩) :
    ∃ e, Exec w bound (censusStep M) d e ∧
      reg e .frameDepth = SearchProgram.word (m + 1) (c + 1) ∧ valid M e.state = true := by
  obtain ⟨f, hs, hkeep, hcnt', _, hfl⟩ := censusSelect_take M w bound m k c hk hc d hd hw hdepth hm ⟨i, hi⟩ v hu hv hcnt hl hreach
  have hfu : reg f .frameMiddle = SearchProgram.word m i := (hkeep .frameMiddle (by simp [censusTakeWrites])).trans hu
  have he := (increment M .frameMiddle).correct w bound f hs.good.2
    (increment_spec M w bound m i hi .frameMiddle f hfu).1
  obtain ⟨hkeep', _, huser, _⟩ := increment_effect w bound m i hi .frameMiddle f hfu
  refine ⟨_, .seq hs (.det he), (hkeep' .frameDepth (by simp)).trans hcnt', ?_⟩
  simpa only [valid, huser] using hfl

end

end Lax362205Proofs.CountingProgram
