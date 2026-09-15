import Lax733996Proofs.CountingCensusComplete
import Lax733996Proofs.CountingCensusSetup

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax733996Proofs.ConfigurationProofs
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

lemma censusSetup_state (w : Word) (bound m k : ℕ) (d : Data M) (hd : Good w bound d)
    (hw : reg d .width = SearchProgram.unary m) (hdepth : reg d .depth = SearchProgram.word m k)
    (v : Fin (2 ^ m)) (hv : reg d .frameB = SearchProgram.word m v.val) (hm : m + 1 < bound) :
    CensusState M w bound m k 0 v ((censusSetup M).result w d) ∧
      reg ((censusSetup M).result w d) .frameDepth = SearchProgram.word (m + 1) (canonicalCount M w m k 0) ∧
      Keeps censusWrites d ((censusSetup M).result w d) ∧
      valid M ((censusSetup M).result w d).state = valid M d.state := by
  obtain ⟨hg, hclock, hcnt, hkeep, hlive, hfound⟩ := censusSetup_spec M w bound m d v hw hv hm
  have he := (censusSetup M).correct w bound d hd hg
  refine ⟨⟨he.good.2, (hkeep .width (by simp [censusWrites])).trans hw,
    (hkeep .depth (by simp [censusWrites])).trans hdepth,
    (hkeep .frameB (by simp [censusWrites])).trans hv, hclock, ⟨0, hcnt, ?_⟩⟩, ?_, hkeep, hlive⟩
  · simpa only [hfound] using StreamingCensus.initial (EncodedGraph.graph M w m) (EncodedGraph.first m) v k
  · simpa only [canonicalCount, StreamingCensus.canonical_zero, Finset.card_empty] using hcnt

def CensusPost (w : Word) (m k : ℕ) (v : Fin (2 ^ m)) (d e : Data M) : Prop :=
  Keeps censusWrites d e ∧ (valid M e.state = true → valid M d.state = true ∧
    (e.state.user.overflow = true ↔ v ∈ Lax733996.Counting.layer (EncodedGraph.graph M w m) (EncodedGraph.first m) (k + 1)))

lemma census_total (w : Word) (bound m k : ℕ) (hk : k < 2 ^ m)
    (d : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (hdepth : reg d .depth = SearchProgram.word m k) (v : Fin (2 ^ m))
    (hv : reg d .frameB = SearchProgram.word m v.val) (hm : m + 1 < bound) :
    Total w bound (census M) d := by
  have he := (censusSetup M).correct w bound d hd (censusSetup_spec M w bound m d v hw hv hm).1
  obtain ⟨hstate, _, _, _⟩ := censusSetup_state M w bound m k d hd hw hdepth v hv hm
  apply ChoiceLanguage.total_det_seq he
  apply Total.seq (censusLoop_total M w bound m k 0 hk (Nat.zero_le _) hm v _ hstate)
  intro e hloop
  exact .det ((censusFinish M).correct w bound e hloop.good.2 (censusFinish_guard M w bound e))

lemma census_sound (w : Word) (bound m k : ℕ) (hk : k < 2 ^ m)
    (d e : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (hdepth : reg d .depth = SearchProgram.word m k) (v : Fin (2 ^ m))
    (hv : reg d .frameB = SearchProgram.word m v.val) (hm : m + 1 < bound)
    (hcnt : reg d .middle = SearchProgram.word (m + 1)
      (Lax733996.Counting.layer (EncodedGraph.graph M w m) (EncodedGraph.first m) k).card)
    (h : Exec w bound (census M) d e) : CensusPost M w m k v d e := by
  have he := (censusSetup M).correct w bound d hd (censusSetup_spec M w bound m d v hw hv hm).1
  obtain ⟨hstate, _, hkeep, hlive⟩ := censusSetup_state M w bound m k d hd hw hdepth v hv hm
  cases h with
  | seq hsetup hrest =>
    obtain rfl := (ChoiceLanguage.det_exec_iff he).mp hsetup
    cases hrest with
    | @seq _ _ _ f _ hloop hfinish =>
      obtain ⟨hkf, hlf⟩ := censusLoop_sound M w bound m k 0 hk (Nat.zero_le _) hm v _ f hstate hloop
      have hef := (censusFinish M).correct w bound f hloop.good.2 (censusFinish_guard M w bound f)
      obtain rfl := (ChoiceLanguage.det_exec_iff hef).mp hfinish
      obtain ⟨hkeep', hfound, hvalid⟩ := censusFinish_spec M w bound f
      refine ⟨hkeep.trans (hkf.trans (hkeep'.mono (Finset.empty_subset _))), ?_⟩
      intro hl
      rw [hvalid, Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨hl₀, hfinal⟩ := hlf hl.1
      obtain ⟨c, hc, hcreg, hI⟩ := census_count_bound M w m k (2 ^ m) v f le_rfl hfinal.progress
      have hfcount := (hkf .middle (by simp [censusWrites])).trans ((hkeep .middle (by simp [censusWrites])).trans hcnt)
      have hcard := canonicalCount_bound M w m k (2 ^ m)
      simp only [canonicalCount, StreamingCensus.canonical_final] at hcard
      have hceq := (word_eq_iff (M := M) (m + 1) _ _ hc hcard).mp (hcreg.symm.trans (hl.2.trans hfcount))
      refine ⟨hlive ▸ hl₀, ?_⟩
      rw [hfound]
      exact StreamingCensus.complete _ _ v k _ (hceq ▸ hI)

lemma census_complete (w : Word) (bound m k : ℕ) (hk : k < 2 ^ m)
    (d : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (hdepth : reg d .depth = SearchProgram.word m k) (v : Fin (2 ^ m))
    (hv : reg d .frameB = SearchProgram.word m v.val) (hm : m + 1 < bound)
    (hcnt : reg d .middle = SearchProgram.word (m + 1)
      (Lax733996.Counting.layer (EncodedGraph.graph M w m) (EncodedGraph.first m) k).card)
    (hl : valid M d.state = true) :
    ∃ e, Exec w bound (census M) d e ∧ CensusPost M w m k v d e ∧ valid M e.state = true := by
  have he := (censusSetup M).correct w bound d hd (censusSetup_spec M w bound m d v hw hv hm).1
  obtain ⟨hstate, hcanonical, hkeep, hlive⟩ := censusSetup_state M w bound m k d hd hw hdepth v hv hm
  obtain ⟨f, hloop, _, hcount, hfl⟩ := censusLoop_complete M w bound m k 0 hk (Nat.zero_le _) hm v _
    hstate hcanonical (hlive.trans hl)
  obtain ⟨hkf, _⟩ := censusLoop_sound M w bound m k 0 hk (Nat.zero_le _) hm v _ f hstate hloop
  have hfc : reg f .middle = reg d .middle :=
    (hkf .middle (by simp [censusWrites])).trans (hkeep .middle (by simp [censusWrites]))
  have hef := (censusFinish M).correct w bound f hloop.good.2 (censusFinish_guard M w bound f)
  have hall : Exec w bound (census M) d _ := .seq (.det he) (.seq hloop (.det hef))
  refine ⟨_, hall, census_sound M w bound m k hk d _ hd hw hdepth v hv hm hcnt hall, ?_⟩
  rw [(censusFinish_spec M w bound f).2.2, hfl, hcount, hfc, hcnt]
  simp

end

end Lax733996Proofs.CountingProgram
