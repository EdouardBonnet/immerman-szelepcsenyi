import Lax362205Proofs.CountingPath
import Lax362205Proofs.CountingRecord

namespace Lax362205Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax362205Proofs.ConfigurationProofs
open Lax362205.Reachability
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

def censusTakeWrites : Finset SearchProgram.Register := {.a, .b, .kinds, .aux, .frameDepth}

def CensusTakePost (w : Word) (m k c : ℕ) (u v : Fin (2 ^ m)) (d e : Data M) : Prop :=
  Keeps censusTakeWrites d e ∧
    (valid M e.state = true → valid M d.state = true) ∧
    ((valid M e.state = false ∧ reg e .frameDepth = SearchProgram.word (m + 1) c ∧
        e.state.user.overflow = d.state.user.overflow) ∨
      (reg e .frameDepth = SearchProgram.word (m + 1) (c + 1) ∧
        e.state.user.overflow = (d.state.user.overflow || EncodedGraph.graph M w m u v) ∧
        Within (fun x y => EncodedGraph.graph M w m x y = true) k (EncodedGraph.first m) u))

lemma censusTake_total (w : Word) (bound m k c : ℕ) (hk : k < 2 ^ m) (hc : c < 2 ^ (m + 1))
    (d : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (hdepth : reg d .depth = SearchProgram.word m k) (hm : m + 1 < bound)
    (u v : Fin (2 ^ m)) (hu : reg d .frameMiddle = SearchProgram.word m u.val)
    (hv : reg d .frameB = SearchProgram.word m v.val)
    (hcnt : reg d .frameDepth = SearchProgram.word (m + 1) c) :
    Total w bound (censusTake M) d := by
  apply Total.seq (path_total M w bound m k hk d hd hw hdepth hm)
  intro f hf
  obtain ⟨hkeep, _, _⟩ := path_sound M w bound m k hk d f hd hw hdepth hm u hu hf
  cases ht : valid M f.state with
  | false => exact .branch_false ht (.det (.skip _ hf.good.2))
  | true =>
    have hg := (censusRecord_spec M w bound m c hc f u v
      ((hkeep .frameMiddle (by simp [pathWrites])).trans hu)
      ((hkeep .frameB (by simp [pathWrites])).trans hv)
      ((hkeep .frameDepth (by simp [pathWrites])).trans hcnt) hm).1
    exact .branch_true ht (.det ((censusRecord M).correct w bound f hf.good.2 hg))

lemma censusTake_sound (w : Word) (bound m k c : ℕ) (hk : k < 2 ^ m) (hc : c < 2 ^ (m + 1))
    (d e : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (hdepth : reg d .depth = SearchProgram.word m k) (hm : m + 1 < bound)
    (u v : Fin (2 ^ m)) (hu : reg d .frameMiddle = SearchProgram.word m u.val)
    (hv : reg d .frameB = SearchProgram.word m v.val)
    (hcnt : reg d .frameDepth = SearchProgram.word (m + 1) c)
    (h : Exec w bound (censusTake M) d e) : CensusTakePost M w m k c u v d e := by
  cases h with
  | @seq _ _ _ f _ hp hb =>
    obtain ⟨hkeep, hfound, hlive⟩ := path_sound M w bound m k hk d f hd hw hdepth hm u hu hp
    have hfu : reg f .frameMiddle = SearchProgram.word m u.val := (hkeep .frameMiddle (by simp [pathWrites])).trans hu
    have hfv : reg f .frameB = SearchProgram.word m v.val := (hkeep .frameB (by simp [pathWrites])).trans hv
    have hfc : reg f .frameDepth = SearchProgram.word (m + 1) c := (hkeep .frameDepth (by simp [pathWrites])).trans hcnt
    cases hb with
    | branch_false ht hs =>
      cases hs with
      | det he =>
        cases he
        exact ⟨hkeep.mono (by intro r hr; simp [pathWrites, censusTakeWrites] at hr ⊢; tauto),
          fun hh => (hlive hh).1, Or.inl ⟨ht, hfc, hfound⟩⟩
    | branch_true ht he =>
      obtain ⟨hg, hk', hc', ho', hv'⟩ := censusRecord_spec M w bound m c hc f u v hfu hfv hfc hm
      obtain rfl := (ChoiceLanguage.det_exec_iff ((censusRecord M).correct w bound f hp.good.2 hg)).mp he
      refine ⟨?_, fun _ => (hlive ht).1, Or.inr ⟨hc', ?_, (hlive ht).2⟩⟩
      · exact (hkeep.mono (by intro r hr; simp [pathWrites, censusTakeWrites] at hr ⊢; tauto)).trans
          (hk'.mono (by intro r hr; simp [censusTakeWrites] at hr ⊢; tauto))
      · rw [ho', hfound]

lemma censusTake_complete (w : Word) (bound m k c : ℕ) (hk : k < 2 ^ m) (hc : c < 2 ^ (m + 1))
    (d : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (hdepth : reg d .depth = SearchProgram.word m k) (hm : m + 1 < bound)
    (u v : Fin (2 ^ m)) (hu : reg d .frameMiddle = SearchProgram.word m u.val)
    (hv : reg d .frameB = SearchProgram.word m v.val)
    (hcnt : reg d .frameDepth = SearchProgram.word (m + 1) c) (hl : valid M d.state = true)
    (hreach : Within (fun x y => EncodedGraph.graph M w m x y = true) k (EncodedGraph.first m) u) :
    ∃ e, Exec w bound (censusTake M) d e ∧ CensusTakePost M w m k c u v d e ∧ valid M e.state = true := by
  obtain ⟨f, hp, ⟨hkeep, _, _⟩, hfl⟩ := path_complete M w bound m k hk d hd hw hdepth hm u hu hl hreach
  obtain ⟨hg, _, _, _, hvl⟩ := censusRecord_spec M w bound m c hc f u v
    ((hkeep .frameMiddle (by simp [pathWrites])).trans hu)
    ((hkeep .frameB (by simp [pathWrites])).trans hv)
    ((hkeep .frameDepth (by simp [pathWrites])).trans hcnt) hm
  have he := (censusRecord M).correct w bound f hp.good.2 hg
  have hall : Exec w bound (censusTake M) d _ := .seq hp (.branch_true hfl (.det he))
  exact ⟨_, hall, censusTake_sound M w bound m k c hk hc d _ hd hw hdepth hm u v hu hv hcnt hall,
    hvl.trans hfl⟩

end

end Lax362205Proofs.CountingProgram
