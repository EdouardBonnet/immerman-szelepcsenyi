import Lax733996Proofs.CountingLayerLoop
import Lax733996Proofs.CountingLayerSetup

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax307052Proofs
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

def layerDoneWrites : Finset SearchProgram.Register := insert .middle layerWrites

def LayerPost (w : Word) (m k : ℕ) (d e : Data M) : Prop :=
  Keeps layerDoneWrites d e ∧ (valid M e.state = true → valid M d.state = true ∧
    reg e .middle = SearchProgram.word (m + 1) (layerCount M w m (k + 1)) ∧
    (e.state.user.overflow = true ↔ EncodedGraph.last m ∈
      Lax733996.Counting.layer (EncodedGraph.graph M w m) (EncodedGraph.first m) (k + 1)))

lemma layer_total (w : Word) (bound m k : ℕ) (hk : k < 2 ^ m)
    (d : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (hdepth : reg d .depth = SearchProgram.word m k)
    (hcnt : reg d .middle = SearchProgram.word (m + 1) (layerCount M w m k)) (hm : m + 1 < bound) :
    Total w bound (layer M) d := by
  have he := (layerSetup M).correct w bound d hd (layerSetup_spec M w bound m d hw hm).1
  obtain ⟨hstate, _, _⟩ := layerSetup_state M w bound m k d hd hw hdepth hcnt hm
  apply ChoiceLanguage.total_det_seq he
  apply Total.seq (layerLoop_total M w bound m k 0 hk (Nat.zero_le _) hm _ hstate)
  intro e hloop
  exact .det ((copy M .frameA .middle).correct w bound e hloop.good.2
    (copy_spec M w bound .frameA .middle (by decide) e).1)

lemma layer_sound (w : Word) (bound m k : ℕ) (hk : k < 2 ^ m)
    (d e : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (hdepth : reg d .depth = SearchProgram.word m k)
    (hcnt : reg d .middle = SearchProgram.word (m + 1) (layerCount M w m k)) (hm : m + 1 < bound)
    (h : Exec w bound (layer M) d e) : LayerPost M w m k d e := by
  have he := (layerSetup M).correct w bound d hd (layerSetup_spec M w bound m d hw hm).1
  obtain ⟨hstate, hkeep, hlive⟩ := layerSetup_state M w bound m k d hd hw hdepth hcnt hm
  cases h with
  | seq hsetup hrest =>
    obtain rfl := (ChoiceLanguage.det_exec_iff he).mp hsetup
    cases hrest with
    | @seq _ _ _ f _ hloop hfinish =>
      obtain ⟨hkf, hlf⟩ := layerLoop_sound M w bound m k 0 hk (Nat.zero_le _) hm _ f hstate hloop
      have hef := (copy M .frameA .middle).correct w bound f hloop.good.2
        (copy_spec M w bound .frameA .middle (by decide) f).1
      obtain rfl := (ChoiceLanguage.det_exec_iff hef).mp hfinish
      obtain ⟨hkeep', hcount, huser⟩ := copy_effect w bound .frameA .middle (by decide) f
      refine ⟨?_, ?_⟩
      · exact ((hkeep.trans hkf).mono (Finset.subset_insert _ _)).trans
          (hkeep'.mono (by intro r hr; simp [layerDoneWrites] at hr ⊢; tauto))
      · intro hl
        have hfl : valid M f.state = true := by simpa only [valid, huser] using hl
        obtain ⟨hl₀, hfinal⟩ := hlf hfl
        obtain ⟨c, _, hcreg, hspec⟩ := hfinal.progress
        obtain ⟨hcanonical, hlast⟩ := hspec hfl
        refine ⟨hlive ▸ hl₀, ?_, ?_⟩
        · rw [hcount, hcreg, hcanonical]
          simp only [canonicalCount, StreamingCensus.canonical_final, layerCount]
        · rw [huser]
          apply hlast (EncodedGraph.last m)
          dsimp [EncodedGraph.last]
          have hp : 0 < 2 ^ m := by positivity
          omega

lemma layer_complete (w : Word) (bound m k : ℕ) (hk : k < 2 ^ m)
    (d : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (hdepth : reg d .depth = SearchProgram.word m k)
    (hcnt : reg d .middle = SearchProgram.word (m + 1) (layerCount M w m k)) (hm : m + 1 < bound)
    (hl : valid M d.state = true) :
    ∃ e, Exec w bound (layer M) d e ∧ LayerPost M w m k d e ∧ valid M e.state = true := by
  have he := (layerSetup M).correct w bound d hd (layerSetup_spec M w bound m d hw hm).1
  obtain ⟨hstate, _, hlive⟩ := layerSetup_state M w bound m k d hd hw hdepth hcnt hm
  obtain ⟨f, hloop, _, hfl⟩ := layerLoop_complete M w bound m k 0 hk (Nat.zero_le _) hm _ hstate (hlive.trans hl)
  have hef := (copy M .frameA .middle).correct w bound f hloop.good.2
    (copy_spec M w bound .frameA .middle (by decide) f).1
  have huser := (copy_effect w bound .frameA .middle (by decide) f).2.2
  have hall : Exec w bound (layer M) d _ := .seq (.det he) (.seq hloop (.det hef))
  refine ⟨_, hall, layer_sound M w bound m k hk d _ hd hw hdepth hcnt hm hall, ?_⟩
  simpa only [valid, huser] using hfl

end

end Lax733996Proofs.CountingProgram
