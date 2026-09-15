import Lax733996Proofs.CountingPathLoop
import Lax733996Proofs.CountingPathSetup

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax733996Proofs.ConfigurationProofs
open Lax733996.Reachability
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

def PathPost (w : Word) (m k : ℕ) (d e : Data M) (u : Fin (2 ^ m)) : Prop :=
  Keeps pathWrites d e ∧ e.state.user.overflow = d.state.user.overflow ∧
    (valid M e.state = true → valid M d.state = true ∧
      Within (fun x y => EncodedGraph.graph M w m x y = true) k (EncodedGraph.first m) u)

lemma path_total (w : Word) (bound m k : ℕ) (hk : k < 2 ^ m)
    (d : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (hdepth : reg d .depth = SearchProgram.word m k) (hm : m + 1 < bound) :
    Total w bound (path M) d := by
  obtain ⟨hg, ha, hc, hkeep, _⟩ := pathSetup_spec M w bound m k hk d hw hdepth hm
  have he := (pathSetup M).correct w bound d hd hg
  apply ChoiceLanguage.total_det_seq he
  apply Total.seq (pathLoop_total M w bound m k (by omega) _ he.good.2
    ((hkeep .width (by simp [pathWrites])).trans hw) (EncodedGraph.first m) ha hc hm)
  intro f hf
  exact .det ((pathFinish M).correct w bound f hf.good.2 (pathFinish_guard M w bound f))

lemma path_sound (w : Word) (bound m k : ℕ) (hk : k < 2 ^ m)
    (d e : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (hdepth : reg d .depth = SearchProgram.word m k) (hm : m + 1 < bound)
    (u : Fin (2 ^ m)) (hu : reg d .frameMiddle = SearchProgram.word m u.val)
    (h : Exec w bound (path M) d e) : PathPost M w m k d e u := by
  obtain ⟨hg, ha, hc, hkeep, huser⟩ := pathSetup_spec M w bound m k hk d hw hdepth hm
  have he := (pathSetup M).correct w bound d hd hg
  cases h with
  | seq hsetup hrest =>
    obtain rfl := (ChoiceLanguage.det_exec_iff he).mp hsetup
    cases hrest with
    | @seq _ _ _ f _ hloop hfinish =>
      obtain ⟨x, hxa, hfkeep, hfound, hlive⟩ := pathLoop_sound M w bound m k (by omega)
        _ f he.good.2 ((hkeep .width (by simp [pathWrites])).trans hw) (EncodedGraph.first m) ha hc hm hloop
      have huf : reg f .frameMiddle = SearchProgram.word m u.val :=
        (hfkeep .frameMiddle (by simp [pathWrites])).trans ((hkeep .frameMiddle (by simp [pathWrites])).trans hu)
      have hef := (pathFinish M).correct w bound f hloop.good.2 (pathFinish_guard M w bound f)
      obtain rfl := (ChoiceLanguage.det_exec_iff hef).mp hfinish
      obtain ⟨hff, hfo, hfv⟩ := pathFinish_spec M w bound m f x u hxa huf
      refine ⟨hkeep.trans (hfkeep.trans (hff.mono (Finset.empty_subset _))), ?_, ?_⟩
      · exact hfo.trans (hfound.trans (congrArg (fun s => s.overflow) huser))
      · intro hv
        rw [hfv, Bool.and_eq_true, decide_eq_true_eq] at hv
        obtain ⟨hv₀, hreach⟩ := hlive hv.1
        have hvd : valid M d.state = true := by simpa only [valid, huser] using hv₀
        exact ⟨hvd, hv.2 ▸ hreach⟩

lemma path_complete (w : Word) (bound m k : ℕ) (hk : k < 2 ^ m)
    (d : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (hdepth : reg d .depth = SearchProgram.word m k) (hm : m + 1 < bound)
    (u : Fin (2 ^ m)) (hu : reg d .frameMiddle = SearchProgram.word m u.val)
    (hv : valid M d.state = true)
    (hreach : Within (fun x y => EncodedGraph.graph M w m x y = true) k (EncodedGraph.first m) u) :
    ∃ e, Exec w bound (path M) d e ∧ PathPost M w m k d e u ∧ valid M e.state = true := by
  obtain ⟨hg, ha, hc, hkeep, huser⟩ := pathSetup_spec M w bound m k hk d hw hdepth hm
  have he := (pathSetup M).correct w bound d hd hg
  obtain ⟨f, hf, ⟨hfa, hfkeep, _, _⟩, hfv⟩ := pathLoop_complete M w bound m k (by omega) _ he.good.2
    ((hkeep .width (by simp [pathWrites])).trans hw) (EncodedGraph.first m) u ha hc hm
    (by simpa only [valid, huser] using hv) hreach
  have huf : reg f .frameMiddle = SearchProgram.word m u.val :=
    (hfkeep .frameMiddle (by simp [pathWrites])).trans ((hkeep .frameMiddle (by simp [pathWrites])).trans hu)
  have hef := (pathFinish M).correct w bound f hf.good.2 (pathFinish_guard M w bound f)
  have hall : Exec w bound (path M) d _ := .seq (.det he) (.seq hf (.det hef))
  refine ⟨_, hall, path_sound M w bound m k hk d _ hd hw hdepth hm u hu hall, ?_⟩
  rw [(pathFinish_spec M w bound m f u u hfa huf).2.2]
  simpa using hfv

end

end Lax733996Proofs.CountingProgram
