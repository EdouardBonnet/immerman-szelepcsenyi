import Lax733996Proofs.CountingLayer

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax307052Proofs
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

structure ProgramState (w : Word) (bound m k : ℕ) (d : Data M) : Prop where
  good : Good w bound d
  width : reg d .width = SearchProgram.unary m
  depth : reg d .depth = SearchProgram.word m k
  flag : d.state.flag = decide (k = 2 ^ m)
  progress : valid M d.state = true →
    reg d .middle = SearchProgram.word (m + 1) (layerCount M w m k) ∧
    (0 < k → (d.state.user.overflow = true ↔ EncodedGraph.last m ∈
      Lax733996.Counting.layer (EncodedGraph.graph M w m) (EncodedGraph.first m) k))

lemma programState_stop (w : Word) (bound m : ℕ) (d : Data M) (hd : ProgramState M w bound m (2 ^ m) d) :
    running M d.state = false := by simp [running, hd.flag]

lemma programState_running (w : Word) (bound m k : ℕ) (hk : k < 2 ^ m)
    (d : Data M) (hd : ProgramState M w bound m k d) : running M d.state = valid M d.state := by
  simp [running, hd.flag, Nat.ne_of_lt hk]

lemma programState_body_total (w : Word) (bound m k : ℕ) (hk : k < 2 ^ m) (hm : m + 1 < bound)
    (d : Data M) (hd : ProgramState M w bound m k d) (hl : valid M d.state = true) :
    Total w bound (programBody M) d := by
  apply Total.seq (layer_total M w bound m k hk d hd.good hd.width hd.depth (hd.progress hl).1 hm)
  intro f hf
  obtain ⟨hkeep, _⟩ := layer_sound M w bound m k hk d f hd.good hd.width hd.depth (hd.progress hl).1 hm hf
  have hfd : reg f .depth = SearchProgram.word m k := (hkeep .depth (by simp [layerDoneWrites, layerWrites])).trans hd.depth
  exact .det ((increment M .depth).correct w bound f hf.good.2 (increment_spec M w bound m k hk .depth f hfd).1)

lemma programState_step (w : Word) (bound m k : ℕ) (hk : k < 2 ^ m) (hm : m + 1 < bound)
    (d e : Data M) (hd : ProgramState M w bound m k d) (hl : valid M d.state = true)
    (h : Exec w bound (programBody M) d e) : ProgramState M w bound m (k + 1) e := by
  cases h with
  | @seq _ _ _ f _ hlayer hinc =>
    obtain ⟨hkeep, hpost⟩ := layer_sound M w bound m k hk d f hd.good hd.width hd.depth (hd.progress hl).1 hm hlayer
    have hfd : reg f .depth = SearchProgram.word m k := (hkeep .depth (by simp [layerDoneWrites, layerWrites])).trans hd.depth
    have he := (increment M .depth).correct w bound f hlayer.good.2 (increment_spec M w bound m k hk .depth f hfd).1
    obtain rfl := (ChoiceLanguage.det_exec_iff he).mp hinc
    obtain ⟨hkeep', hdepth, huser, hflag⟩ := increment_effect w bound m k hk .depth f hfd
    refine ⟨he.good.2, (hkeep' .width (by simp)).trans
      ((hkeep .width (by simp [layerDoneWrites, layerWrites])).trans hd.width), hdepth, hflag, ?_⟩
    intro hel
    have hfl : valid M f.state = true := by simpa only [valid, huser] using hel
    obtain ⟨_, hcount, hfound⟩ := hpost hfl
    exact ⟨(hkeep' .middle (by simp)).trans hcount, fun _ => by simpa only [huser] using hfound⟩

lemma programState_complete_step (w : Word) (bound m k : ℕ) (hk : k < 2 ^ m) (hm : m + 1 < bound)
    (d : Data M) (hd : ProgramState M w bound m k d) (hl : valid M d.state = true) :
    ∃ e, Exec w bound (programBody M) d e ∧ ProgramState M w bound m (k + 1) e ∧ valid M e.state = true := by
  obtain ⟨f, hlayer, ⟨hkeep, _⟩, hfl⟩ := layer_complete M w bound m k hk d hd.good hd.width hd.depth (hd.progress hl).1 hm hl
  have hfd : reg f .depth = SearchProgram.word m k := (hkeep .depth (by simp [layerDoneWrites, layerWrites])).trans hd.depth
  have he := (increment M .depth).correct w bound f hlayer.good.2 (increment_spec M w bound m k hk .depth f hfd).1
  have huser := (increment_effect w bound m k hk .depth f hfd).2.2.1
  have hall : Exec w bound (programBody M) d _ := .seq hlayer (.det he)
  refine ⟨_, hall, programState_step M w bound m k hk hm d _ hd hl hall, ?_⟩
  simpa only [valid, huser] using hfl

end

end Lax733996Proofs.CountingProgram
