import Lax733996Proofs.CountingPathStep

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax733996Proofs.ConfigurationProofs
open SearchProgram (Register)
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

def pathWrites : Finset Register := {.a, .b, .kinds, .aux}

def PathClock (m r : ℕ) (d : Data M) : Prop :=
  reg d .kinds = SearchProgram.word m (if r = 0 then 2 ^ m - 1 else r - 1) ∧
    d.state.flag = decide (r = 0)

lemma pathClock_zero (m : ℕ) (d : Data M) (hc : PathClock M m 0 d) :
    running M d.state = false := by simp [running, hc.2]

lemma pathClock_succ (m r : ℕ) (d : Data M) (hc : PathClock M m (r + 1) d) :
    reg d .kinds = SearchProgram.word m r ∧ running M d.state = valid M d.state := by
  constructor
  · simpa using hc.1
  · simp [running, hc.2]

def PathBodyPost (w : Word) (m r : ℕ) (d e : Data M) (x y : Fin (2 ^ m)) : Prop :=
  PathClock M m r e ∧ reg e .a = SearchProgram.word m y.val ∧ Keeps pathWrites d e ∧
    e.state.user.overflow = d.state.user.overflow ∧
    (valid M e.state = true → valid M d.state = true ∧ (x = y ∨ EncodedGraph.graph M w m x y = true))

lemma pathBody_total (w : Word) (bound m r : ℕ) (hr : r < 2 ^ m)
    (d : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (x : Fin (2 ^ m)) (ha : reg d .a = SearchProgram.word m x.val)
    (hc : PathClock M m (r + 1) d) (hm : m + 1 < bound) :
    Total w bound (pathBody M) d := by
  apply Total.seq (pathStep_total M w bound m d hd hw x ha hm)
  intro f hf
  obtain ⟨_, _, hk, _, _⟩ := pathStep_sound M w bound m d f hd hw x ha hm hf
  have hfk : reg f .kinds = SearchProgram.word m r :=
    (hk .kinds (by simp)).trans (pathClock_succ M m r d hc).1
  exact .det ((decrement M .kinds).correct w bound f hf.good.2
    (decrement_spec M w bound m r hr .kinds f hfk).1)

lemma pathBody_sound (w : Word) (bound m r : ℕ) (hr : r < 2 ^ m)
    (d e : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (x : Fin (2 ^ m)) (ha : reg d .a = SearchProgram.word m x.val)
    (hc : PathClock M m (r + 1) d) (hm : m + 1 < bound)
    (h : Exec w bound (pathBody M) d e) : ∃ y, PathBodyPost M w m r d e x y := by
  cases h with
  | @seq _ _ _ f _ hs hdcr =>
    obtain ⟨y, hya, hk, ho, hv⟩ := pathStep_sound M w bound m d f hd hw x ha hm hs
    have hfk : reg f .kinds = SearchProgram.word m r :=
      (hk .kinds (by simp)).trans (pathClock_succ M m r d hc).1
    have he := (decrement M .kinds).correct w bound f hs.good.2
      (decrement_spec M w bound m r hr .kinds f hfk).1
    obtain rfl := (ChoiceLanguage.det_exec_iff he).mp hdcr
    obtain ⟨hkeep, hclock, hu, hflag⟩ := decrement_effect w bound m r hr .kinds f hfk
    refine ⟨y, ⟨hclock, hflag⟩, (hkeep .a (by simp)).trans hya, ?_, ?_, ?_⟩
    · exact (hk.mono (by intro q hq; simp [pathWrites] at hq ⊢; tauto)).trans
        (hkeep.mono (by intro q hq; simp [pathWrites] at hq ⊢; tauto))
    · exact (congrArg (fun u => u.overflow) hu).trans ho
    · simpa only [valid, hu] using hv

lemma pathBody_complete (w : Word) (bound m r : ℕ) (hr : r < 2 ^ m)
    (d : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (x y : Fin (2 ^ m)) (ha : reg d .a = SearchProgram.word m x.val)
    (hc : PathClock M m (r + 1) d) (hm : m + 1 < bound)
    (hv : valid M d.state = true) (hxy : x = y ∨ EncodedGraph.graph M w m x y = true) :
    ∃ e, Exec w bound (pathBody M) d e ∧ PathBodyPost M w m r d e x y ∧ valid M e.state = true := by
  obtain ⟨f, hs, ⟨hya, hk, _, _⟩, hfv⟩ := pathStep_complete M w bound m d hd hw x y ha hm hv hxy
  have hfk : reg f .kinds = SearchProgram.word m r :=
    (hk .kinds (by simp)).trans (pathClock_succ M m r d hc).1
  have he := (decrement M .kinds).correct w bound f hs.good.2
    (decrement_spec M w bound m r hr .kinds f hfk).1
  have hall : Exec w bound (pathBody M) d _ := .seq hs (.det he)
  obtain ⟨y', hp⟩ := pathBody_sound M w bound m r hr d _ hd hw x ha hc hm hall
  obtain ⟨hkeep, _, hu, _⟩ := decrement_effect w bound m r hr .kinds f hfk
  have hy' : y' = y := by
    apply Fin.ext
    apply (word_eq_iff m y'.val y.val y'.isLt y.isLt (M := M)).mp
    exact hp.2.1.symm.trans ((hkeep .a (by simp)).trans hya)
  refine ⟨_, hall, hy' ▸ hp, ?_⟩
  simpa only [valid, hu] using hfv

end

end Lax733996Proofs.CountingProgram
