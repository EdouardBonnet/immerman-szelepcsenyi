import Lax733996Proofs.CountingPathBody
import Lax307052Proofs.Reachability

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax307052Proofs
open Lax307052.Reachability
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

def PathLoopPost (w : Word) (m r : ℕ) (d e : Data M) (x y : Fin (2 ^ m)) : Prop :=
  reg e .a = SearchProgram.word m y.val ∧ Keeps pathWrites d e ∧
    e.state.user.overflow = d.state.user.overflow ∧
    (valid M e.state = true → valid M d.state = true ∧
      Within (fun u v => EncodedGraph.graph M w m u v = true) r x y)

lemma pathLoop_total (w : Word) (bound m r : ℕ) (hr : r ≤ 2 ^ m)
    (d : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (x : Fin (2 ^ m)) (ha : reg d .a = SearchProgram.word m x.val)
    (hc : PathClock M m r d) (hm : m + 1 < bound) : Total w bound (pathLoop M) d := by
  induction r generalizing d x with
  | zero => exact .loop_false _ _ d hd (pathClock_zero M m d hc)
  | succ r ih =>
    cases ht : running M d.state with
    | false => exact .loop_false _ _ d hd ht
    | true =>
      apply Total.loop_true ht (pathBody_total M w bound m r (by omega) d hd hw x ha hc hm)
      intro f hf
      obtain ⟨y, hfc, hfa, hk, _, _⟩ := pathBody_sound M w bound m r (by omega) d f hd hw x ha hc hm hf
      exact ih (by omega) f hf.good.2 ((hk .width (by simp [pathWrites])).trans hw) y hfa hfc

lemma pathLoop_sound (w : Word) (bound m r : ℕ) (hr : r ≤ 2 ^ m)
    (d e : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (x : Fin (2 ^ m)) (ha : reg d .a = SearchProgram.word m x.val)
    (hc : PathClock M m r d) (hm : m + 1 < bound)
    (h : Exec w bound (pathLoop M) d e) : ∃ y, PathLoopPost M w m r d e x y := by
  induction r generalizing d e x with
  | zero =>
    have ht := pathClock_zero M m d hc
    cases h with
    | loop_false => exact ⟨x, ha, Keeps.refl _ _, rfl, fun hv => ⟨hv, 0, le_rfl, .nil x⟩⟩
    | loop_true hf _ _ => simp [ht] at hf
  | succ r ih =>
    cases h with
    | loop_false => exact ⟨x, ha, Keeps.refl _ _, rfl, fun hv => ⟨hv, 0, Nat.zero_le _, .nil x⟩⟩
    | @loop_true _ _ _ f _ ht hb hl =>
      obtain ⟨y, hfc, hfa, hk, ho, hv⟩ := pathBody_sound M w bound m r (by omega) d f hd hw x ha hc hm hb
      obtain ⟨z, hza, hkeep, hfound, hvalid⟩ := ih (by omega) f e hb.good.2
        ((hk .width (by simp [pathWrites])).trans hw) y hfa hfc hl
      refine ⟨z, hza, hk.trans hkeep, hfound.trans ho, ?_⟩
      intro he
      obtain ⟨hf, hreach⟩ := hvalid he
      obtain ⟨hdv, hedge⟩ := hv hf
      refine ⟨hdv, ?_⟩
      have hh := (path_splitting (fun u v => EncodedGraph.graph M w m u v = true) 1 r x z).mpr
        ⟨y, (within_one _ x y).mpr hedge, hreach⟩
      simpa [Nat.add_comm] using hh

lemma pathLoop_complete (w : Word) (bound m r : ℕ) (hr : r ≤ 2 ^ m)
    (d : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (x y : Fin (2 ^ m)) (ha : reg d .a = SearchProgram.word m x.val)
    (hc : PathClock M m r d) (hm : m + 1 < bound) (hv : valid M d.state = true)
    (hxy : Within (fun u v => EncodedGraph.graph M w m u v = true) r x y) :
    ∃ e, Exec w bound (pathLoop M) d e ∧ PathLoopPost M w m r d e x y ∧ valid M e.state = true := by
  induction r generalizing d x with
  | zero =>
    obtain ⟨k, hk, hwalk⟩ := hxy
    have hk0 : k = 0 := by omega
    subst k
    cases hwalk
    exact ⟨d, .loop_false _ _ d hd (pathClock_zero M m d hc), ⟨ha, Keeps.refl _ _, rfl,
      (fun h => ⟨h, 0, le_rfl, .nil y⟩)⟩, hv⟩
  | succ r ih =>
    obtain ⟨z, hxz, hzy⟩ := (path_splitting
      (fun u v => EncodedGraph.graph M w m u v = true) 1 r x y).mp (by simpa [Nat.add_comm] using hxy)
    obtain ⟨f, hf, ⟨hfc, hfa, hk, _, _⟩, hfv⟩ := pathBody_complete M w bound m r (by omega)
      d hd hw x z ha hc hm hv ((within_one _ x z).mp hxz)
    obtain ⟨e, he, hpost, hev⟩ := ih (by omega) f hf.good.2
      ((hk .width (by simp [pathWrites])).trans hw) z hfa hfc hfv hzy
    have hall : Exec w bound (pathLoop M) d e :=
      .loop_true (by rw [(pathClock_succ M m r d hc).2]; exact hv) hf he
    obtain ⟨y', hp⟩ := pathLoop_sound M w bound m (r + 1) hr d e hd hw x ha hc hm hall
    have hy : y' = y := by
      apply Fin.ext
      exact (word_eq_iff m _ _ y'.isLt y.isLt (M := M)).mp (hp.1.symm.trans hpost.1)
    exact ⟨e, hall, hy ▸ hp, hev⟩

end

end Lax733996Proofs.CountingProgram
