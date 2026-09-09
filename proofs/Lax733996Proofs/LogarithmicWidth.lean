import Lax733996Proofs.BinaryInputCount

/-! An input scan constructs the logarithmic bound on an actual stack. -/

namespace Lax733996Proofs.LogarithmicWidth

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930.SpaceBounds
open Lax307052Proofs
open StackLanguage (Exec Good)
open StackMacros (Macro)
open scoped Classical

noncomputable section

variable {K Γ σ : Type} [Inhabited Γ]

def finish (src aux width : K) (marker : Γ) : Macro K Γ σ :=
  (Macro.copyMap src width aux (fun _ => marker)).seq
    ((Macro.read width).seq (Macro.clear src))

def code (src aux width : K) (bit : Bool → Γ) (readBit : Γ → Bool) (marker : Γ) :
    StackRoutines.Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (BinaryInputCount.countCode src aux bit readBit) (finish src aux width marker).code

lemma finish_spec (w : Word) (bound : ℕ) (src aux width : K)
    (hsa : src ≠ aux) (hsw : src ≠ width) (hwa : width ≠ aux) (marker : Γ)
    (d : StackRoutines.Data (K := K) (Γ := Γ) (σ := σ))
    (ha : d.store aux = []) (hlen : (d.store src).length = logSpace w.length + 1) :
    (finish src aux width marker).guard w bound d ∧
      let e := (finish src aux width marker).result w d
      e.store width = List.replicate (logSpace w.length) marker ∧ e.store src = [] ∧
      (∀ k, k ≠ src → k ≠ width → e.store k = d.store k) ∧
      e.inputHead = d.inputHead ∧ e.state.user = d.state.user := by
  constructor
  · exact ⟨⟨hsw, hsa, hwa, ha⟩, trivial, trivial⟩
  · simp [finish, Macro.seq, Macro.copyMap, Macro.read, Macro.clear,
      StackLanguage.popped, StackRoutines.cleared, hsw, Ne.symm hsw, hlen]
    intro k hks hkw
    simp [hks, hkw]

lemma execute (w : Word) (bound : ℕ) (src aux width : K)
    (hsa : src ≠ aux) (hsw : src ≠ width) (hwa : width ≠ aux)
    (bit : Bool → Γ) (readBit : Γ → Bool) (hbit : ∀ b, readBit (bit b) = b) (marker : Γ)
    (d : StackRoutines.Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (hi : d.inputHead = 0) (hs : d.store src = []) (ha : d.store aux = [])
    (hb : logSpace w.length + 2 < bound) :
    ∃ e, Exec w bound (code src aux width bit readBit marker) d e ∧
      e.store width = List.replicate (logSpace w.length) marker ∧ e.store src = [] ∧
      (∀ k, k ≠ src → k ≠ width → e.store k = d.store k) ∧
      e.inputHead = w.length + 1 ∧ e.state.user = d.state.user := by
  obtain ⟨e, he, hei, hes, heframe, heu⟩ :=
    BinaryInputCount.count_exec w bound src aux hsa bit readBit hbit d hd hi hs ha hb
  have hea : e.store aux = [] := by rw [heframe aux (Ne.symm hsa)]; exact ha
  have helen : (e.store src).length = logSpace w.length + 1 := by
    rw [hes, List.length_map, BinaryInputCount.bits_length _ (by omega)]
    rfl
  obtain ⟨hg, hfwidth, hfsrc, hfframe, hfi, hfu⟩ :=
    finish_spec w bound src aux width hsa hsw hwa marker e hea helen
  have hf := (finish src aux width marker).correct w bound e he.good.2 hg
  refine ⟨_, .seq he hf, hfwidth, hfsrc, ?_, hfi.trans hei, hfu.trans heu⟩
  intro k hks hkw
  exact (hfframe k hks hkw).trans (heframe k hks)

end

end Lax733996Proofs.LogarithmicWidth
