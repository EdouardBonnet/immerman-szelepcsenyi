import Lax362205Proofs.ConfigurationProofs.StackMacros
import Lax434930.SpaceBounds

namespace Lax362205Proofs.GrowingBinary

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax362205Proofs.ConfigurationProofs Lax362205Proofs.ConfigurationProofs.BinaryCounter
open scoped Classical

noncomputable section

def grow (xs : List Bool) : List Bool :=
  if carry xs then increment xs ++ [true] else increment xs

lemma value_append (xs ys : List Bool) :
    value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih => simp only [List.cons_append, value, List.length_cons, ih, pow_succ]; ring

lemma grow_value (xs : List Bool) : value (grow xs) = value xs + 1 := by
  have h := increment_value xs
  cases hc : carry xs <;>
    simpa [grow, hc, value_append, increment_length, value] using h

lemma grow_length (xs : List Bool) :
    (grow xs).length = xs.length + (if carry xs then 1 else 0) := by
  cases hc : carry xs <;> simp [grow, hc, increment_length]

def Canonical (xs : List Bool) : Prop := xs = [] ∨ 2 ^ (xs.length - 1) ≤ value xs

lemma grow_canonical {xs : List Bool} (h : Canonical xs) : Canonical (grow xs) := by
  right
  rw [grow_value, grow_length]
  cases hc : carry xs with
  | false =>
    simp only [hc, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    rcases h with rfl | h
    · simp [carry] at hc
    · omega
  | true =>
    simp only [hc, ↓reduceIte, Nat.add_sub_cancel]
    have hi := increment_value xs
    simp only [hc, ↓reduceIte] at hi
    omega

lemma length_eq_log {xs : List Bool} (h : Canonical xs) (hp : 0 < value xs) :
    xs.length = Nat.log 2 (value xs) + 1 := by
  have hn : 0 < xs.length := by
    cases xs with
    | nil => simp [value] at hp
    | cons => simp
  have hlo : xs.length - 1 ≤ Nat.log 2 (value xs) := by
    apply Nat.le_log_of_pow_le (by decide)
    rcases h with rfl | h
    · simp [value] at hp
    · exact h
  have hhi := Nat.log_lt_of_lt_pow (Nat.ne_of_gt hp) (value_lt xs)
  omega

lemma length_bound {xs : List Bool} (h : Canonical xs) {n : ℕ} (hv : value xs ≤ n + 2) :
    xs.length ≤ Lax434930.SpaceBounds.logSpace n + 1 := by
  rcases h with rfl | h
  · simp
  · have hp : 0 < value xs := lt_of_lt_of_le (by positivity : 0 < 2 ^ (xs.length - 1)) h
    rw [length_eq_log (Or.inr h) hp]
    exact Nat.add_le_add_right (Nat.log_mono_right hv) 1

variable {K Γ σ : Type} [Inhabited Γ]

def extend (src aux : K) (bit : Bool → Γ) : StackMacros.Macro K Γ σ :=
  (StackMacros.Macro.transfer src aux).seq
    ((StackMacros.Macro.push src (fun _ => bit true)).seq (StackMacros.Macro.transfer aux src))

def program (src aux : K) (bit : Bool → Γ) (readBit : Γ → Bool) : StackMacros.Macro K Γ σ :=
  (StackMacros.Macro.increment src aux bit readBit).seq
    (StackMacros.Macro.branch (fun s => s.flag) (extend src aux bit) StackMacros.Macro.skip)

lemma extend_correct (w : Word) (bound : ℕ) (src aux : K) (hne : src ≠ aux)
    (bit : Bool → Γ) (d : StackRoutines.Data (K := K) (Γ := Γ) (σ := σ))
    (ha : d.store aux = []) (hb : (d.store src).length + 1 < bound) :
    (extend src aux bit).guard w bound d ∧
    (extend src aux bit).result w d =
      ⟨{d.state with value := none}, d.inputHead,
        Function.update d.store src (d.store src ++ [bit true])⟩ := by
  constructor
  · simp [extend, StackMacros.Macro.seq, StackMacros.Macro.transfer, StackMacros.Macro.push,
      StackRoutines.transferred, StackLanguage.pushed, Function.update_apply, hne, Ne.symm hne, ha]
    omega
  · simp only [extend, StackMacros.Macro.seq, StackMacros.Macro.transfer, StackMacros.Macro.push,
      StackRoutines.transferred, StackLanguage.pushed]
    congr 1
    funext k
    by_cases hs : k = src <;> by_cases ha' : k = aux <;>
      simp_all [Function.update_apply, Ne.symm hne]

lemma program_correct (w : Word) (bound : ℕ) (src aux : K) (hne : src ≠ aux)
    (bit : Bool → Γ) (readBit : Γ → Bool) (hbit : ∀ b, readBit (bit b) = b)
    (d : StackRoutines.Data (K := K) (Γ := Γ) (σ := σ)) (xs : List Bool)
    (hs : d.store src = xs.map bit) (ha : d.store aux = []) (hb : xs.length + 1 < bound) :
    (program src aux bit readBit).guard w bound d ∧
    (program src aux bit readBit).result w d =
      ⟨{d.state with value := none, flag := carry xs}, d.inputHead,
        Function.update d.store src ((grow xs).map bit)⟩ := by
  have hmap : (d.store src).map readBit = xs := by
    simp [hs, List.map_map, Function.comp_def, hbit]
  let di : StackRoutines.Data (K := K) (Γ := Γ) (σ := σ) :=
    ⟨{d.state with value := none, flag := carry xs}, d.inputHead,
      Function.update d.store src ((increment xs).map bit)⟩
  have hi : (StackMacros.Macro.increment src aux bit readBit).result w d = di := by
    simp [StackMacros.Macro.increment, hmap, di]
  have hguard : (StackMacros.Macro.increment src aux bit readBit).guard w bound d :=
    ⟨hne, hbit, ha, by rw [hmap, hs]⟩
  have hdia : di.store aux = [] := by simp [di, Ne.symm hne, ha]
  have hdib : (di.store src).length + 1 < bound := by simpa [di, increment_length] using hb
  obtain ⟨hext, hresult⟩ := extend_correct w bound src aux hne bit di hdia hdib
  constructor
  · refine ⟨hguard, ?_⟩
    change (StackMacros.Macro.branch (fun s => s.flag) (extend src aux bit) StackMacros.Macro.skip).guard w bound _
    rw [hi]
    dsimp only [StackMacros.Macro.branch, StackMacros.Macro.skip]
    split
    · exact hext
    · trivial
  · change (StackMacros.Macro.branch (fun s => s.flag) (extend src aux bit) StackMacros.Macro.skip).result w _ = _
    rw [hi]
    cases hc : carry xs with
    | false => simp [StackMacros.Macro.branch, StackMacros.Macro.skip, di, grow, hc]
    | true =>
      simp only [StackMacros.Macro.branch, show di.state.flag = true from hc, ↓reduceIte]
      rw [hresult]
      simp [di, grow, hc]

end

end Lax362205Proofs.GrowingBinary
