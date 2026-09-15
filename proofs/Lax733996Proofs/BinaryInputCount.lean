import Lax733996Proofs.GrowingBinary
import Lax733996Proofs.ConfigurationProofs.InputRoutines

namespace Lax733996Proofs.BinaryInputCount

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax434930.SpaceBounds
open Lax733996Proofs.ConfigurationProofs
open StackLanguage (Exec Good assigned moved)
open StackMacros (Macro)
open scoped Classical

noncomputable section

def bits : ℕ → List Bool
  | 0 => []
  | n + 1 => GrowingBinary.grow (bits n)

lemma bits_value (n : ℕ) : BinaryCounter.value (bits n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bits, GrowingBinary.grow_value, ih]

lemma bits_canonical (n : ℕ) : GrowingBinary.Canonical (bits n) := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih => exact GrowingBinary.grow_canonical ih

lemma bits_length (n : ℕ) (hn : 0 < n) : (bits n).length = Nat.log 2 n + 1 := by
  simpa only [bits_value] using GrowingBinary.length_eq_log (bits_canonical n) (by simpa only [bits_value] using hn)

lemma bits_bound (n size : ℕ) (hn : n ≤ size + 2) : (bits n).length ≤ logSpace size + 1 :=
  GrowingBinary.length_bound (bits_canonical n) (by simpa only [bits_value] using hn)

variable {K Γ σ : Type} [Inhabited Γ]

abbrev Data := StackRoutines.Data (K := K) (Γ := Γ) (σ := σ)

def advance : Macro K Γ σ := (Macro.move (fun _ => .right)).seq Macro.sample

def body (src aux : K) (bit : Bool → Γ) (readBit : Γ → Bool) : Macro K Γ σ :=
  (GrowingBinary.program src aux bit readBit).seq advance

def loopCode (src aux : K) (bit : Bool → Γ) (readBit : Γ → Bool) :
    StackRoutines.Code (K := K) (Γ := Γ) (σ := σ) :=
  .loop (fun s => decide (s.input ≠ .rightEnd)) (body src aux bit readBit).code

lemma body_spec (w : Word) (bound : ℕ) (src aux : K) (hne : src ≠ aux)
    (bit : Bool → Γ) (readBit : Γ → Bool) (hbit : ∀ b, readBit (bit b) = b)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (n : ℕ)
    (hd : Good w bound d) (hs : d.store src = (bits n).map bit) (ha : d.store aux = [])
    (hb : (bits n).length + 1 < bound) (hi : d.inputHead < w.length + 1) :
    ∃ e, Exec w bound (body src aux bit readBit).code d e ∧
      e.inputHead = d.inputHead + 1 ∧ e.state.input = readInput w e.inputHead ∧
      e.store src = (bits (n + 1)).map bit ∧
      (∀ k, k ≠ src → e.store k = d.store k) ∧ e.state.user = d.state.user := by
  obtain ⟨hg, hr⟩ := GrowingBinary.program_correct w bound src aux hne bit readBit hbit d (bits n) hs ha hb
  let e := (body src aux bit readBit).result w d
  have he : Exec w bound (body src aux bit readBit).code d e :=
    (body src aux bit readBit).correct w bound d hd ⟨hg, trivial, trivial⟩
  have heq : e =
      ⟨{d.state with
          value := none
          flag := BinaryCounter.carry (bits n)
          input := readInput w (d.inputHead + 1)}, d.inputHead + 1,
        Function.update d.store src ((bits (n + 1)).map bit)⟩ := by
    dsimp only [e, body, Macro.seq]
    rw [hr]
    simp [advance, Macro.seq, Macro.move, Macro.sample, assigned, moved, Move.apply,
      Nat.min_eq_left (by omega : d.inputHead ≤ w.length), show d.inputHead ≤ w.length by omega, bits]
  refine ⟨e, he, ?_⟩
  rw [heq]
  exact ⟨rfl, rfl, by simp, by intro k hk; simp [hk], rfl⟩

lemma loop_exec (w : Word) (bound : ℕ) (src aux : K) (hne : src ≠ aux)
    (bit : Bool → Γ) (readBit : Γ → Bool) (hbit : ∀ b, readBit (bit b) = b)
    (remaining n : ℕ) (d : Data (K := K) (Γ := Γ) (σ := σ))
    (hd : Good w bound d) (hi : d.inputHead + remaining = w.length + 1)
    (hinput : d.state.input = readInput w d.inputHead)
    (hs : d.store src = (bits n).map bit) (ha : d.store aux = [])
    (hn : n + remaining ≤ w.length + 2) (hb : logSpace w.length + 2 < bound) :
    ∃ e, Exec w bound (loopCode src aux bit readBit) d e ∧
      e.inputHead = w.length + 1 ∧ e.store src = (bits (n + remaining)).map bit ∧
      (∀ k, k ≠ src → e.store k = d.store k) ∧ e.state.user = d.state.user := by
  induction remaining generalizing d n with
  | zero =>
    have hhead : d.inputHead = w.length + 1 := by omega
    have ht : d.state.input = .rightEnd := by
      rw [hinput]
      exact (InputRoutines.read_right _ _).mpr (by omega)
    exact ⟨d, .loop_false _ _ _ hd (by simp [ht]), hhead, by simpa using hs,
      by intro k _; rfl, rfl⟩
  | succ remaining ih =>
    have hlen := bits_bound n w.length (by omega)
    obtain ⟨e, he, hei, heinput, hes, heframe, heu⟩ :=
      body_spec w bound src aux hne bit readBit hbit d n hd hs ha (by omega) (by omega)
    obtain ⟨f, hf, hfi, hfs, hfframe, hfu⟩ := ih (n + 1) e he.good.2 (by omega) heinput hes
      (by rw [heframe aux (Ne.symm hne)]; exact ha) (by omega)
    refine ⟨f, .loop_true ?_ he hf, hfi, ?_, ?_, hfu.trans heu⟩
    · simp [hinput, InputRoutines.read_right, show ¬ w.length + 1 ≤ d.inputHead by omega]
    · simpa only [Nat.add_assoc, Nat.add_comm 1 remaining] using hfs
    · intro k hk
      exact (hfframe k hk).trans (heframe k hk)

def seed (src aux : K) (bit : Bool → Γ) (readBit : Γ → Bool) : Macro K Γ σ :=
  (GrowingBinary.program src aux bit readBit).seq
    ((GrowingBinary.program src aux bit readBit).seq advance)

def countCode (src aux : K) (bit : Bool → Γ) (readBit : Γ → Bool) :
    StackRoutines.Code (K := K) (Γ := Γ) (σ := σ) :=
  .seq (seed src aux bit readBit).code (loopCode src aux bit readBit)

lemma count_exec (w : Word) (bound : ℕ) (src aux : K) (hne : src ≠ aux)
    (bit : Bool → Γ) (readBit : Γ → Bool) (hbit : ∀ b, readBit (bit b) = b)
    (d : Data (K := K) (Γ := Γ) (σ := σ)) (hd : Good w bound d)
    (hi : d.inputHead = 0) (hs : d.store src = []) (ha : d.store aux = [])
    (hb : logSpace w.length + 2 < bound) :
    ∃ e, Exec w bound (countCode src aux bit readBit) d e ∧
      e.inputHead = w.length + 1 ∧ e.store src = (bits (w.length + 2)).map bit ∧
      (∀ k, k ≠ src → e.store k = d.store k) ∧ e.state.user = d.state.user := by
  have hpos : 0 < logSpace w.length := by
    apply Nat.lt_of_lt_of_le (by decide : 0 < 1)
    exact Nat.le_log_of_pow_le (by decide) (by simp)
  obtain ⟨hg₀, hr₀⟩ := GrowingBinary.program_correct w bound src aux hne bit readBit hbit d []
    (by simpa using hs) ha (by simp; omega)
  let d₁ := (GrowingBinary.program src aux bit readBit).result w d
  have he₁ : Exec w bound (GrowingBinary.program src aux bit readBit).code d d₁ :=
    (GrowingBinary.program src aux bit readBit).correct w bound d hd hg₀
  have hs₁ : d₁.store src = (bits 1).map bit := by simp [d₁, hr₀, bits]
  have ha₁ : d₁.store aux = [] := by simp [d₁, hr₀, Ne.symm hne, ha]
  have hi₁ : d₁.inputHead = 0 := by simp [d₁, hr₀, hi]
  obtain ⟨e, he, hei, heinput, hes, heframe, heu⟩ := body_spec w bound src aux hne bit readBit hbit
    d₁ 1 he₁.good.2 hs₁ ha₁ (by have hlen := bits_bound 1 w.length (by omega); omega)
    (by rw [hi₁]; omega)
  obtain ⟨f, hf, hfi, hfs, hfframe, hfu⟩ := loop_exec w bound src aux hne bit readBit hbit
    w.length 2 e he.good.2 (by omega) heinput hes
    (by rw [heframe aux (Ne.symm hne)]; exact ha₁) (by omega) hb
  refine ⟨f, .seq (.seq he₁ he) hf, hfi, ?_, ?_, ?_⟩
  · simpa only [Nat.add_comm 2] using hfs
  · intro k hk
    rw [hfframe k hk, heframe k hk]
    simp [d₁, hr₀, hk]
  · rw [hfu, heu]
    simp [d₁, hr₀]

end

end Lax733996Proofs.BinaryInputCount
