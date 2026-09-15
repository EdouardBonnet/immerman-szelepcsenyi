import Lax733996Proofs.CountingPrimitives

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax733996Proofs.ConfigurationProofs
open SearchProgram (Register)
open StackMacros (Macro)
open scoped Classical

noncomputable section

variable {M : Machine}

abbrev reg (d : Data M) (r : Register) := d.store (SearchProgram.key r)

def Keeps (written : Finset Register) (d e : Data M) : Prop :=
  ∀ r, r ∉ written → reg e r = reg d r

lemma Keeps.refl (s : Finset Register) (d : Data M) : Keeps s d d := fun _ _ => rfl

lemma Keeps.mono {s t : Finset Register} {d e : Data M} (h : Keeps s d e) (hst : s ⊆ t) :
    Keeps t d e := fun r hr => h r (fun hs => hr (hst hs))

lemma Keeps.trans {s : Finset Register} {d e f : Data M} (h : Keeps s d e) (hf : Keeps s e f) :
    Keeps s d f := fun r hr => (hf r hr).trans (h r hr)

lemma Keeps.union {s t : Finset Register} {d e f : Data M} (h : Keeps s d e) (hf : Keeps t e f) :
    Keeps (s ∪ t) d f := by
  intro r hr
  have hn : r ∉ s ∧ r ∉ t := by simpa using hr
  exact (hf r hn.2).trans (h r hn.1)

lemma word_eq_iff (m x y : ℕ) (hx : x < 2 ^ m) (hy : y < 2 ^ m) :
    (SearchProgram.word m x : List (GraphQuery.Alphabet M Unit)) = SearchProgram.word m y ↔ x = y := by
  simpa only [Fin.ext_iff] using SearchProgram.word_eq_fin_iff (β := GraphQuery.Beta M Unit)
    m ⟨x, hx⟩ ⟨y, hy⟩

lemma copy_effect (w : Word) (bound : ℕ) (src dst : Register) (hne : src ≠ dst) (d : Data M) :
    Keeps {dst} d ((copy M src dst).result w d) ∧
      reg ((copy M src dst).result w d) dst = reg d src ∧
      ((copy M src dst).result w d).state.user = d.state.user := by
  rw [(copy_spec M w bound src dst hne d).2]
  refine ⟨?_, by simp [reg], rfl⟩
  intro r hr
  simp only [Finset.mem_singleton] at hr
  simp [reg, GraphQuery.key, SearchProgram.key, hr]

lemma fill_effect (w : Word) (bound m : ℕ) (dst : Register) (hne : dst ≠ .width)
    (extra : Option Bool) (d : Data M)
    (hw : reg d .width = SearchProgram.unary m) (hb : m + 1 < bound) :
    Keeps {dst} d ((fill M dst extra).result w d) ∧
      reg ((fill M dst extra).result w d) dst = filledWord M m extra ∧
      ((fill M dst extra).result w d).state.user = d.state.user := by
  rw [(fill_spec M w bound m dst hne extra d hw hb).2]
  refine ⟨?_, by simp [reg], rfl⟩
  intro r hr
  simp only [Finset.mem_singleton] at hr
  simp [reg, GraphQuery.key, SearchProgram.key, hr]

lemma increment_effect (w : Word) (bound m n : ℕ) (hn : n < 2 ^ m) (r : Register) (d : Data M)
    (hr : reg d r = SearchProgram.word m n) :
    Keeps {r} d ((increment M r).result w d) ∧
      reg ((increment M r).result w d) r = SearchProgram.word m (n + 1) ∧
      ((increment M r).result w d).state.user = d.state.user ∧
      ((increment M r).result w d).state.flag = decide (n + 1 = 2 ^ m) := by
  rw [(increment_spec M w bound m n hn r d hr).2]
  refine ⟨?_, by simp [reg], rfl, rfl⟩
  intro s hs
  simp only [Finset.mem_singleton] at hs
  simp [reg, GraphQuery.key, SearchProgram.key, hs]

lemma decrement_effect (w : Word) (bound m n : ℕ) (hn : n < 2 ^ m) (r : Register) (d : Data M)
    (hr : reg d r = SearchProgram.word m n) :
    Keeps {r} d ((decrement M r).result w d) ∧
      reg ((decrement M r).result w d) r = SearchProgram.word m (if n = 0 then 2 ^ m - 1 else n - 1) ∧
      ((decrement M r).result w d).state.user = d.state.user ∧
      ((decrement M r).result w d).state.flag = decide (n = 0) := by
  rw [(decrement_spec M w bound m n hn r d hr).2]
  refine ⟨?_, by simp [reg], rfl, rfl⟩
  intro s hs
  simp only [Finset.mem_singleton] at hs
  simp [reg, GraphQuery.key, SearchProgram.key, hs]

lemma compare_effect (w : Word) (bound : ℕ) (src dst : Register) (d : Data M) :
    Keeps ∅ d ((compare M src dst).result w d) ∧
      ((compare M src dst).result w d).state.user = d.state.user ∧
      ((compare M src dst).result w d).state.flag = decide (reg d src = reg d dst) := by
  rw [(compare_spec M w bound src dst d).2]
  refine ⟨?_, rfl, rfl⟩
  intro r _
  simp [reg, GraphQuery.key, SearchProgram.key]

@[simp] lemma requireFlag_valid (w : Word) (d : Data M) :
    valid M ((requireFlag M).result w d).state = (valid M d.state && d.state.flag) := by
  cases hf : d.state.flag <;> simp [requireFlag, Macro.assign, StackLanguage.assigned, valid, hf]

@[simp] lemma requireAnswer_valid (w : Word) (d : Data M) :
    valid M ((requireAnswer M).result w d).state = (valid M d.state && d.state.user.answer) := by
  cases hf : d.state.user.answer <;> simp [requireAnswer, Macro.assign, StackLanguage.assigned, valid, hf]

end

end Lax733996Proofs.CountingProgram
