import Lax733996Proofs.ChoiceRoutines

/-! Finite loop bounds for all branches, with a separate construction of
successful executions from witnesses for the individual iterations. -/

namespace Lax733996Proofs.ChoiceLanguage

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax733996Proofs.ConfigurationProofs

variable {K Γ σ : Type}

lemma bounded_loop_total (w : Word) (bound limit : ℕ) (test : σ → Bool) (body : Command K Γ σ)
    (I : ℕ → Data K Γ σ → Prop)
    (hg : ∀ i d, I i d → Good w bound d)
    (hstop : ∀ d, I limit d → test d.state = false)
    (hbody : ∀ i d, i < limit → I i d → test d.state = true → Total w bound body d)
    (hnext : ∀ i d e, i < limit → I i d → test d.state = true → Exec w bound body d e → I (i + 1) e)
    (i : ℕ) (d : Data K Γ σ) (hi : i ≤ limit) (hd : I i d) :
    Total w bound (.loop test body) d := by
  have go (remaining : ℕ) : ∀ i d, i + remaining = limit → I i d → Total w bound (.loop test body) d := by
    induction remaining with
    | zero =>
      intro i d hi hd
      have he : i = limit := by omega
      subst i
      exact .loop_false test body d (hg limit d hd) (hstop d hd)
    | succ remaining ih =>
      intro i d hi hd
      cases ht : test d.state with
      | false => exact .loop_false test body d (hg i d hd) ht
      | true =>
        apply Total.loop_true ht (hbody i d (by omega) hd ht)
        intro e he
        exact ih (i + 1) e (by omega) (hnext i d e (by omega) hd ht he)
  exact go (limit - i) i d (by omega) hd

lemma bounded_loop_sound (w : Word) (bound limit : ℕ) (test : σ → Bool) (body : Command K Γ σ)
    (I : ℕ → Data K Γ σ → Prop)
    (hstop : ∀ d, I limit d → test d.state = false)
    (hnext : ∀ i d e, i < limit → I i d → test d.state = true → Exec w bound body d e → I (i + 1) e)
    (i : ℕ) (d e : Data K Γ σ) (hi : i ≤ limit) (hd : I i d)
    (h : Exec w bound (.loop test body) d e) :
    (∃ j, j ≤ limit ∧ I j e) ∧ test e.state = false := by
  apply exec_loop_invariant (fun d => ∃ j, j ≤ limit ∧ I j d) ?_ h ⟨i, hi, hd⟩
  rintro a b ⟨j, hj, hja⟩ ht he
  have hlt : j < limit := by
    by_contra hn
    have hh : j = limit := by omega
    subst j
    have := hstop a hja
    simp [ht] at this
  exact ⟨j + 1, by omega, hnext j a b hlt hja ht he⟩

lemma bounded_loop_complete (w : Word) (bound limit : ℕ) (test : σ → Bool) (body : Command K Γ σ)
    (I : ℕ → Data K Γ σ → Prop)
    (hg : ∀ i d, I i d → Good w bound d)
    (hstop : ∀ d, I limit d → test d.state = false)
    (hstep : ∀ i d, i < limit → I i d →
      test d.state = true ∧ ∃ e, Exec w bound body d e ∧ I (i + 1) e)
    (i : ℕ) (d : Data K Γ σ) (hi : i ≤ limit) (hd : I i d) :
    ∃ e, Exec w bound (.loop test body) d e ∧ I limit e := by
  have go (remaining : ℕ) : ∀ i d, i + remaining = limit → I i d →
      ∃ e, Exec w bound (.loop test body) d e ∧ I limit e := by
    induction remaining with
    | zero =>
      intro i d hi hd
      have he : i = limit := by omega
      subst i
      exact ⟨d, .loop_false test body d (hg limit d hd) (hstop d hd), hd⟩
    | succ remaining ih =>
      intro i d hi hd
      obtain ⟨ht, e, he, hie⟩ := hstep i d (by omega) hd
      obtain ⟨f, hf, hif⟩ := ih (i + 1) e (by omega) hie
      exact ⟨f, .loop_true ht he hf, hif⟩
  exact go (limit - i) i d (by omega) hd

end Lax733996Proofs.ChoiceLanguage
