import Lax733996.Rejection
import Lax733996.Nonreachability
import Lax733996.CountMachine
import Lax733996.ComplementClosure
import Lax733996.NLcoNL
import Lax307052.Runs
import Mathlib.Tactic

namespace Lax733996Proofs

open Lax733996 Lax733996.ConfigurationCounting
open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930.NondeterministicLogarithmicSpace Lax434930.ComplementClasses
open Lax307052.ConfigurationGraph

/--
---
conclusion: Lax733996.Rejection.correct
assumptions:
  - Lax307052.Runs.acceptance
  - Lax733996.Nonreachability.correct
---
Apply the nonreachability certificate to each possible accepting configuration.
-/
lemma counting_rejection (M : Machine) (w : Word) (s : ℕ) (hs : M.UsesSpace w s) :
    RejectsByCounting M w s ↔ ¬ M.Accepts w := by
  rw [← Lax307052.Runs.acceptance M w s hs]
  simp only [RejectsByCounting, AcceptsBounded, Nonreachability.correct, not_exists, not_and]

/--
---
conclusion: Lax733996.ComplementClosure.closed
assumptions:
  - Lax733996.CountMachine.implement
  - Lax733996.Rejection.correct
---
The counting machine accepts the complement and preserves a logarithmic space bound.
-/
lemma complement_closed (A : Language) : A ∈ NL → Aᶜ ∈ NL := by
  rintro ⟨c, hc, M, hdec, hbound⟩
  obtain ⟨d, D, hd, hD, hb⟩ := CountMachine.implement M c hc hbound
  refine ⟨d, hd, D, ?_, hb⟩
  intro w
  exact ⟨(hD w).1,
    (hD w).2.trans ((Rejection.correct M w _ (hbound w)).trans (not_congr (hdec w).2))⟩

/--
---
conclusion: Lax733996.NLcoNL.nl_eq_conl
assumptions:
  - Lax733996.ComplementClosure.closed
---
Apply complement closure in both directions and use double complementation.
-/
theorem immerman_szelepcsenyi : NL = coNL := by
  ext A
  change A ∈ NL ↔ Aᶜ ∈ NL
  constructor
  · exact ComplementClosure.closed A
  · intro h
    simpa using ComplementClosure.closed Aᶜ h

end Lax733996Proofs
