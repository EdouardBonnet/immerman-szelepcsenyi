import Lax362205.Rejection
import Lax362205.Nonreachability
import Lax362205.CountMachine
import Lax362205.ComplementClosure
import Lax362205.NLcoNL
import Lax362205Proofs.ConfigurationProofs.Configurations
import Mathlib.Tactic

namespace Lax362205Proofs

open Lax362205 Lax362205.ConfigurationCounting
open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930.NondeterministicLogarithmicSpace Lax434930.ComplementClasses
open Lax362205.ConfigurationGraph

/--
---
conclusion: Lax362205.Rejection.correct
assumptions:
  - Lax362205.Nonreachability.correct
---
Apply the nonreachability certificate to each possible accepting configuration.
-/
lemma counting_rejection (M : Machine) (w : Word) (s : ℕ) (hs : M.UsesSpace w s) :
    RejectsByCounting M w s ↔ ¬ M.Accepts w := by
  rw [← Lax362205Proofs.ConfigurationProofs.configuration_acceptance M w s hs]
  simp only [RejectsByCounting, AcceptsBounded, Nonreachability.correct, not_exists, not_and]

/--
---
conclusion: Lax362205.ComplementClosure.closed
assumptions:
  - Lax362205.CountMachine.implement
  - Lax362205.Rejection.correct
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
conclusion: Lax362205.NLcoNL.nl_eq_conl
assumptions:
  - Lax362205.ComplementClosure.closed
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

end Lax362205Proofs
