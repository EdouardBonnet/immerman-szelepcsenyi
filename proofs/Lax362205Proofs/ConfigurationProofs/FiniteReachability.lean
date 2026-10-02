import Lax362205Proofs.ConfigurationProofs.Reachability
import Lax362205Proofs.ConfigurationProofs.ShortPaths
import Lax362205Proofs.ConfigurationProofs.Reachability

set_option backward.isDefEq.respectTransparency false
namespace Lax362205Proofs.ConfigurationProofs
open Lax362205 Lax362205.Reachability
/--
The recursion covers every simple path because $N\leq 2^{\lceil\log_2 N\rceil}$.
-/
lemma finite_reachability {N : ℕ} (G : Graph N) (a b : Fin N) :
    search G (Nat.clog 2 N) a b = true ↔ Reachable G a b := by
  rw [Lax362205Proofs.ConfigurationProofs.recursive_reachability]
  constructor
  · rintro ⟨k, _, h⟩
    exact walk_reachable h
  · intro h
    obtain ⟨k, hk, hw⟩ := (Lax362205Proofs.ConfigurationProofs.short_paths G a b).mp h
    exact ⟨k, (Nat.le_of_lt hk).trans (Nat.le_pow_clog (by decide) N), hw⟩

end Lax362205Proofs.ConfigurationProofs
