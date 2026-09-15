import Lax733996Proofs.ConfigurationProofs.Reachability
import Lax733996Proofs.ConfigurationProofs.ShortPaths
import Lax733996Proofs.ConfigurationProofs.Reachability

set_option backward.isDefEq.respectTransparency false
namespace Lax733996Proofs.ConfigurationProofs
open Lax733996 Lax733996.Reachability
/--
The recursion covers every simple path because $N\leq 2^{\lceil\log_2 N\rceil}$.
-/
lemma finite_reachability {N : ℕ} (G : Graph N) (a b : Fin N) :
    search G (Nat.clog 2 N) a b = true ↔ Reachable G a b := by
  rw [Lax733996Proofs.ConfigurationProofs.recursive_reachability]
  constructor
  · rintro ⟨k, _, h⟩
    exact walk_reachable h
  · intro h
    obtain ⟨k, hk, hw⟩ := (Lax733996Proofs.ConfigurationProofs.short_paths G a b).mp h
    exact ⟨k, (Nat.le_of_lt hk).trans (Nat.le_pow_clog (by decide) N), hw⟩

end Lax733996Proofs.ConfigurationProofs
