import Lax362205.Counting

/-!
---
title: Correctness of nonreachability certificates
type: lemma
---
A valid sequence of counts and a final census omitting the target exist
exactly when the target is unreachable from the source.
-/

namespace Lax362205.Nonreachability

open Lax362205.Reachability Counting

axiom correct {N : ℕ} (G : Graph N) (a b : Fin N) :
  NonreachCertificate G a b ↔ ¬ Reachable G a b

end Lax362205.Nonreachability
