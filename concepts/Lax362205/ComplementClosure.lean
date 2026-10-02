import Lax434930.NondeterministicLogarithmicSpace

/-!
---
title: Complementing a logarithmic space language
type: lemma
---
The complement of a language in $\mathrm{NL}$ also belongs to $\mathrm{NL}$.
-/

namespace Lax362205.ComplementClosure

open Lax434930.PolynomialTime Lax434930.NondeterministicLogarithmicSpace

axiom closed (A : Language) : A ∈ NL → Aᶜ ∈ NL

end Lax362205.ComplementClosure
