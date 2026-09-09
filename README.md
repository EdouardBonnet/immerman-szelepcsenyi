# The Immerman–Szelepcsényi theorem

Lax submission **lax-733996**, stating `NL = coNL` for the machine classes
of lax-434930. The finite configuration graphs and their correspondence with
machine runs are reused from lax-307052.

The checked argument proves that an exact census contains the entire
reachable layer, that its successor classifications are correct, and that
inductive counts certify nonreachability. The complement construction and
the main equality have proofs relative to `CountMachine.implement`.

That lemma is open: it must construct a nondeterministic machine implementing
the certificate predicate in logarithmic space, with every branch halting.
The finite sets and functions in the certificate semantics are mathematical
witnesses. They must be generated sequentially by the implementation;
storing them explicitly would not establish a logarithmic space bound.

Only the main equality is labeled `theorem`; its supporting statements are
`lemma`. The proof network records actual Lean dependencies, including the
open machine construction. Run `lax build . --replay` to validate.
