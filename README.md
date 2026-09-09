# The Immerman–Szelepcsényi theorem

Lax submission **lax-733996**, stating `NL = coNL` for the machine classes
of lax-434930. The finite configuration graphs and their correspondence with
machine runs are reused from lax-307052.

The proof constructs the counting machine. A fixed collection of binary
registers stores vertices, depths, and counts. Paths and census witnesses
are generated sequentially. Loop invariants prove soundness, completeness,
and termination of every nondeterministic branch. A verified compiler
translates the register program into the finite Turing machine model.

The input length is counted in binary and converted into a logarithmic
register width. The graph query reuses the configuration encoding and stack
routines from the closed Savitch submission. All scratch registers and
compiler microsteps satisfy the space bound.

`CountMachine.implement` assumes that the simulated machine obeys its
logarithmic space bound. The complement theorem supplies this hypothesis;
the main statement remains `NL = coNL`.

Only the main equality is labeled `theorem`; its supporting statements are
`lemma`. The proof network records actual Lean dependencies. Run
`lax build . --replay` and the workspace proof-closure audit to validate.
