# The Immerman–Szelepcsényi theorem

Submission [lax-733996](https://laxarchive.org/lax-733996/), proving `NL = coNL` for the machine classes
of [lax-434930](https://laxarchive.org/lax-434930/). The finite configuration graphs and their correspondence with
machine runs are included locally, using the checked 4.33.0 sources from that submission.

The proof constructs the counting machine. A fixed collection of binary
registers stores vertices, depths, and counts. Paths and census witnesses
are generated sequentially. Loop invariants prove soundness, completeness,
and termination of every nondeterministic branch. A verified compiler
translates the register program into the finite Turing machine model.

The input length is counted in binary and converted into a logarithmic
register width. The graph query reuses the configuration encoding and stack
routines included with the configuration proofs. All scratch registers and
compiler microsteps satisfy the space bound.

`CountMachine.implement` assumes that the simulated machine obeys its
logarithmic space bound. The complement theorem supplies this hypothesis;
the main statement remains `NL = coNL`.

Only the main equality is labeled `theorem`; its supporting statements are
`lemma`. The proof network records actual Lean dependencies. Run
`lax build . --replay` and the workspace proof-closure audit to validate.

The submission targets Lean and Mathlib 4.33.0 and includes an annotated companion in [paper/main.tex](paper/main.tex). The class definitions, encodings, and result statements are preserved; proof changes address imports and Lean 4.33 elaboration.
