# An agent-written scored proof (pilot, 20 October 2026)

The third submission of round 1 of the open-lane pilot on the tiny max2 network, written by the agent
(claude-fable-5-1 through the Claude Code CLI) in one session with the four tools and no rule descriptions:
the logits of (a, b) are column a plus column b of M = U L E; the checker computes the needed columns in the
counted language, adds two per pair and compares, with one `single` call to establish the weights' shapes;
every step has its specification lemma, and the evaluator's output formula is proved symbolically. It
covers 23 of the 64 inputs for a bill of 458, chosen to fit the 540 budget of the Q_grid grid.

The service verified it (23 of 64, kernel-checked) and refused scoring under the first policy, whose
literal measure counted Lean's equation lemmas and charged the three weight names 25: 97 against a budget
of 42. Later that day the language itself changed: a reviewer showed that the first language (a concrete
`CostM Nat` with concrete booleans) let a checker turn charged comparisons into free arithmetic, and the
language became an interface (`Checker := (I : Interp) → I.M I.N`, docs/COUNTED.md). This module is a
program of the first language; the service still verifies its mathematics and refuses to score it, since
its checker uses `CostM` directly. The test suite expects exactly that.

Kept unchanged, as the agent wrote it, as the record of the pilot's first round.
