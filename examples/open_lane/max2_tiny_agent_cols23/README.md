# An agent-written scored proof (pilot, 20 October 2026)

The third submission of round 1 of the open-lane pilot on the tiny max2 network, written by the agent
(claude-fable-5-1 through the Claude Code CLI) in one session with the four tools and no rule descriptions:
the logits of (a, b) are column a plus column b of M = U L E; the checker computes the needed columns in the
counted language, adds two per pair and compares, with one `single` call to establish the weights' shapes;
every step has its specification lemma, and the evaluator's output formula is proved symbolically. It
covers 23 of the 64 inputs for a bill of 458, chosen to fit the 540 budget of the Q_grid grid.

The service verified it (23 of 64, kernel-checked) and refused scoring under the first policy, whose
literal measure counted Lean's equation lemmas and charged the three weight names 25: 97 against a budget
of 42. The measure was corrected after this submission (equation lemmas weigh nothing, a string 1 per 8
bytes); the test suite now expects this module to be scored at length 538.

Kept unchanged, as the agent wrote it, as a fixture.
