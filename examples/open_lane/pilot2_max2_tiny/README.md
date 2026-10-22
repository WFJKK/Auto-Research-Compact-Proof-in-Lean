# Pilot 2 (22 October 2026): the agent's own proofs, in language version 4

The seven submissions of run `open-lane-pilot-tiny-3` (pipeline f929cfa, this project at c11b8e4), written by
the agent (claude-fable-5-1 through the Claude Code CLI) in four sessions on the tiny max2 network, with
no example proof to copy beyond the two of its prompt (`max2_tiny_brute`, `max2_tiny_scored`). Each folder
is the candidate as submitted (its manifest's `candidate_id` renamed) with the receipt the Mac's service
wrote; `scripts/test_accept.py` resubmits them and checks that the numbers reproduce. The run's record
(archive, notes, tool logs, receipts) is `results/open-lane-pilot-tiny-3` in the pipeline repository.

| round | candidate | claim | result |
|---|---|---|---|
| 1 | `r1_ColFull` | 64/64 | verified; refused scoring: `Eq.ndrec_symm` in the checker's closure (from a `match` on numeral patterns) |
| 1 | `r1_ColFull2` | 64/64 | scored: bill 951, length 1,031, description size 6,534 |
| 1 | `r1_Col21` | 21/64 | scored: bill 455, length 535 |
| 2 | `r2_Six` | 6/64 | scored: bill 189, length 269 (three singles, counted twice by symmetry) |
| 2 | `r2_Col32` | 32/64 | scored: bill 453, length 533 |
| 3 | `r3_Col38` | 38/64 | scored: bill 456, length 536 (the six-column maximum under 540) |
| 4 | `r4_Full64` | 64/64 | scored: bill 639, length 719, description size 7,502 |

The method throughout: the network is linear in the summed one-hot, so the logits of `[a, b]` are column
`a` plus column `b` of `M = U L E`; a column costs 48 counted operations; one `single` (63) establishes
that the weights are well formed (no free operation bounds a tensor's data size) and certifies its input
and the mirror; pairs are certified from column statistics by a cascade of sufficient tests (2, 6, 16
operations) with the guard folded into one `selectV` margin per column. Brute force is 4,323 and the best
hand-written proof (contraction and interval leaves) 1,227; `r4_Full64` is 719. The agent's notes also
record what the language refused it: `Graph.mk` and `Op.*` (a 29-operation guard graph), and the
match-compiler constants; both are policy questions, not bugs in its proofs.
