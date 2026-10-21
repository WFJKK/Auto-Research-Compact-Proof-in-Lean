# A decision tree over truth values, in version 4 (fixture, 21 October 2026)

A reviewer's counterexample to version 3 of the counted language: with the free mask `nmask : B → N → N`,
a recursive `decode` selected `f` of the number spelled by a list of truth values, for nothing. This is
that decoder written in version 4, where a count is only a sum of concrete multiples of truth values and
a product of truth values exists only through a charged gate: the path indicator passes a gate at every
node, so a tree over `k` truth values bills `3 (2^k - 1)` gates whatever its leaves compute. With `k = 4`
on one weight of the tiny network: 4 numerals, 4 comparisons, 45 gates, bill 53, count 0 (the leaves are
`nscale 0 p`). `scripts/test_accept.py` submits it and checks the bill; the version 3 decoder itself no
longer compiles (there is no `nmask`), which the same test checks first.
