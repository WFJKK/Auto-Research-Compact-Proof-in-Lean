# The agent's column proof, ported to language v4 (human-assisted, 21 October 2026)

`max2_tiny_agent_cols23` is the agent's pilot proof in the first counted language. This is the same
argument and the same plan, ported by hand to version 4 of the interface (a checker as a function of the
interpreter, no branching on a truth value, counts as sums of concrete multiples of truth values):
`I.band` for `&&`, `I.nscale k` for `if ok then k else 0`, `I.bfalse`, the specification lemmas restated
about `Interp.counting`. The bill is 562 (the agent's 458 plus 104 charged gates: 91 inside the pair
checks and 13 joining each pair's result with the single's), the length 642 with E = 80. Under version 3
the single's result masked the whole count through the free `nmask`, and the bill was 549; version 4 has
no free mask, so that join costs one gate per pair.

It is an integration test of the interface: a meaningful method stays expressible, provable and scoreable
under it. Whether the agent can use the interface by itself is what the next pilot run establishes.
