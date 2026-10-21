# The agent's column proof, ported to language v3 (human-assisted, 21 October 2026)

`max2_tiny_agent_cols23` is the agent's pilot proof in the first counted language. This is the same
argument and the same plan, ported by hand to version 3 of the interface (a checker as a function of the
interpreter, no branching on a truth value): `I.band` for `&&`, `I.nmask` for `if ok then ... else ...`,
`I.countB`, `I.bfalse`, the specification lemmas restated about `Interp.counting`. The bill is 549 (the
agent's 458 plus 91 charged gates), the length 629 with E = 80.

It is an integration test of the interface: a meaningful method stays expressible, provable and scoreable
under it. Whether the agent can use the interface by itself is what the next pilot run establishes.
