# PHJ-FRI Stage 3 Lean verification scratch branch

This isolated branch is used only to kernel-check exact arithmetic certificates
for the research question:

> Can a seed-parametric hidden Hasse-jet annihilator module prove a
> direct-threshold Reed–Solomon proximity gap for smooth FRI domains beyond the
> Johnson radius?

The workflow checks out the public Proximity Prize repository at commit
`b3fac81ad2b1ee609672b04bd3c3ee1ca5c06884`, thereby inheriting its pinned Lean
4.32.2 / Lake environment.  It copies and compiles the standalone K14
certificate.  Nothing in this branch modifies the production `main` branch or
claims the unformalized MPCB/seed-anchored geometric theorem.

Verification layers:

1. `PHJ_FRI_K14_Arithmetic.lean`: exact Johnson crossing, interpolation slack,
   current coordinate projection gates, alignment-budget quotient, and
   challenge-field gate.
2. Planned: parameterized wrappers around the existing contact geometry.
3. Planned: seed-anchored resultant pole budget replacing all-coordinate
   separability for the stronger M14 profile.
