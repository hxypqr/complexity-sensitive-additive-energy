# Formalization roadmap

This directory is reserved for machine-checked definitions and proofs. No proof assistant has been selected yet. Lean 4 with mathlib is a natural candidate because of its support for finite sets, finite sums, measure theory, and harmonic-analysis infrastructure, but the choice should be recorded before code is added.

## Proposed milestones

1. Define the difference representation function for a finite subset of an additive group.
2. Define additive energy as a finite sum of squared representation counts.
3. Prove the universal lower and upper bounds for additive energy.
4. Formalize weighted additive energy and the basic convolution identities.
5. Isolate hereditary energy estimates as reusable hypotheses.
6. Derive the elementary weighted $L^4$ and Young-inequality consequences from those hypotheses.
7. Formalize algebraic-geometric and polynomial-partitioning inputs only after their exact interfaces are stable.

## Proof discipline

- Each formal theorem should cite the corresponding manuscript label.
- Record any additional assumptions introduced by the formalization.
- Keep experimental code separate from accepted proofs.
- Prefer small, reusable lemmas over a monolithic translation of the paper.
