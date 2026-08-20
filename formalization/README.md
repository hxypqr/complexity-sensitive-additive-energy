# ComplexitySensitiveEnergy

This is the Lean 4.32 / mathlib 4.32 formalization project accompanying the paper
*Complexity-Sensitive Additive Energy and Off-Diagonal Young Inequalities on
Bounded-Degree Algebraic Varieties* ([arXiv:2608.18956v1](https://arxiv.org/abs/2608.18956)).

## Formalization Principles

- The paper's finite combinatorics, Cauchy--Schwarz arguments, recurrence
  exponents, parameter interpolation, and sharpness counts are proved internally
  in Lean.
- External results due to Walsh, Barone--Basu, Bezout, generic projection,
  Jing--Wu, and Cushman--Demeter--Wu, as well as complex interpolation and
  Fourier/Hilbert-transform results, are stated precisely only in `External/`.
  They are not proved in this project and are not declared as global `axiom`s.
- `PaperVariety` is the semantic interface for the real and complex carriers,
  complex dimension, degree, and dimensions of difference fibers. Mathlib does not
  currently provide a unified API covering all of the algebraic geometry required
  by the paper, so external geometry enters the finite proof layer through
  certificates.
- The project prohibits `sorry`, `admit`, and custom global axioms. `Audit.lean`
  prints the kernel dependencies of representative theorems.

## The Four Main Theorems

### Theorem 1.1

- `Flagged/Definitions.lean`: the theorem statement with all constants and the
  positive-dimension hypothesis made explicit.
- `Additive/UnionEnergy.lean`: a fully combinatorial proof of
  `E(⋃ A_i) ≤ k^3 ∑ E(A_i)`, with no appeal to Fourier--Minkowski.
- `Algebraic/LocalLambda.lean`: node-local concentration, `lambda <= |A|`,
  hereditary monotonicity, and flag monotonicity.
- `Flagged/ExceptionalEnergy.lean`: separate energy bounds for the stabilizer and
  bad-fiber contributions.
- `Flagged/TwoCrossing.lean`: the finite Cauchy--Schwarz core of the two crossing
  arguments.
- `Flagged/LocalInterpolation.lean`: the corrected chain
  `lambda |A|^2 <= lambda^(3-a) |A|^a <= Lambda^(3-a)|A|^a`.
- `Flagged/Recurrence.lean` and `Flagged/Main.lean`: cell contraction, wall
  absorption, and closure by strong induction.
- `Flagged/CertifiedTheorem11.lean`: the genuine lexicographic induction on
  dimension and cardinality, together with the paper-facing wrapper
  `FlaggedRecurrenceInputs → Theorem11Statement`.

### Theorem 1.2

- `QuadraticThreefold/Definitions.lean`: positive-definite simple generalized
  spectrum and the quadratic graph.
- `QuadraticThreefold/NoLines.lean`: positive-definite quadratic coordinates rule
  out nontrivial affine lines.
- `QuadraticThreefold/RankDrop.lean`: Gram-matrix estimates in the three
  eigendirections; internally the stronger `4 N^2` bound is proved first and then
  used to derive the `7 N^2` bound stated in the paper.
- `QuadraticThreefold/FiberRank.lean`: rank-drop classification for the `2×3`
  coefficient matrix in the normalized eigenbasis; a nonzero displacement can lie
  only in one of the three eigendirections.
- `QuadraticThreefold/TwoCrossing.lean`: derives the two crossing arguments, mixed
  rearrangement, Cauchy--Schwarz estimates, and the explicit cell estimate of
  Proposition 4.5 internally from active-support and genuine-incidence
  certificates.
- `QuadraticThreefold/CellRecurrence.lean` and `QuadraticThreefold/Main.lean`:
  granular-node conversion, cell power sums, wall absorption, contraction, and
  strong induction on cardinality for the actual energy.
- `Additive/Diagonal.lean` and `QuadraticThreefold/Theorem12.lean`: the exact
  diagonal lower bound `2 N^2 - N`, sharpness, and the paper-facing wrapper for the
  granular recurrence.

### Theorem 1.3

- `Weighted/Definitions.lean`: explicitly assumes `K_X,K_Y >= 1` and expands the
  constants hidden by `<<_eta` in the hereditary estimates.
- `Weighted/Correlation.lean`: directly proves the complex-phase majorant and
  `weightedEnergy <= c^4 E(A)`; it does not misinterpret an indicator bound as a
  bound for arbitrary complex coefficients.
- `Weighted/DyadicExtension.lean`: finite dyadic decomposition, phase-safe
  levelwise estimates, and finite-level assembly through the norm triangle
  inequality.
- `Weighted/RestrictedStrong.lean`: after normalization by the actual `ℓ²` norm,
  uses `m_j≤|X|` and `m_j≤4^(j+1)` to prove the dynamic-range-independent
  strong-type extension in Proposition 5.1, and proves
  `theorem13_internal : AnalysisInputs → Theorem13Statement`.
- `Weighted/OffDiagonalParameters.lean`: the alpha-two interpolation triangle and
  `theta=max(0,3-2(1/p+1/q))`.
- `Weighted/BilinearCorrelation.lean`: finite convolution/correlation identities
  and the geometric endpoint.
- `Weighted/Main.lean`: internally proves finite `ℓ^p` monotonicity and the two
  Young endpoints, connects them to the geometric `(2,2)` endpoint and the complex
  interpolation polygon, and gives
  `Theorem13EndpointInputs → Theorem13Statement`; empty support is handled by a
  separate zero-convolution branch.

### Theorem 1.4

- `Turning/Definitions.lean` and `Turning/ComplexityExistence.lean`: ordered point
  sets, signed-convex blocks, the minimum number of blocks, and its existence and
  uniqueness.
- `Turning/SlopeInvariance.lean`: internally constructs `m'=cm+dℓ`, `c≠0` from any
  two admissible complements and proves complete invariance of turning complexity.
- `Turning/ConvexInterpolation.lean` and `Turning/ConcaveReduction.lean`: the
  curvature-perturbation/upper-envelope construction of a finite strictly convex
  interpolant and reduction of concave graphs by reflection.
- `Turning/StripExponent.lean`: rigorously derives
  `6 theta (1-1/r)=4+4/(r-2)`.
- `Turning/DyadicAssembly.lean`: assembles nonuniform leaves using finite
  Jensen/Hölder inequalities.
- `Turning/Sharpness.lean` and `Turning/PacketExample.lean`: interval and power-curve
  examples, product energy, reset-forced block counts, exact `K/2≤k≤K`, and the
  sharp packet example.
- `Turning/Main.lean`: starting from the noncircular dyadic certificate supplied by
  CDW/strip results, internally proves the sixth-power estimate, nonuniform-level
  assembly, propagation of the uniform analytic constant as `A^6`, and absorption
  of `log N` into `N^eps`.
- `Turning/Theorem14.lean`: the conditional combinatorial upper bound and the fully
  internal sharp packet construction.

`FlaggedRecurrenceInputs`, `GranularThreefoldRecurrenceInputs`, and
`TurningDyadicInputs` are public, noncircular certificate-generation interfaces.
The project does not currently prove that `External.Inputs` automatically generates
them. See [the formalization status](../docs/FORMALIZATION_STATUS.md) for the precise
division between kernel-checked steps and the geometric/analytic bridge obligations
that remain open.

## Build and Audit

The project pins mathlib tag `v4.32.0` (commit
`81a5d257c8e410db227a6665ed08f64fea08e997`). From this directory, run:

```text
lake build
lake env lean ComplexitySensitiveEnergy/Audit.lean
```

For a detailed audit of the external literature and corrections to the paper, see
[the external-theorem audit](../docs/EXTERNAL_THEOREM_AUDIT.md). For each main
theorem's kernel-checked content, external boundary, and remaining glue, see
[the formalization status](../docs/FORMALIZATION_STATUS.md).
