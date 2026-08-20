# Formalization Status and Trust Boundary

This document distinguishes three kinds of content:

1. **Kernel-checked Lean proofs:** the theorem body contains a complete proof term;
2. **External results from the literature:** these are stated precisely only in
   `External/` and are not proved in this project;
3. **Geometric certificate generators:** external results from algebraic geometry
   produce finite certificates, while Lean uses only their partition, support-count,
   cardinality, and dimension-drop fields.

The project does not use `sorry`, `admit`, custom `axiom` declarations, or `opaque`
definitions to bypass internal proofs.

## Theorem 1.1

Kernel-checked in Lean:

- exact identities relating difference representation counts, mixed energy, and
  mathlib's `Finset.addEnergy`;
- the combinatorial inequality
  `E(⋃ A_i) ≤ k^3 ∑ E(A_i)` for finite pairwise-disjoint unions, without a
  Fourier/Minkowski black box;
- separate exceptional-energy bounds for stabilizer subcollections and bad translate
  fibers;
- two crossing arguments, mixed-energy rearrangement, and two finite
  Cauchy--Schwarz arguments;
- the corrected order of passage from the local `lambda` to the global `Lambda`;
- cell power sums, wall assembly, contraction constants, and strong induction for
  the actual quantity `energy A`.

External/certificate boundary: Walsh partitioning, the Barone--Basu connected-component
bound, Bezout, and irreducible decomposition should produce the node/wall
certificate. The certificate is not permitted to contain the energy conclusion
being proved. The project does not yet prove the generation bridge
`External.Inputs → FlaggedRecurrenceInputs`; consequently,
`theorem11_of_recurrenceInputs` is a kernel-checked conditional implication.

## Theorem 1.2

Kernel-checked in Lean:

- positive-definite quadratic coordinates rule out nontrivial midpoints and affine
  lines;
- rank-drop classification for the normalized `2×3` difference-fiber matrix;
- a Gram-matrix estimate for 0--1 incidences, first giving the stronger bound
  `4 N^2` and then the `7 N^2` bound used in the paper;
- the two crossing arguments of Proposition 4.5, mixed-energy rearrangement, two
  finite Cauchy--Schwarz arguments, and the explicit estimate
  `14(D N^2 + D^2 ∑ E(X_i))` derived from the granular active-support/Gram
  certificate; the final cell estimate is no longer a field of the granular
  certificate;
- the exact `D^(-1-3 eps)` exponent calculation, absorption of lower-order wall
  terms, and strong induction on cardinality;
- the universal diagonal lower bound `2 N^2 - N`.

External/certificate boundary: the bridge from the original quadratic coordinates
to the normalized eigenbasis fiber matrix; injection of the actual rank-drop
quadruples into the three incidence Gram matrices and the active-support
certificate; partitioning of the three-dimensional parameter space; and the
two-dimensional wall decomposition, curve bound, generic Freiman-2 projection,
and Jing--Wu assembly. `GenericSurfaceProjectionStatement` now explicitly contains
the no-line source hypothesis, preservation of non-collinear triples, closure of
the complex Zariski image, degree control for irreducible nonplanar components,
and the line-occupancy bound required by Jing--Wu. The project does not yet prove
the generation bridge
`External.Inputs → GranularThreefoldRecurrenceInputs`; the upper bound is therefore
a kernel-checked conditional implication and should not be described as an
unconditional complete formalization.

## Theorem 1.3

Kernel-checked in Lean:

- a pointwise correlation majorant for arbitrary complex phases; an indicator
  bound is not incorrectly reused as a coefficient estimate for arbitrary complex
  coefficients;
- disjointness of dyadic levels, exact reconstruction, and levelwise energy control
  after normalization by the actual finite `ℓ²` norm;
- summation of the Lorentz geometric series using `m_j ≤ |X|` and
  `m_j ≤ 4^(j+1)`, yielding a strong-type `L² → L⁴` endpoint independent of both
  the coefficient dynamic range and the number of nonempty levels;
- exact identities for finite convolution/correlation and the geometric `(2,2)`
  endpoint;
- barycentric coordinates for
  `theta = max(0, 3 - 2(1/p+1/q))`, the Young endpoints, finite `ℓ^p`
  monotonicity, and the final `rpow` calculation for the constant;
- a separate branch in which empty support makes the expression vanish, avoiding
  an incorrect comparison with the zero-cardinality power when `theta=0` and
  `0^0` occurs;
- `theorem13_internal : AnalysisInputs → Theorem13Statement`.

External analytic boundary: the Fourier/Parseval implementation and bilinear
complex interpolation. The paper-facing statement explicitly includes the
hypotheses `K_X,K_Y ≥ 1` and that the ambient abelian group is torsion-free, and it
expands the inherited constant hidden by `≪_eta`. The alpha-two strong-type endpoint
of Proposition 5.1 is closed internally in `Weighted/RestrictedStrong.lean` and is
no longer an input field.

## Theorem 1.4

Kernel-checked in Lean:

- exact finite definitions of ordered configurations, contiguous signed-convex
  blocks, and the minimum number of blocks;
- the singleton partition and existence and uniqueness of the minimum turning
  complexity;
- for any two admissible complementary coordinates,
  `m'=c m+d ell` with `c≠0`, and hence independence of the upper and exact turning
  complexities from the choice of complementary coordinate;
- construction of a globally strictly convex or concave interpolating function
  from finitely many strictly increasing or decreasing adjacent slopes;
- an explicit solution for the strip interpolation parameter and the associated
  exponent identity;
- finite Jensen/Hölder assembly for nonuniform dyadic levels;
- sixth-power closure from the CDW/strip level certificate and explicit absorption
  of `log N` into any remaining `N^eps`; the uniform external analytic constant `A`
  is correctly propagated as `A^6` in the final constant;
- `J3` counts for intervals and power curves, uniqueness of carry-free sums of
  three powers, and the packet estimate `J3 ≍ K^2 (Kn)^3`; the reset-boundary
  slopes internally force `K ≤ 2·blocks.length`, thereby producing an exact `k`
  with `K/2 ≤ k ≤ K` and closing the full sharpness statement.

External analytic/literature boundary: the Cushman--Demeter--Wu `J3` theorem for
convex graphs and the Hilbert-transform/strip-projection lemma. The upper bound
remains conditional on `TurningDyadicInputs`. This certificate currently packages
a common admissible thickening, genuine Fourier-strip semantics, leafwise
applications of CDW from the already-proved convex interpolant, and the
strip/Minkowski assembly; there is not yet an
`External.Inputs → TurningDyadicInputs` generator. The certificate does not contain
the final `J3` conclusion, and its constant is quantified before `P,K`. Thus the
conditional verifier is noncircular and its constant is uniform, but this does not
justify claiming that the upper bound has been formalized unconditionally.

## Corrections to the Paper

- In Theorem 1.1, the interpolation inequality must first be applied with the
  node-local `lambda ≤ M`, and only then with `lambda ≤ Lambda`; the local quantity
  cannot be replaced by the global `Lambda` prematurely.
- Theorem 1.3 must explicitly assume `K_X,K_Y ≥ 1`. Passing from set indicators to
  arbitrary complex phases requires a correlation majorant; it is not an automatic
  consequence for a general linear operator.
- The definition of `alpha(V)` in Theorem 1.1 divides by the dimension, so the
  paper-facing theorem explicitly assumes positive dimension.
- In Theorem 1.4, the implicit CDW/strip constant must be uniform before
  quantification over `P,K` and must enter the final constant to the sixth power;
  it cannot silently be normalized to 1.
