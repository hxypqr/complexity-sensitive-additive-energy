# External theorem and proof audit

Source paper: arXiv:2608.18956v1.

## Substantive internal corrections

1. **Theorem 1.1, local versus global concentration.**  In displayed
   (3.14)--(3.17) the manuscript substitutes the global flag parameter
   `Lambda` before applying `lambda M^2 <= lambda^(3-a) M^a`.  That inequality
   needs `lambda <= M`; a global `Lambda` can be much larger than the node size
   `M`.  The formal proof retains `lambda_W(A)` and uses

   ```text
   lambda M^2 <= lambda^(3-a) M^a <= Lambda^(3-a) M^a.
   ```

   The conclusion is unchanged.

2. **Theorem 1.3, complex coefficients.**  An indicator estimate for a generic
   linear operator does not imply arbitrary complex restricted type.  The
   Fourier correlation here has the special pointwise majorant
   `|R_f(t)| <= R_|f|(t)`.  `Weighted/Correlation.lean` proves this on the
   actual finite sums.  `Weighted/RestrictedStrong.lean` then normalizes by
   the real finite `ell^2` norm and performs a geometric Lorentz sum whose
   constant is independent of coefficient dynamic range.

3. **Missing hypotheses in the displayed statements.**  The Lean statement
   adds positive dimension in Theorem 1.1 (otherwise `alpha` divides by zero)
   and `K_X,K_Y >= 1` in Theorem 1.3 (used explicitly in Proposition 5.1 and
   Theorem 5.3).  It also retains the paper's standing torsion-free hypothesis
   on the ambient abelian group.  The constants hidden by `<<_eta` are
   explicit parameters.

4. **Complementary coordinate in Theorem 1.4.**  The transverse functional
   is not arbitrary: together with the ordering functional it must form an
   injective coordinate map on `ℝ²`.  `OrderedConfiguration` stores this
   condition explicitly; otherwise a degenerate choice such as a multiple of
   the ordering functional could change the strict slope-block complexity.
   The formal proof now also derives `m' = c m + d ell`, `c != 0`, from any
   two valid complements, rather than assuming that relation.

5. **Uniform strip/CDW constant.**  The analytic constant is quantified
   before the point configuration and block bound.  It propagates as `A^6`
   after the sixth-power argument; silently setting it to one would give an
   incorrect final constant.

## Literature statements

- **Jing--Wu.**  The source theorem is for a real-irreducible polynomial
  `F : R^3 -> R` of degree at least two and gives
  `E(X) <= C_(deg F,eps) Lambda_F(X) |X|^(2+eps)`, with `Lambda_F` the maximum
  affine-line occupancy on lines contained in `Z(F)`.  This is recorded in
  `External/Literature.lean` using the equivalent upper-bound predicate
  `LineOccupancyBound`.  Source: <https://arxiv.org/abs/2608.14467>.

- **Cushman--Demeter--Wu.**  Version 2 quantifies the constant uniformly over
  every Jensen-strictly-convex `f : R -> R` and every finite `X`; the result is
  `J3(graph(f|X)) <= C_eps |X|^(3+eps)`.  The constant is therefore quantified
  before `f` in Lean.  Source: <https://arxiv.org/abs/2608.12316>.

- **Walsh polynomial partitioning.**  Walsh's original parameter gives a
  partition polynomial of degree `O_n(D)`, not literally `<= D`.
  `External/AlgebraicGeometry.lean` retains a degree multiplier in
  `WalshPartitionStatement`; the paper's form follows by reparameterization
  together with the component count.  Source:
  <https://arxiv.org/abs/1811.07865>.

- **Barone--Basu.**  The source controls connected components of realizable
  sign conditions in terms of the degrees of defining equations.  The paper's
  degree-`B` algebraic-set formulation also uses the standard bounded-degree
  to bounded-defining-complexity reduction.  Lean records that extra premise
  explicitly.  Source: <https://arxiv.org/abs/1104.0636>.

- **Generic surface projection (paper Lemma 4.3).**  Theorem 1.2 uses a
  generic projection of a line-free irreducible surface.  The manuscript gives
  no specific citation, so Lean isolates its `R^5` specialization as
  `GenericSurfaceProjectionStatement`.  It now records every property used in
  the manuscript: a complex-linear extension, the complex Zariski image
  closure, finite Freiman order two, preservation of noncollinear triples,
  irreducible nonplanar degree control, an irreducible defining polynomial,
  and the explicit line-occupancy bound `<= B` required by Jing--Wu.

## Trust boundary

`External/*.lean` contains proposition-valued structures and definitions,
not `axiom` declarations.  Supplying an external package is therefore visible
at the use site.  `External.Inputs` is a registry of source-faithful external
statements; it does **not** currently prove the bridge to
`FlaggedRecurrenceInputs`, `GranularThreefoldRecurrenceInputs`, or
`TurningDyadicInputs`.  Consequently those paper-facing upper bounds remain
kernel-checked conditional implications.  The finite combinatorial verifiers
do not depend on the truth of the historical literature bundle.
