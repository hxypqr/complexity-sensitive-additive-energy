import Mathlib

/-!
# The interpolation polygon in Theorem 1.3

The analytic interpolation theorem is external.  The conversion from its
barycentric parameters to the paper's closed formula for `theta` is elementary
and is proved here.
-/

namespace ComplexitySensitiveEnergy

/-- The exponent of the joint complexity parameter in Theorem 1.3, written
in reciprocal input coordinates `x = 1/p`, `y = 1/q`. -/
def offDiagonalTheta (x y : ℝ) : ℝ :=
  max 0 (3 - 2 * (x + y))

/-- In the genuine interpolation triangle (`1 ≤ x+y ≤ 3/2`), these are
the unique barycentric coordinates of `(x,y)` relative to
`(1/2,1/2)`, `(1,1/2)`, `(1/2,1)`. -/
theorem alphaTwo_barycentric_coordinates
    {x y : ℝ} (hx : 1 / 2 ≤ x) (hy : 1 / 2 ≤ y)
    (hs : x + y ≤ 3 / 2) :
    let theta₀ := 3 - 2 * (x + y)
    let theta₁ := 2 * x - 1
    let theta₂ := 2 * y - 1
    0 ≤ theta₀ ∧ 0 ≤ theta₁ ∧ 0 ≤ theta₂ ∧
      theta₀ + theta₁ + theta₂ = 1 ∧
      x = theta₀ / 2 + theta₁ + theta₂ / 2 ∧
      y = theta₀ / 2 + theta₁ / 2 + theta₂ := by
  dsimp
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · ring
  constructor <;> ring

theorem offDiagonalTheta_eq_interior
    {x y : ℝ} (hs : x + y ≤ 3 / 2) :
    offDiagonalTheta x y = 3 - 2 * (x + y) := by
  rw [offDiagonalTheta, max_eq_right]
  linarith

/-- Above the interpolation edge, monotonicity of counting norms reaches
`(x,y)` from the displayed boundary point `(3/2-y,y)`. -/
theorem alphaTwo_boundary_point_below
    {x y : ℝ} (hy : 1 / 2 ≤ y)
    (hy1 : y ≤ 1) (hs : 3 / 2 ≤ x + y) :
    let x₀ := 3 / 2 - y
    1 / 2 ≤ x₀ ∧ x₀ ≤ 1 ∧ x₀ ≤ x ∧
      1 / 2 ≤ y ∧ y ≤ 1 ∧ x₀ + y = 3 / 2 := by
  dsimp
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  exact ⟨hy, hy1, by ring⟩

theorem offDiagonalTheta_eq_zero
    {x y : ℝ} (hs : 3 / 2 ≤ x + y) :
    offDiagonalTheta x y = 0 := by
  rw [offDiagonalTheta, max_eq_left]
  linarith

/-- Complete numerical description of the alpha-two region.  Below the
critical edge the geometric endpoint receives weight `theta`; above it the
complexity exponent vanishes and norm monotonicity is used. -/
theorem offDiagonalTheta_piecewise
    {x y : ℝ} :
    offDiagonalTheta x y =
      if x + y ≤ 3 / 2 then 3 - 2 * (x + y) else 0 := by
  by_cases hs : x + y ≤ 3 / 2
  · simp [hs, offDiagonalTheta_eq_interior hs]
  · have hs' : 3 / 2 ≤ x + y := le_of_not_ge hs
    simp [hs, offDiagonalTheta_eq_zero hs']

end ComplexitySensitiveEnergy
