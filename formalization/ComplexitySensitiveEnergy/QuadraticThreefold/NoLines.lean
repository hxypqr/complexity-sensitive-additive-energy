import ComplexitySensitiveEnergy.QuadraticThreefold.Definitions

/-!
# The positive-definite quadratic graph has no affine lines

The full Bezout intersection bound is external algebraic geometry.  The
new internal observation needed by Theorem 1.2 is that a nonconstant affine
parameter line cannot lie in the graph.  It already follows from the first
positive-definite quadratic coordinate; Lean checks the midpoint identity.
-/

open scoped BigOperators Matrix

namespace ComplexitySensitiveEnergy.QuadraticThreefold

theorem quadraticForm_add_sub_midpoint
    (A : Matrix (Fin 3) (Fin 3) ℝ) (u v : R3) :
  quadraticForm A (u + v) + quadraticForm A (u - v) =
      2 * quadraticForm A u + 2 * quadraticForm A v := by
  simp only [quadraticForm, Matrix.mulVec_add, Matrix.mulVec_sub,
    add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub]
  ring

/-- Three equally spaced parameter points cannot map to three equally spaced
graph points unless the parameter displacement is zero.  Consequently the
quadratic graph contains no nontrivial affine line. -/
theorem graphMap_no_nontrivial_midpoint
    (Q : SimplePencil) (u v : R3) (hv : v ≠ 0) :
    graphMap Q (u + v) + graphMap Q (u - v) ≠
      (2 : ℝ) • graphMap Q u := by
  intro hline
  have hcoord := congrFun hline (⟨3, by omega⟩ : Fin 5)
  have hq : quadraticForm Q.A₁ (u + v) + quadraticForm Q.A₁ (u - v) =
      2 * quadraticForm Q.A₁ u := by
    simpa [graphMap] using hcoord
  have hexpand := quadraticForm_add_sub_midpoint Q.A₁ u v
  have hpos := Q.positive₁ v hv
  linarith

end ComplexitySensitiveEnergy.QuadraticThreefold
