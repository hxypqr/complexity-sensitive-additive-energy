import ComplexitySensitiveEnergy.QuadraticThreefold.Definitions
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank classification of quadratic-threefold difference fibers

After changing to a generalized eigenbasis and dividing the first positive
quadratic form by its diagonal coefficients, the two linear equations in a
difference fiber have coefficient rows

`d` and `(lambda i * d i)_i`.

This file proves the internal linear-algebra assertion used in the paper:
when the generalized eigenvalues are distinct, rank below two forces the
displacement `d` to have at most one nonzero coordinate.  Thus every nonzero
rank-drop displacement lies on one of the three eigendirections.
All ranks below are matrix ranks over `ℝ`.
-/

open scoped Matrix

namespace ComplexitySensitiveEnergy.QuadraticThreefold

noncomputable section

/-- The normalized `2 × 3` coefficient matrix of a difference fiber in a
generalized eigenbasis.  The harmless common factors `2` have been removed. -/
def canonicalFiberCoefficient
    (lambda d : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  fun r i => if r = 0 then d i else lambda i * d i

@[simp] theorem canonicalFiberCoefficient_row_zero
    (lambda d : Fin 3 → ℝ) (i : Fin 3) :
    canonicalFiberCoefficient lambda d 0 i = d i := by
  simp [canonicalFiberCoefficient]

@[simp] theorem canonicalFiberCoefficient_row_one
    (lambda d : Fin 3 → ℝ) (i : Fin 3) :
    canonicalFiberCoefficient lambda d 1 i = lambda i * d i := by
  simp [canonicalFiberCoefficient]

/-- Two nonzero displacement coordinates with different eigenvalues produce
an invertible `2 × 2` minor, hence force matrix rank two. -/
theorem two_le_rank_canonicalFiberCoefficient_of_two_nonzero
    {lambda d : Fin 3 → ℝ} {i j : Fin 3}
    (hdi : d i ≠ 0) (hdj : d j ≠ 0)
    (hlambda : lambda i ≠ lambda j) :
    2 ≤ (canonicalFiberCoefficient lambda d).rank := by
  let columns : Fin 2 → Fin 3 := ![i, j]
  let minor : Matrix (Fin 2) (Fin 2) ℝ :=
    (canonicalFiberCoefficient lambda d).submatrix id columns
  have hdetFormula : minor.det = d i * d j * (lambda j - lambda i) := by
    dsimp only [minor, columns]
    rw [Matrix.det_fin_two]
    simp [canonicalFiberCoefficient]
    ring
  have hdet : minor.det ≠ 0 := by
    rw [hdetFormula]
    exact mul_ne_zero (mul_ne_zero hdi hdj) (sub_ne_zero.mpr hlambda.symm)
  have hminorUnit : IsUnit minor := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdet
  have hminorRank : minor.rank = 2 := by
    rw [Matrix.rank_of_isUnit minor hminorUnit]
    norm_num
  have hsubmatrix : minor.rank ≤
      (canonicalFiberCoefficient lambda d).rank := by
    exact Matrix.rank_submatrix_le
      (canonicalFiberCoefficient lambda d) id columns
  simpa only [hminorRank] using hsubmatrix

/-- Rank below two implies that the support of the displacement is a
subsingleton. -/
theorem canonicalFiberCoefficient_rank_lt_two_support_subsingleton
    {lambda d : Fin 3 → ℝ} (hlambda : Function.Injective lambda)
    (hrank : (canonicalFiberCoefficient lambda d).rank < 2) :
    ∀ i j : Fin 3, d i ≠ 0 → d j ≠ 0 → i = j := by
  intro i j hdi hdj
  by_contra hij
  have hrankTwo := two_le_rank_canonicalFiberCoefficient_of_two_nonzero
    hdi hdj (hlambda.ne hij)
  omega

/-- Geometric form of the classification: a rank-drop displacement is zero
or is supported on exactly one of the three generalized eigendirections. -/
theorem canonicalFiberCoefficient_rank_lt_two_direction
    {lambda d : Fin 3 → ℝ} (hlambda : Function.Injective lambda)
    (hrank : (canonicalFiberCoefficient lambda d).rank < 2) :
    d = 0 ∨ ∃ i : Fin 3, d i ≠ 0 ∧ ∀ j : Fin 3, j ≠ i → d j = 0 := by
  classical
  by_cases hd : d = 0
  · exact Or.inl hd
  · right
    have hexists : ∃ i : Fin 3, d i ≠ 0 := by
      by_contra h
      push Not at h
      exact hd (funext h)
    obtain ⟨i, hi⟩ := hexists
    refine ⟨i, hi, ?_⟩
    intro j hji
    by_contra hj
    exact hji (canonicalFiberCoefficient_rank_lt_two_support_subsingleton
      hlambda hrank j i hj hi)

/-- Direct simple-pencil specialization: the `SimplePencil` spectrum field
discharges the only spectral hypothesis in the normalized classification. -/
theorem SimplePencil.canonicalFiber_rank_lt_two_direction
    (Q : SimplePencil) {d : Fin 3 → ℝ}
    (hrank : (canonicalFiberCoefficient Q.eigenvalue d).rank < 2) :
    d = 0 ∨ ∃ i : Fin 3, d i ≠ 0 ∧ ∀ j : Fin 3, j ≠ i → d j = 0 :=
  canonicalFiberCoefficient_rank_lt_two_direction
    Q.eigenvalues_distinct hrank

end

end ComplexitySensitiveEnergy.QuadraticThreefold
