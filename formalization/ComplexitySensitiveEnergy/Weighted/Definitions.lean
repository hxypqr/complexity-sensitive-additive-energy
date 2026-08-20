import ComplexitySensitiveEnergy.External.Analysis
import ComplexitySensitiveEnergy.Weighted.DyadicExtension
import ComplexitySensitiveEnergy.Weighted.OffDiagonalParameters

/-!
# Explicit statement of Theorem 1.3

The manuscript's `≪_η` hides a constant for each hereditary energy
estimate.  Lean cannot leave that dependence implicit, so `C_X,C_Y` appear
below and receive the same interpolated power as `K_X,K_Y`.  We also include
the necessary hypotheses `K_X,K_Y ≥ 1`, which are used later in the paper.
-/

namespace ComplexitySensitiveEnergy

open External

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- One explicit hereditary quadratic energy estimate. -/
def HereditaryQuadraticEnergy (X : Finset G)
    (K C eta : ℝ) : Prop :=
  1 ≤ K ∧ 1 ≤ C ∧ 0 < eta ∧
    ∀ A : Finset G, A ⊆ X →
      (energy A : ℝ) ≤ C * K * (A.card : ℝ) ^ (2 + eta)

/-- Fully quantified, constant-explicit version of Theorem 1.3.

The outer constant is uniform in the group, supports, complexity parameters,
and hereditary constants.  The theorem's `theta` is exactly the closed formula
in the paper. -/
def Theorem13Statement : Prop :=
  ∀ (p q eps : ℝ), 1 ≤ p → p ≤ 2 →
    1 ≤ q → q ≤ 2 → 1 ≤ 1 / p + 1 / q →
    0 < eps →
    ∃ eta : ℝ, 0 < eta ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : Type) (_ : AddCommGroup G) (_ : IsAddTorsionFree G)
        (_ : DecidableEq G)
        (X Y : Finset G) (KX KY CX CY : ℝ),
        HereditaryQuadraticEnergy X KX CX eta →
        HereditaryQuadraticEnergy Y KY CY eta →
        ConvolutionBound X Y p q
          (C * ((CX * CY) * (KX * KY)) ^
              (offDiagonalTheta (1 / p) (1 / q) / 4) *
            ((X.card : ℝ) * (Y.card : ℝ)) ^ eps)

end ComplexitySensitiveEnergy
