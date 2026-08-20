import Mathlib
import ComplexitySensitiveEnergy.Additive.Energy
import ComplexitySensitiveEnergy.Algebraic.Variety

/-!
# The quadratic threefold in Theorem 1.2

The simple generalized spectrum is expressed without choosing a matrix square
root: a positive-definite symmetric first form and a basis of generalized
eigenvectors with pairwise distinct real eigenvalues.  For a symmetric pencil
this is equivalent to the formulation in the paper.
-/

open scoped BigOperators Matrix

namespace ComplexitySensitiveEnergy.QuadraticThreefold

abbrev R3 := RVec 3
abbrev R5 := RVec 5

/-- Quadratic form represented by a real `3 × 3` matrix. -/
def quadraticForm (A : Matrix (Fin 3) (Fin 3) ℝ) (u : R3) : ℝ :=
  dotProduct u (A.mulVec u)

/-- Literal positive definiteness. -/
def IsPositiveDefinite (A : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ u : R3, u ≠ 0 → 0 < quadraticForm A u

/-- A symmetric quadratic pencil with simple generalized spectrum. -/
structure SimplePencil where
  A₁ : Matrix (Fin 3) (Fin 3) ℝ
  A₂ : Matrix (Fin 3) (Fin 3) ℝ
  symmetric₁ : A₁.IsSymm
  symmetric₂ : A₂.IsSymm
  positive₁ : IsPositiveDefinite A₁
  eigenvalue : Fin 3 → ℝ
  eigenvector : Fin 3 → R3
  eigenvectors_independent : LinearIndependent ℝ eigenvector
  eigenvalues_distinct : Function.Injective eigenvalue
  generalized_eigenvector : ∀ i,
    A₂.mulVec (eigenvector i) =
      eigenvalue i • A₁.mulVec (eigenvector i)

/-- The graph parametrization `u ↦ (u,Q₁(u),Q₂(u))`. -/
def graphMap (Q : SimplePencil) (u : R3) : R5 := fun i =>
  if h : i.val < 3 then u ⟨i.val, h⟩
  else if i.val = 3 then quadraticForm Q.A₁ u else quadraticForm Q.A₂ u

/-- Point-set carrier of the quadratic threefold. -/
def graphCarrier (Q : SimplePencil) : Set R5 := Set.range (graphMap Q)

/-- Exact upper-bound clause of Theorem 1.2. -/
def QuadraticThreefoldEnergyStatement : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Q : SimplePencil) (X : Finset R5), ↑X ⊆ graphCarrier Q →
      (energy X : ℝ) ≤ C * (X.card : ℝ) ^ (2 + eps)

/-- The paper's Theorem 1.2, with its sharpness sentence expanded as the
universal diagonal lower bound. -/
def Theorem12Statement : Prop :=
  QuadraticThreefoldEnergyStatement ∧
    ∀ (X : Finset R5), 2 * X.card ^ 2 - X.card ≤ energy X

end ComplexitySensitiveEnergy.QuadraticThreefold
