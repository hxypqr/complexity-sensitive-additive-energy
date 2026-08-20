import ComplexitySensitiveEnergy.Additive.Energy
import ComplexitySensitiveEnergy.Algebraic.Variety

/-!
# Exact statement of Theorem 1.1

We use an upper-bound parameter `Lambda` satisfying `PaperVariety.FlagBound`.
This is logically equivalent to inserting the maximum `Λ_{a,R}(X;V)` and is
far more robust than an infinite natural-number supremum.  Positive complex
dimension is explicit because `alpha(V)` contains division by that dimension.
-/

namespace ComplexitySensitiveEnergy

/-- Constant-explicit upper-bound formulation of Theorem 1.1. -/
def Theorem11Statement : Prop :=
  ∀ (n Delta : ℕ) (a eps : ℝ),
    1 ≤ n → 1 ≤ Delta → 2 ≤ a → a < 3 → 0 < eps →
    ∃ R : ℕ, Delta ≤ R ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (V : PaperVariety n), V.admissibleIrreducible →
        0 < V.complexDim → V.degree ≤ Delta → V.alpha ≤ a →
        ∀ (X : Finset (RVec n)), ↑X ⊆ V.realPoints →
          ∀ Lambda : ℕ, V.FlagBound a R X Lambda →
            (energy X : ℝ) ≤
              C * (Lambda : ℝ) ^ (3 - a) *
                (X.card : ℝ) ^ (a + eps)

end ComplexitySensitiveEnergy
