import Mathlib
import ComplexitySensitiveEnergy.Additive.Energy
import ComplexitySensitiveEnergy.Additive.HigherEnergy

/-!
# Exact statements of the two additive-energy inputs from the literature

This file is a trust-boundary record, not a list of global axioms.  The two
results are fields of a proposition-valued structure which a user may supply.
In particular, importing this file proves neither result.

The formulation of Jing--Wu uses an upper bound `L` for the maximum line
occupancy.  This is equivalent to their `max {1, ...}` formulation and avoids
pretending that an infinite supremum of natural numbers is definitionally a
maximum.  The Cushman--Demeter--Wu constant is quantified *before* the convex
function, recording the uniformity in that function.
-/

open scoped BigOperators Pointwise

namespace ComplexitySensitiveEnergy.External

abbrev R3 := Fin 3 → ℝ

/-- The real zero set of a three-variable polynomial. -/
def realZeroSet (F : MvPolynomial (Fin 3) ℝ) : Set R3 :=
  {x | MvPolynomial.eval x F = 0}

/-- A genuine affine line: the direction is required to be nonzero. -/
structure AffineLine3 where
  base : R3
  direction : R3
  direction_ne_zero : direction ≠ 0

namespace AffineLine3

/-- Point-set carrier of an affine line. -/
def carrier (L : AffineLine3) : Set R3 :=
  {x | ∃ s : ℝ, x = L.base + s • L.direction}

end AffineLine3

/-- `L` bounds one and every affine-line occupancy occurring in Jing--Wu's
parameter `Λ_F(X)`. -/
def LineOccupancyBound (F : MvPolynomial (Fin 3) ℝ)
    (X : Finset R3) (L : ℕ) : Prop := by
  classical
  exact 1 ≤ L ∧ ∀ ℓ : AffineLine3, ℓ.carrier ⊆ realZeroSet F →
    (X.filter fun x => x ∈ ℓ.carrier).card ≤ L

/-- Exact upper-bound form of Jing--Wu, Theorem 1.1 (arXiv:2608.14467v1).

`F` is real-irreducible, has degree exactly `d ≥ 2`, and `X` lies on its
real zero set.  The constant depends only on `d` and `eps`, not on `F`, `X`,
or the chosen upper bound `L`. -/
def JingWuStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : MvPolynomial (Fin 3) ℝ), Irreducible F →
        F.totalDegree = (d : WithBot ℕ) →
        ∀ (X : Finset R3), ↑X ⊆ realZeroSet F →
          ∀ L : ℕ, LineOccupancyBound F X L →
            (energy X : ℝ) ≤
              C * (L : ℝ) * (X.card : ℝ) ^ (2 + eps)

/-- Graph of a real function over a finite set, embedded in `ℝ²`. -/
noncomputable def finiteGraph (f : ℝ → ℝ) (X : Finset ℝ) :
    Finset (Fin 2 → ℝ) := by
  classical
  exact X.image fun x i => if i = 0 then x else f x

/-- Exact upper-bound form of Cushman--Demeter--Wu, Theorem 1.1
(arXiv:2608.12316v2).  `C` is uniform over all Jensen-strictly-convex
functions `f`. -/
def CushmanDemeterWuStatement : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f : ℝ → ℝ), StrictConvexOn ℝ Set.univ f →
      ∀ X : Finset ℝ,
        (J3 (finiteGraph f X) : ℝ) ≤
          C * (X.card : ℝ) ^ (3 + eps)

/-- The literature inputs used by the paper, kept explicit and inert. -/
structure LiteratureInputs : Prop where
  jingWu : JingWuStatement
  cushmanDemeterWu : CushmanDemeterWuStatement

end ComplexitySensitiveEnergy.External
