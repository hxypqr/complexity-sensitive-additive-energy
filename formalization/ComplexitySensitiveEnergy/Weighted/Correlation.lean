import Mathlib
import ComplexitySensitiveEnergy.Additive.Energy

/-!
# Complex phases and weighted difference correlations

An indicator estimate does not, for a general linear operator, imply the
complex-coefficient restricted estimate used in Proposition 5.1.  For the
Fourier correlation in this paper there is an additional pointwise
majorization.  This file proves it directly on finite sums and derives the
bounded-coefficient weighted-energy estimate.  These are internal lemmas,
not external analysis inputs.
-/

open scoped BigOperators

namespace ComplexitySensitiveEnergy

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Weighted difference correlation
`R_f(t) = ∑_{x-y=t} f(x) conjugate(f(y))`. -/
def weightedDifferenceCorrelation (A : Finset G) (f : G → ℂ) (t : G) : ℂ :=
  ∑ ab ∈ (A ×ˢ A).filter (fun ab => ab.1 - ab.2 = t),
    f ab.1 * star (f ab.2)

/-- The positive correlation obtained by discarding all phases. -/
noncomputable def absoluteDifferenceCorrelation
    (A : Finset G) (f : G → ℂ) (t : G) : ℝ :=
  ∑ ab ∈ (A ×ˢ A).filter (fun ab => ab.1 - ab.2 = t),
    ‖f ab.1‖ * ‖f ab.2‖

/-- The missing phase step in the manuscript: cancellation can only reduce
the norm of a finite correlation. -/
theorem norm_weightedDifferenceCorrelation_le_absolute
    (A : Finset G) (f : G → ℂ) (t : G) :
    ‖weightedDifferenceCorrelation A f t‖ ≤
      absoluteDifferenceCorrelation A f t := by
  unfold weightedDifferenceCorrelation absoluteDifferenceCorrelation
  calc
    ‖∑ ab ∈ (A ×ˢ A).filter (fun ab => ab.1 - ab.2 = t),
        f ab.1 * star (f ab.2)‖ ≤
        ∑ ab ∈ (A ×ˢ A).filter (fun ab => ab.1 - ab.2 = t),
          ‖f ab.1 * star (f ab.2)‖ := norm_sum_le _ _
    _ = ∑ ab ∈ (A ×ˢ A).filter (fun ab => ab.1 - ab.2 = t),
          ‖f ab.1‖ * ‖f ab.2‖ := by
      apply Finset.sum_congr rfl
      intro ab hab
      simp

/-- If all coefficients on `A` have size at most `c`, then each correlation
is bounded by `c²` times the indicator representation count. -/
theorem norm_weightedDifferenceCorrelation_le_representation
    (A : Finset G) (f : G → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hf : ∀ x ∈ A, ‖f x‖ ≤ c) (t : G) :
    ‖weightedDifferenceCorrelation A f t‖ ≤
      c ^ 2 * (differenceRepresentation A A t : ℝ) := by
  refine (norm_weightedDifferenceCorrelation_le_absolute A f t).trans ?_
  unfold absoluteDifferenceCorrelation differenceRepresentation
  calc
    (∑ ab ∈ (A ×ˢ A).filter (fun ab => ab.1 - ab.2 = t),
        ‖f ab.1‖ * ‖f ab.2‖) ≤
        ∑ _ab ∈ (A ×ˢ A).filter (fun ab => ab.1 - ab.2 = t),
          c ^ 2 := by
      apply Finset.sum_le_sum
      intro ab hab
      have habA := (Finset.mem_filter.mp hab).1
      have ha := (Finset.mem_product.mp habA).1
      have hb := (Finset.mem_product.mp habA).2
      simpa [pow_two] using
        (mul_le_mul (hf ab.1 ha) (hf ab.2 hb) (norm_nonneg _) hc)
    _ = c ^ 2 *
        (((A ×ˢ A).filter (fun ab => ab.1 - ab.2 = t)).card : ℝ) := by
      simp [mul_comm]

/-- Squared-correlation sum over its actual finite support. -/
noncomputable def weightedCorrelationSquareSum
    (A : Finset G) (f : G → ℂ) : ℝ :=
  ∑ t ∈ differenceSet A A, ‖weightedDifferenceCorrelation A f t‖ ^ 2

/-- Bounded complex coefficients have weighted energy at most `c⁴ E(A)`.
This is the hereditary restricted estimate needed before any Lorentz/dyadic
extension; phases have been handled, rather than silently ignored. -/
theorem weightedCorrelationSquareSum_le
    (A : Finset G) (f : G → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hf : ∀ x ∈ A, ‖f x‖ ≤ c) :
    weightedCorrelationSquareSum A f ≤ c ^ 4 * (energy A : ℝ) := by
  unfold weightedCorrelationSquareSum
  calc
    (∑ t ∈ differenceSet A A,
        ‖weightedDifferenceCorrelation A f t‖ ^ 2) ≤
        ∑ t ∈ differenceSet A A,
          c ^ 4 * (differenceRepresentation A A t : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      have h := norm_weightedDifferenceCorrelation_le_representation
        A f c hc hf t
      have hn : 0 ≤ ‖weightedDifferenceCorrelation A f t‖ := norm_nonneg _
      have hr : 0 ≤ (differenceRepresentation A A t : ℝ) := by positivity
      nlinarith [sq_nonneg (c ^ 2 *
        (differenceRepresentation A A t : ℝ) -
          ‖weightedDifferenceCorrelation A f t‖)]
    _ = c ^ 4 * (energy A : ℝ) := by
      simp only [energy, differenceEnergy, Nat.cast_sum, Nat.cast_pow]
      rw [Finset.mul_sum]

end ComplexitySensitiveEnergy
