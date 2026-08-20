import Mathlib

/-!
# The Gram-matrix kernel for the rank-drop term

This file isolates the elementary finite calculation used for the three
characteristic directions of a quadratic threefold.  A matrix `M : R → Z → ℕ`
is regarded as an incidence matrix (the intended entries are zero or one).
Its row Gram matrix is

`gram M r s = ∑ z, M r z * M s z`.

The proof below is deliberately entrywise.  Cauchy--Schwarz bounds every
off-diagonal Gram entry, summing the resulting product of diagonal entries
gives a square of the trace, and a zero-one hypothesis identifies that trace
with the number of incidences.  No spectral theorem is used.

The final definitions add one zero-difference contribution and three
off-diagonal direction contributions.  Thus the zero difference is present
exactly once.  The calculation actually gives the sharper coefficient `4`;
the coefficient `7` used in the paper follows immediately.
-/

namespace ComplexitySensitiveEnergy
namespace QuadraticThreefold

open scoped BigOperators

section OneMatrix

variable {R Z : Type*}

/-- The row Gram matrix of a finite, natural-valued incidence matrix. -/
def gram [Fintype Z] (M : R → Z → ℕ) (r s : R) : ℕ :=
  ∑ z, M r z * M s z

/-- The trace of the row Gram matrix. -/
def gramTrace [Fintype R] [Fintype Z] (M : R → Z → ℕ) : ℕ :=
  ∑ r, gram M r r

/-- The sum of the squares of all entries of the row Gram matrix. -/
def fullGramSquareSum [Fintype R] [Fintype Z] (M : R → Z → ℕ) : ℕ :=
  ∑ r, ∑ s, gram M r s ^ 2

/-- The sum of squares of the off-diagonal entries of the row Gram matrix. -/
def offDiagonalGramSquareSum [Fintype R] [Fintype Z] [DecidableEq R]
    (M : R → Z → ℕ) : ℕ :=
  ∑ r, ∑ s, if r = s then 0 else gram M r s ^ 2

/-- The total mass of a finite incidence matrix. -/
def incidenceMass [Fintype R] [Fintype Z] (M : R → Z → ℕ) : ℕ :=
  ∑ r, ∑ z, M r z

/-- The intended incidence-matrix condition. -/
def IsZeroOne (M : R → Z → ℕ) : Prop :=
  ∀ r z, M r z = 0 ∨ M r z = 1

/-- Entrywise Cauchy--Schwarz for the row Gram matrix. -/
theorem gram_entry_sq_le_diag_mul_diag [Fintype Z]
    (M : R → Z → ℕ) (r s : R) :
    gram M r s ^ 2 ≤ gram M r r * gram M s s := by
  simpa [gram, pow_two] using
    (Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ) (Finset.univ : Finset Z) (M r) (M s))

/-- Summing the entrywise Cauchy--Schwarz inequalities gives
`∑ r,s, G r s ^ 2 ≤ (trace G) ^ 2`. -/
theorem fullGramSquareSum_le_trace_sq [Fintype R] [Fintype Z]
    (M : R → Z → ℕ) :
    fullGramSquareSum M ≤ gramTrace M ^ 2 := by
  calc
    fullGramSquareSum M
        ≤ ∑ r, ∑ s, gram M r r * gram M s s := by
          apply Finset.sum_le_sum
          intro r _
          apply Finset.sum_le_sum
          intro s _
          exact gram_entry_sq_le_diag_mul_diag M r s
    _ = (∑ r, gram M r r) * ∑ s, gram M s s := by
          symm
          exact Fintype.sum_mul_sum (fun r ↦ gram M r r) (fun s ↦ gram M s s)
    _ = gramTrace M ^ 2 := by
          simp [gramTrace, pow_two]

/-- Dropping the diagonal terms can only decrease the Gram square sum. -/
theorem offDiagonalGramSquareSum_le_full [Fintype R] [Fintype Z]
    [DecidableEq R] (M : R → Z → ℕ) :
    offDiagonalGramSquareSum M ≤ fullGramSquareSum M := by
  apply Finset.sum_le_sum
  intro r _
  apply Finset.sum_le_sum
  intro s _
  by_cases hrs : r = s <;> simp [hrs]

/-- The off-diagonal square sum is bounded by the square of the Gram trace. -/
theorem offDiagonalGramSquareSum_le_trace_sq [Fintype R] [Fintype Z]
    [DecidableEq R] (M : R → Z → ℕ) :
    offDiagonalGramSquareSum M ≤ gramTrace M ^ 2 :=
  (offDiagonalGramSquareSum_le_full M).trans (fullGramSquareSum_le_trace_sq M)

/-- For a zero-one matrix, the trace is exactly the total incidence mass. -/
theorem gramTrace_eq_incidenceMass [Fintype R] [Fintype Z]
    (M : R → Z → ℕ) (hM : IsZeroOne M) :
    gramTrace M = incidenceMass M := by
  classical
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro z _
  rcases hM r z with hrz | hrz <;> simp [hrz]

/-- The paper's off-diagonal estimate, expressed directly in terms of the
number of zero-one incidences. -/
theorem offDiagonalGramSquareSum_le_incidenceMass_sq [Fintype R] [Fintype Z]
    [DecidableEq R] (M : R → Z → ℕ) (hM : IsZeroOne M) :
    offDiagonalGramSquareSum M ≤ incidenceMass M ^ 2 := by
  simpa [gramTrace_eq_incidenceMass M hM] using
    (offDiagonalGramSquareSum_le_trace_sq M)

end OneMatrix

section FinsetIncidence

variable {R Z : Type*} [DecidableEq R] [DecidableEq Z]

/-- The zero-one incidence matrix attached to a finite set of row-column pairs.

For the quadratic-threefold application, `R` is one selected coordinate and
`Z` is the pair of remaining coordinates. -/
def finsetIncidence (A : Finset (R × Z)) (r : R) (z : Z) : ℕ :=
  if (r, z) ∈ A then 1 else 0

theorem finsetIncidence_isZeroOne (A : Finset (R × Z)) :
    IsZeroOne (finsetIncidence A) := by
  intro r z
  by_cases h : (r, z) ∈ A <;> simp [finsetIncidence, h]

variable [Fintype R] [Fintype Z]

/-- The mass of the incidence matrix of `A` is its cardinality. -/
theorem incidenceMass_finsetIncidence (A : Finset (R × Z)) :
    incidenceMass (finsetIncidence A) = A.card := by
  classical
  rw [incidenceMass, ← Fintype.sum_prod_type']
  simp [finsetIncidence]

/-- Consequently the Gram trace of a finite set is its cardinality. -/
theorem gramTrace_finsetIncidence (A : Finset (R × Z)) :
    gramTrace (finsetIncidence A) = A.card := by
  rw [gramTrace_eq_incidenceMass (finsetIncidence A) (finsetIncidence_isZeroOne A)]
  exact incidenceMass_finsetIncidence A

/-- Ready-to-use off-diagonal Gram estimate for a finite point set. -/
theorem offDiagonalGramSquareSum_finsetIncidence_le_card_sq
    (A : Finset (R × Z)) :
    offDiagonalGramSquareSum (finsetIncidence A) ≤ A.card ^ 2 := by
  simpa [gramTrace_finsetIncidence A] using
    (offDiagonalGramSquareSum_le_trace_sq (finsetIncidence A))

end FinsetIncidence

section ThreeDirections

variable {R1 Z1 R2 Z2 R3 Z3 : Type*}
variable [Fintype R1] [Fintype Z1] [DecidableEq R1]
variable [Fintype R2] [Fintype Z2] [DecidableEq R2]
variable [Fintype R3] [Fintype Z3] [DecidableEq R3]

/-- One zero-difference term together with the three characteristic-direction
off-diagonal Gram terms.  The zero term occurs exactly once in this definition. -/
def rankDropGramMajorant (zeroContribution : ℕ)
    (M1 : R1 → Z1 → ℕ) (M2 : R2 → Z2 → ℕ) (M3 : R3 → Z3 → ℕ) : ℕ :=
  zeroContribution + offDiagonalGramSquareSum M1 +
    offDiagonalGramSquareSum M2 + offDiagonalGramSquareSum M3

/-- The internal calculation actually proves coefficient `4`: one unit for the
zero difference and one for each of the three characteristic directions. -/
theorem rankDropGramMajorant_le_four
    (N zeroContribution : ℕ)
    (M1 : R1 → Z1 → ℕ) (M2 : R2 → Z2 → ℕ) (M3 : R3 → Z3 → ℕ)
    (hzero : zeroContribution ≤ N ^ 2)
    (htrace1 : gramTrace M1 ≤ N)
    (htrace2 : gramTrace M2 ≤ N)
    (htrace3 : gramTrace M3 ≤ N) :
    rankDropGramMajorant zeroContribution M1 M2 M3 ≤ 4 * N ^ 2 := by
  have h1 : offDiagonalGramSquareSum M1 ≤ N ^ 2 :=
    (offDiagonalGramSquareSum_le_trace_sq M1).trans
      (Nat.pow_le_pow_left htrace1 2)
  have h2 : offDiagonalGramSquareSum M2 ≤ N ^ 2 :=
    (offDiagonalGramSquareSum_le_trace_sq M2).trans
      (Nat.pow_le_pow_left htrace2 2)
  have h3 : offDiagonalGramSquareSum M3 ≤ N ^ 2 :=
    (offDiagonalGramSquareSum_le_trace_sq M3).trans
      (Nat.pow_le_pow_left htrace3 2)
  unfold rankDropGramMajorant
  omega

/-- The paper's deliberately loose numerical constant `7`. -/
theorem rankDropGramMajorant_le_seven
    (N zeroContribution : ℕ)
    (M1 : R1 → Z1 → ℕ) (M2 : R2 → Z2 → ℕ) (M3 : R3 → Z3 → ℕ)
    (hzero : zeroContribution ≤ N ^ 2)
    (htrace1 : gramTrace M1 ≤ N)
    (htrace2 : gramTrace M2 ≤ N)
    (htrace3 : gramTrace M3 ≤ N) :
    rankDropGramMajorant zeroContribution M1 M2 M3 ≤ 7 * N ^ 2 := by
  have h4 := rankDropGramMajorant_le_four N zeroContribution M1 M2 M3
    hzero htrace1 htrace2 htrace3
  omega

/-- A convenient specialization in which the single zero-difference term is
itself bounded by `N²` and the three direction terms are only known to be
bounded by their corresponding Gram sums. -/
theorem rankDrop_contributions_le_seven
    (N zeroContribution direction1 direction2 direction3 : ℕ)
    (M1 : R1 → Z1 → ℕ) (M2 : R2 → Z2 → ℕ) (M3 : R3 → Z3 → ℕ)
    (hzero : zeroContribution ≤ N ^ 2)
    (hdir1 : direction1 ≤ offDiagonalGramSquareSum M1)
    (hdir2 : direction2 ≤ offDiagonalGramSquareSum M2)
    (hdir3 : direction3 ≤ offDiagonalGramSquareSum M3)
    (htrace1 : gramTrace M1 ≤ N)
    (htrace2 : gramTrace M2 ≤ N)
    (htrace3 : gramTrace M3 ≤ N) :
    zeroContribution + direction1 + direction2 + direction3 ≤ 7 * N ^ 2 := by
  have hmajor : rankDropGramMajorant zeroContribution M1 M2 M3 ≤ 7 * N ^ 2 :=
    rankDropGramMajorant_le_seven N zeroContribution M1 M2 M3
      hzero htrace1 htrace2 htrace3
  apply le_trans _ hmajor
  unfold rankDropGramMajorant
  omega

end ThreeDirections

section ThreeFinitePointSets

variable {R1 Z1 R2 Z2 R3 Z3 : Type*}
variable [Fintype R1] [Fintype Z1] [DecidableEq R1] [DecidableEq Z1]
variable [Fintype R2] [Fintype Z2] [DecidableEq R2] [DecidableEq Z2]
variable [Fintype R3] [Fintype Z3] [DecidableEq R3] [DecidableEq Z3]

/-- Finite-set interface for the three directional decompositions.  Each set
can use its own row/column coordinate types; in the main application they are
three re-indexings of the same point set. -/
theorem three_finset_direction_majorant_le_seven
    (N : ℕ) (A1 : Finset (R1 × Z1)) (A2 : Finset (R2 × Z2))
    (A3 : Finset (R3 × Z3))
    (hcard1 : A1.card ≤ N) (hcard2 : A2.card ≤ N) (hcard3 : A3.card ≤ N) :
    rankDropGramMajorant (N ^ 2) (finsetIncidence A1)
      (finsetIncidence A2) (finsetIncidence A3) ≤ 7 * N ^ 2 := by
  apply rankDropGramMajorant_le_seven N (N ^ 2)
  · exact le_rfl
  · simpa [gramTrace_finsetIncidence A1] using hcard1
  · simpa [gramTrace_finsetIncidence A2] using hcard2
  · simpa [gramTrace_finsetIncidence A3] using hcard3

end ThreeFinitePointSets

end QuadraticThreefold
end ComplexitySensitiveEnergy
