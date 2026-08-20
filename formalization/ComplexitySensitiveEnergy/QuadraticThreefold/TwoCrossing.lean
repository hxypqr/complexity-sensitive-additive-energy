import ComplexitySensitiveEnergy.Flagged.TwoCrossing
import ComplexitySensitiveEnergy.QuadraticThreefold.RankDrop

/-!
# The two-crossing kernel for the quadratic threefold

This file proves the finite combinatorial content of Proposition 4.5
(`prop:threefold-cell`) in the attached version of the paper.  The
certificate below records only the exact cell decompositions and the two
geometric active-support bounds.  The mixed rearrangement and both
Cauchy--Schwarz estimates are proved internally.

The exceptional translations are represented by an actual finite set.  A
second, independent certificate identifies their literal energy with the
zero displacement and the three directional Gram contributions.  Thus no
field of either certificate assumes the cellular energy estimate that we
eventually prove.
-/

open scoped BigOperators Pointwise

namespace ComplexitySensitiveEnergy.QuadraticThreefold

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The literal part of the difference energy supported on a designated
finite set of rank-drop translations. -/
def rankDropEnergy (X rankDropSet : Finset G) : ℕ :=
  ∑ t ∈ differenceSet X X,
    if t ∈ rankDropSet then differenceRepresentation X X t ^ 2 else 0

/-- Granular geometric input for the two crossings.

The two decomposition fields are exact counting identities.  The two
support fields are precisely the polynomial-partition crossing conclusions.
There is deliberately no energy inequality in this structure. -/
structure ThreefoldCrossingCertificate
    (X Y : Finset G) (D : ℕ) where
  cells : Finset (Finset G)
  rankDropSet : Finset G
  retained_subset : Y ⊆ X
  cell_subset : ∀ B ∈ cells, B ⊆ X
  first_decomposition :
    ∀ t ∈ differenceSet X X,
      differenceRepresentation Y Y t =
        ∑ BC ∈ cells ×ˢ cells,
          differenceRepresentation BC.1 BC.2 t
  first_active_support :
    ∀ t ∈ differenceSet X X, t ∉ rankDropSet →
      ((cells ×ˢ cells).filter fun BC =>
        differenceRepresentation BC.1 BC.2 t ≠ 0).card ≤ D
  diagonal_decomposition :
    ∀ u ∈ differenceSet X X,
      ∃ remainder : ℕ,
        differenceRepresentation X X u =
          (∑ B ∈ cells, differenceRepresentation B B u) + remainder
  second_active_support :
    ∀ u ∈ differenceSet X X, u ∉ rankDropSet →
      (cells.filter fun B =>
        differenceRepresentation B B u ≠ 0).card ≤ D

namespace ThreefoldCrossingCertificate

variable {X Y : Finset G} {D : ℕ}

private theorem sum_rankDropIndicator
    (C : ThreefoldCrossingCertificate X Y D) :
    (∑ t ∈ differenceSet X X,
      if t ∈ C.rankDropSet then
        differenceRepresentation X X t ^ 2 else 0) =
      rankDropEnergy X C.rankDropSet := by
  rfl

/-- The first crossing: exceptional translations are kept as a literal
summand, while Cauchy--Schwarz is applied on every other fiber. -/
theorem first_crossing (C : ThreefoldCrossingCertificate X Y D) :
    energy Y ≤ rankDropEnergy X C.rankDropSet +
      D * (∑ t ∈ differenceSet X X,
        ∑ BC ∈ C.cells ×ˢ C.cells,
          differenceRepresentation BC.1 BC.2 t ^ 2) := by
  classical
  rw [energy_eq_sum_differenceRepresentation_sq_of_subset
    C.retained_subset]
  calc
    (∑ t ∈ differenceSet X X,
        differenceRepresentation Y Y t ^ 2) ≤
        ∑ t ∈ differenceSet X X,
          ((if t ∈ C.rankDropSet then
              differenceRepresentation X X t ^ 2 else 0) +
            D * (∑ BC ∈ C.cells ×ˢ C.cells,
              differenceRepresentation BC.1 BC.2 t ^ 2)) := by
      apply Finset.sum_le_sum
      intro t ht
      by_cases hex : t ∈ C.rankDropSet
      · have hrep := differenceRepresentation_mono
          C.retained_subset C.retained_subset t
        have hsq : differenceRepresentation Y Y t ^ 2 ≤
            differenceRepresentation X X t ^ 2 :=
          Nat.pow_le_pow_left hrep 2
        simpa [hex] using hsq.trans
          (Nat.le_add_right
            (differenceRepresentation X X t ^ 2)
            (D * ∑ BC ∈ C.cells ×ˢ C.cells,
              differenceRepresentation BC.1 BC.2 t ^ 2))
      · rw [C.first_decomposition t ht]
        simpa [hex] using
          sq_sum_le_mul_sum_sq_of_active_card_le
            (C.cells ×ˢ C.cells)
            (fun BC => differenceRepresentation BC.1 BC.2 t) D
            (C.first_active_support t ht hex)
    _ = rankDropEnergy X C.rankDropSet +
        D * (∑ t ∈ differenceSet X X,
          ∑ BC ∈ C.cells ×ˢ C.cells,
            differenceRepresentation BC.1 BC.2 t ^ 2) := by
      rw [Finset.sum_add_distrib, C.sum_rankDropIndicator]
      rw [Finset.mul_sum]

private theorem sum_diagonalSquares_eq_sum_energy
    (C : ThreefoldCrossingCertificate X Y D) :
    (∑ u ∈ differenceSet X X,
        ∑ B ∈ C.cells, differenceRepresentation B B u ^ 2) =
      ∑ B ∈ C.cells, energy B := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B hB
  exact (energy_eq_sum_differenceRepresentation_sq_of_subset
    (C.cell_subset B hB)).symm

/-- The second crossing.  The mixed-energy rearrangement invoked here is
the universal finite identity proved in `Flagged.TwoCrossing`, not a field
of the geometric certificate. -/
theorem second_crossing (C : ThreefoldCrossingCertificate X Y D) :
    (∑ t ∈ differenceSet X X,
        ∑ BC ∈ C.cells ×ˢ C.cells,
          differenceRepresentation BC.1 BC.2 t ^ 2) ≤
      rankDropEnergy X C.rankDropSet +
        D * ∑ B ∈ C.cells, energy B := by
  classical
  rw [mixed_rearrangement X C.cells C.cell_subset]
  calc
    (∑ u ∈ differenceSet X X,
        (∑ B ∈ C.cells, differenceRepresentation B B u) ^ 2) ≤
        ∑ u ∈ differenceSet X X,
          ((if u ∈ C.rankDropSet then
              differenceRepresentation X X u ^ 2 else 0) +
            D * (∑ B ∈ C.cells,
              differenceRepresentation B B u ^ 2)) := by
      apply Finset.sum_le_sum
      intro u hu
      by_cases hex : u ∈ C.rankDropSet
      · rcases C.diagonal_decomposition u hu with ⟨remainder, hdecomp⟩
        have hdiag : (∑ B ∈ C.cells,
            differenceRepresentation B B u) ≤
            differenceRepresentation X X u := by omega
        have hsq : (∑ B ∈ C.cells,
            differenceRepresentation B B u) ^ 2 ≤
            differenceRepresentation X X u ^ 2 :=
          Nat.pow_le_pow_left hdiag 2
        simpa [hex] using hsq.trans
          (Nat.le_add_right
            (differenceRepresentation X X u ^ 2)
            (D * ∑ B ∈ C.cells,
              differenceRepresentation B B u ^ 2))
      · simpa [hex] using
          sq_sum_le_mul_sum_sq_of_active_card_le C.cells
            (fun B => differenceRepresentation B B u) D
            (C.second_active_support u hu hex)
    _ = rankDropEnergy X C.rankDropSet +
        D * (∑ u ∈ differenceSet X X,
          ∑ B ∈ C.cells,
            differenceRepresentation B B u ^ 2) := by
      rw [Finset.sum_add_distrib, C.sum_rankDropIndicator]
      rw [Finset.mul_sum]
    _ = rankDropEnergy X C.rankDropSet +
        D * ∑ B ∈ C.cells, energy B := by
      rw [C.sum_diagonalSquares_eq_sum_energy]

/-- The two Cauchy--Schwarz steps before the rank-drop Gram bound is
inserted.  This is the exact finite analogue of (4.11)--(4.13). -/
theorem two_crossing (C : ThreefoldCrossingCertificate X Y D) :
    energy Y ≤ (D + 1) * rankDropEnergy X C.rankDropSet +
      D ^ 2 * ∑ B ∈ C.cells, energy B := by
  calc
    energy Y ≤ rankDropEnergy X C.rankDropSet +
        D * (∑ t ∈ differenceSet X X,
          ∑ BC ∈ C.cells ×ˢ C.cells,
            differenceRepresentation BC.1 BC.2 t ^ 2) := C.first_crossing
    _ ≤ rankDropEnergy X C.rankDropSet +
        D * (rankDropEnergy X C.rankDropSet +
          D * ∑ B ∈ C.cells, energy B) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left D C.second_crossing) _
    _ = (D + 1) * rankDropEnergy X C.rankDropSet +
        D ^ 2 * ∑ B ∈ C.cells, energy B := by ring

end ThreefoldCrossingCertificate

/-- Exact finite Gram data for the rank-drop set.

Each direction is represented by a genuine zero-one incidence set.  Its
Gram trace and the resulting square bound are therefore derived internally
from cardinality. -/
structure RankDropGramCertificate
    (X rankDropSet : Finset G) where
  rowCount1 : ℕ
  columnCount1 : ℕ
  rowCount2 : ℕ
  columnCount2 : ℕ
  rowCount3 : ℕ
  columnCount3 : ℕ
  incidence1 : Finset (Fin rowCount1 × Fin columnCount1)
  incidence2 : Finset (Fin rowCount2 × Fin columnCount2)
  incidence3 : Finset (Fin rowCount3 × Fin columnCount3)
  zeroContribution : ℕ
  direction1 : ℕ
  direction2 : ℕ
  direction3 : ℕ
  exceptional_decomposition :
    rankDropEnergy X rankDropSet =
      zeroContribution + direction1 + direction2 + direction3
  zero_bound : zeroContribution ≤ X.card ^ 2
  direction1_bound : direction1 ≤
    offDiagonalGramSquareSum (finsetIncidence incidence1)
  direction2_bound : direction2 ≤
    offDiagonalGramSquareSum (finsetIncidence incidence2)
  direction3_bound : direction3 ≤
    offDiagonalGramSquareSum (finsetIncidence incidence3)
  incidence1_card : incidence1.card ≤ X.card
  incidence2_card : incidence2.card ≤ X.card
  incidence3_card : incidence3.card ≤ X.card

namespace RankDropGramCertificate

variable {X rankDropSet : Finset G}

/-- Lemma 4.1, with the paper's coefficient `7`, from the literal
zero-plus-three-directions decomposition. -/
theorem energy_le_seven
    (R : RankDropGramCertificate X rankDropSet) :
    rankDropEnergy X rankDropSet ≤ 7 * X.card ^ 2 := by
  rw [R.exceptional_decomposition]
  apply rankDrop_contributions_le_seven X.card R.zeroContribution
    R.direction1 R.direction2 R.direction3
    (finsetIncidence R.incidence1)
    (finsetIncidence R.incidence2)
    (finsetIncidence R.incidence3)
  · exact R.zero_bound
  · exact R.direction1_bound
  · exact R.direction2_bound
  · exact R.direction3_bound
  · simpa only [gramTrace_finsetIncidence] using R.incidence1_card
  · simpa only [gramTrace_finsetIncidence] using R.incidence2_card
  · simpa only [gramTrace_finsetIncidence] using R.incidence3_card

end RankDropGramCertificate

namespace ThreefoldCrossingCertificate

variable {X Y : Finset G} {D : ℕ}

/-- Proposition 4.5 (`prop:threefold-cell`) with an explicit absolute
constant.  The two occurrences
of the rank-drop energy yield `(D+1) * 7 N²`; for `D ≥ 1` this is absorbed
by `14 D N²`.  The coefficient `14` also harmlessly enlarges the cellular
term, giving exactly the recurrence shape used later. -/
theorem two_crossing_rankDrop
    (C : ThreefoldCrossingCertificate X Y D)
    (R : RankDropGramCertificate X C.rankDropSet)
    (hD : 1 ≤ D) :
    energy Y ≤ 14 *
      (D * X.card ^ 2 + D ^ 2 * ∑ B ∈ C.cells, energy B) := by
  have hrank := R.energy_le_seven
  have hcoef : (D + 1) * 7 ≤ 14 * D := by omega
  have hexceptional :
      (D + 1) * rankDropEnergy X C.rankDropSet ≤
        14 * D * X.card ^ 2 := by
    calc
      (D + 1) * rankDropEnergy X C.rankDropSet ≤
          (D + 1) * (7 * X.card ^ 2) :=
        Nat.mul_le_mul_left (D + 1) hrank
      _ = ((D + 1) * 7) * X.card ^ 2 := by ring
      _ ≤ (14 * D) * X.card ^ 2 :=
        Nat.mul_le_mul_right (X.card ^ 2) hcoef
  have hcell : D ^ 2 * (∑ B ∈ C.cells, energy B) ≤
      14 * (D ^ 2 * ∑ B ∈ C.cells, energy B) := by omega
  calc
    energy Y ≤ (D + 1) * rankDropEnergy X C.rankDropSet +
        D ^ 2 * ∑ B ∈ C.cells, energy B := C.two_crossing
    _ ≤ 14 * D * X.card ^ 2 +
        14 * (D ^ 2 * ∑ B ∈ C.cells, energy B) :=
      Nat.add_le_add hexceptional hcell
    _ = 14 *
        (D * X.card ^ 2 + D ^ 2 * ∑ B ∈ C.cells, energy B) := by
      ring

/-- Real-valued form used by the recurrence certificate.  Any chosen
uniform cellular coefficient at least `14` may absorb the explicit finite
constant. -/
theorem cell_estimate_real
    (C : ThreefoldCrossingCertificate X Y D)
    (R : RankDropGramCertificate X C.rankDropSet)
    (hD : 1 ≤ D) (cellCoefficient : ℝ)
    (hcellCoefficient : (14 : ℝ) ≤ cellCoefficient) :
    (energy Y : ℝ) ≤ cellCoefficient *
      ((D : ℝ) * (X.card : ℝ) ^ (2 : ℕ) +
        (D : ℝ) ^ (2 : ℕ) *
          ∑ B ∈ C.cells, (energy B : ℝ)) := by
  let base : ℝ :=
    (D : ℝ) * (X.card : ℝ) ^ (2 : ℕ) +
      (D : ℝ) ^ (2 : ℕ) *
        ∑ B ∈ C.cells, (energy B : ℝ)
  have hnat := C.two_crossing_rankDrop R hD
  have hcast : (energy Y : ℝ) ≤ 14 * base := by
    dsimp only [base]
    exact_mod_cast hnat
  exact hcast.trans <| by
    exact mul_le_mul_of_nonneg_right hcellCoefficient (by
      dsimp only [base]
      positivity)

end ThreefoldCrossingCertificate

end ComplexitySensitiveEnergy.QuadraticThreefold
