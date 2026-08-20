import ComplexitySensitiveEnergy.Flagged.ExceptionalEnergy
import ComplexitySensitiveEnergy.Flagged.LocalInterpolation

/-!
# The two-crossing estimate at a flagged partition node

The geometry of a partition is isolated in `CrossingCertificate`.  Its
fields contain only finite support bounds and exact counting/rearrangement
identities.  Both Cauchy--Schwarz inequalities, every monotonicity step, and
all numerical estimates are proved in this file.

In particular the conclusion uses the node-local quantity
`energyLocalLambda W A`, rather than replacing it prematurely by a global
flag parameter.
-/

open scoped BigOperators Pointwise

namespace ComplexitySensitiveEnergy

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Cauchy--Schwarz for a finite family with at most `L` nonzero entries. -/
theorem sq_sum_le_mul_sum_sq_of_active_card_le
    {ι : Type*}
    (s : Finset ι) (f : ι → ℕ) (L : ℕ)
    (hactive : (s.filter fun i => f i ≠ 0).card ≤ L) :
    (∑ i ∈ s, f i) ^ 2 ≤ L * ∑ i ∈ s, f i ^ 2 := by
  classical
  let active := s.filter fun i => f i ≠ 0
  have hactive' : active.card ≤ L := by
    simpa [active] using hactive
  have hsum : (∑ i ∈ active, f i) = ∑ i ∈ s, f i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i his hinot
    have hzero : f i = 0 := by
      by_contra hne
      exact hinot (Finset.mem_filter.mpr ⟨his, hne⟩)
    simp [hzero]
  have hsquares : (∑ i ∈ active, f i ^ 2) =
      ∑ i ∈ s, f i ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i his hinot
    have hzero : f i = 0 := by
      by_contra hne
      exact hinot (Finset.mem_filter.mpr ⟨his, hne⟩)
    simp [hzero]
  rw [← hsum, ← hsquares]
  exact (sq_sum_le_card_mul_sum_sq (s := active) (f := f)).trans
    (Nat.mul_le_mul_right _ hactive')

/-- Enlarging both input sets enlarges every individual representation
count, not merely the total energy. -/
theorem differenceRepresentation_mono
    {A A' B B' : Finset G} (hA : A ⊆ A') (hB : B ⊆ B') (t : G) :
    differenceRepresentation A B t ≤ differenceRepresentation A' B' t := by
  classical
  unfold differenceRepresentation
  apply Finset.card_le_card
  intro ab hab
  rcases Finset.mem_filter.mp hab with ⟨hab, ht⟩
  rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hA ha, hB hb⟩, ht⟩

/-- If `Y ⊆ A`, the energy of `Y` may be summed over the larger support
`A-A`; the added summands are genuinely zero. -/
theorem energy_eq_sum_differenceRepresentation_sq_of_subset
    {Y A : Finset G} (hYA : Y ⊆ A) :
    energy Y =
      ∑ t ∈ differenceSet A A, differenceRepresentation Y Y t ^ 2 := by
  unfold energy differenceEnergy
  apply Finset.sum_subset
  · intro t ht
    rcases mem_differenceSet.mp ht with ⟨y₁, hy₁, y₂, hy₂, rfl⟩
    exact mem_differenceSet.mpr ⟨y₁, hYA hy₁, y₂, hYA hy₂, rfl⟩
  · intro t _ htY
    rw [differenceRepresentation_eq_zero_of_not_mem_differenceSet htY]
    simp

/-- A mixed energy can likewise be summed over the difference support of a
common ambient set. -/
theorem differenceEnergy_eq_sum_differenceRepresentation_sq_of_subsets
    {B C A : Finset G} (hB : B ⊆ A) (hC : C ⊆ A) :
    differenceEnergy B C =
      ∑ t ∈ differenceSet A A, differenceRepresentation B C t ^ 2 := by
  unfold differenceEnergy
  apply Finset.sum_subset
  · intro t ht
    rcases mem_differenceSet.mp ht with ⟨b, hb, c, hc, rfl⟩
    exact mem_differenceSet.mpr ⟨b, hB hb, c, hC hc, rfl⟩
  · intro t _ htBC
    rw [differenceRepresentation_eq_zero_of_not_mem_differenceSet htBC]
    simp

private noncomputable def diagonalPairSet (B C : Finset G) :
    Finset ((G × G) × (G × G)) := by
  classical
  exact ((B ×ˢ B) ×ˢ (C ×ˢ C)).filter fun q =>
    q.1.1 - q.1.2 = q.2.1 - q.2.2

private def diagonalToAdditiveEquiv :
    ((G × G) × (G × G)) ≃ ((G × G) × (G × G)) where
  toFun q := ((q.1.1, q.2.2), (q.1.2, q.2.1))
  invFun q := ((q.1.1, q.2.1), (q.2.2, q.1.2))
  left_inv q := by rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
  right_inv q := by rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl

private theorem card_diagonalPairSet_eq_differenceEnergy
    (B C : Finset G) :
    (diagonalPairSet B C).card = differenceEnergy B C := by
  classical
  rw [differenceEnergy_eq_addEnergy, Finset.addEnergy_eq_card_filter]
  apply Finset.card_equiv diagonalToAdditiveEquiv
  rintro ⟨⟨b₁, b₂⟩, ⟨c₁, c₂⟩⟩
  have heq : b₁ - b₂ = c₁ - c₂ ↔
      b₁ + c₂ = b₂ + c₁ := by
    simpa [add_comm] using
      (sub_eq_sub_iff_add_eq_add (a := b₁) (b := b₂)
        (c := c₁) (d := c₂))
  simp [diagonalPairSet, diagonalToAdditiveEquiv, heq,
    and_assoc, and_left_comm, and_comm]

/-- The paper's mixed identity
`E(B,C) = ∑_u r_{B-B}(u) r_{C-C}(u)`, proved by an explicit finite
rearrangement. -/
theorem mixed_energy_identity (B C : Finset G) :
    differenceEnergy B C =
      ∑ u ∈ differenceSet B B,
        differenceRepresentation B B u * differenceRepresentation C C u := by
  classical
  have hfiber : ∀ u,
      ((diagonalPairSet B C).filter fun q =>
        q.1.1 - q.1.2 = u).card =
        differenceRepresentation B B u *
          differenceRepresentation C C u := by
    intro u
    unfold differenceRepresentation
    rw [← Finset.card_product]
    apply congrArg Finset.card
    ext q
    simp only [diagonalPairSet,
      Finset.mem_filter, Finset.mem_product]
    aesop
  rw [← card_diagonalPairSet_eq_differenceEnergy]
  symm
  calc
    (∑ u ∈ differenceSet B B,
        differenceRepresentation B B u *
          differenceRepresentation C C u) =
        ∑ u ∈ differenceSet B B,
          ((diagonalPairSet B C).filter fun q =>
            q.1.1 - q.1.2 = u).card := by
      apply Finset.sum_congr rfl
      intro u hu
      exact (hfiber u).symm
    _ = ((diagonalPairSet B C).filter fun q =>
        q.1.1 - q.1.2 ∈ differenceSet B B).card := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
    _ = (diagonalPairSet B C).card := by
      apply congrArg Finset.card
      ext q
      simp only [diagonalPairSet, Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨hq, hu⟩
        exact hq
      · rintro hq
        refine ⟨hq, ?_⟩
        exact mem_differenceSet.mpr
          ⟨q.1.1, hq.1.1.1, q.1.2, hq.1.1.2, rfl⟩

/-- Ambient-support form of `mixed_energy_identity`. -/
theorem mixed_energy_identity_on_ambient
    {B C A : Finset G} (hB : B ⊆ A) :
    differenceEnergy B C =
      ∑ u ∈ differenceSet A A,
        differenceRepresentation B B u * differenceRepresentation C C u := by
  rw [mixed_energy_identity]
  apply Finset.sum_subset
  · intro u hu
    rcases mem_differenceSet.mp hu with ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    exact mem_differenceSet.mpr ⟨b₁, hB hb₁, b₂, hB hb₂, rfl⟩
  · intro u huA huB
    rw [differenceRepresentation_eq_zero_of_not_mem_differenceSet huB]
    simp

/-- The full crossing rearrangement is a universal finite identity; it is
not geometric certificate data. -/
theorem mixed_rearrangement
    (A : Finset G) (cells : Finset (Finset G))
    (hcell : ∀ B ∈ cells, B ⊆ A) :
    (∑ t ∈ differenceSet A A,
        ∑ BC ∈ cells ×ˢ cells,
          differenceRepresentation BC.1 BC.2 t ^ 2) =
      ∑ u ∈ differenceSet A A,
        (∑ B ∈ cells, differenceRepresentation B B u) ^ 2 := by
  classical
  calc
    (∑ t ∈ differenceSet A A,
        ∑ BC ∈ cells ×ˢ cells,
          differenceRepresentation BC.1 BC.2 t ^ 2) =
        ∑ BC ∈ cells ×ˢ cells,
          ∑ t ∈ differenceSet A A,
            differenceRepresentation BC.1 BC.2 t ^ 2 := by
      rw [Finset.sum_comm]
    _ = ∑ BC ∈ cells ×ˢ cells,
        differenceEnergy BC.1 BC.2 := by
      apply Finset.sum_congr rfl
      intro BC hBC
      exact (differenceEnergy_eq_sum_differenceRepresentation_sq_of_subsets
        (hcell BC.1 (Finset.mem_product.mp hBC).1)
        (hcell BC.2 (Finset.mem_product.mp hBC).2)).symm
    _ = ∑ BC ∈ cells ×ˢ cells,
        ∑ u ∈ differenceSet A A,
          differenceRepresentation BC.1 BC.1 u *
            differenceRepresentation BC.2 BC.2 u := by
      apply Finset.sum_congr rfl
      intro BC hBC
      exact mixed_energy_identity_on_ambient
        (hcell BC.1 (Finset.mem_product.mp hBC).1)
    _ = ∑ u ∈ differenceSet A A,
        ∑ BC ∈ cells ×ˢ cells,
          differenceRepresentation BC.1 BC.1 u *
            differenceRepresentation BC.2 BC.2 u := by
      rw [Finset.sum_comm]
    _ = ∑ u ∈ differenceSet A A,
        (∑ B ∈ cells, differenceRepresentation B B u) ^ 2 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_product]

end ComplexitySensitiveEnergy

namespace ComplexitySensitiveEnergy.PaperVariety

variable {n : ℕ}

/-- The finite geometric data needed by the two-crossing argument.

`first_decomposition` and `diagonal_decomposition` are exact partition
identities.  The two `active_support` fields are the output of the geometric
crossing-number argument.  The universal mixed rearrangement is proved
above, rather than stored in this structure.  No energy or
Cauchy--Schwarz inequality is assumed here. -/
structure CrossingCertificate
    (W : PaperVariety n) (A Y : Finset (RVec n)) (L : ℕ) where
  /-- Pieces of the partition node. -/
  cells : Finset (Finset (RVec n))
  /-- The retained points really belong to the node. -/
  y_subset : Y ⊆ A
  /-- Every cell piece belongs to the node. -/
  cell_subset : ∀ B ∈ cells, B ⊆ A
  /-- Decomposition of a retained representation into ordered cell pairs. -/
  first_decomposition :
    ∀ t ∈ differenceSet A A,
      differenceRepresentation Y Y t =
        ∑ BC ∈ cells ×ˢ cells,
          differenceRepresentation BC.1 BC.2 t
  /-- Away from the exceptional translations, at most `L` cell pairs cross. -/
  first_active_support :
    ∀ t ∈ differenceSet A A,
      t ∉ W.exceptionalDifferenceSet A →
        ((cells ×ˢ cells).filter fun BC =>
          differenceRepresentation BC.1 BC.2 t ≠ 0).card ≤ L
  /-- The diagonal cell counts form a subcount of the node count. -/
  diagonal_decomposition :
    ∀ u ∈ differenceSet A A,
      ∃ remainder : ℕ,
        differenceRepresentation A A u =
          (∑ B ∈ cells, differenceRepresentation B B u) + remainder
  /-- Away from the exceptional translations, at most `L` diagonal pieces
  are active in the second crossing. -/
  second_active_support :
    ∀ u ∈ differenceSet A A,
      u ∉ W.exceptionalDifferenceSet A →
        (cells.filter fun B =>
          differenceRepresentation B B u ≠ 0).card ≤ L

namespace CrossingCertificate

variable {W : PaperVariety n} {A Y : Finset (RVec n)} {L : ℕ}

private theorem sum_exceptionalIndicator
    (W : PaperVariety n) (A : Finset (RVec n)) :
    (∑ t ∈ differenceSet A A,
      if t ∈ W.exceptionalDifferenceSet A then
        differenceRepresentation A A t ^ 2 else 0) =
      W.exceptionalEnergy A := by
  classical
  unfold exceptionalEnergy exceptionalDifferenceSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  simp [ht]

/-- The first Cauchy--Schwarz crossing. -/
theorem first_crossing
    (C : CrossingCertificate W A Y L) :
    energy Y ≤ W.exceptionalEnergy A +
      L * (∑ t ∈ differenceSet A A,
        ∑ BC ∈ C.cells ×ˢ C.cells,
          differenceRepresentation BC.1 BC.2 t ^ 2) := by
  classical
  rw [energy_eq_sum_differenceRepresentation_sq_of_subset C.y_subset]
  calc
    (∑ t ∈ differenceSet A A,
        differenceRepresentation Y Y t ^ 2) ≤
        ∑ t ∈ differenceSet A A,
          ((if t ∈ W.exceptionalDifferenceSet A then
              differenceRepresentation A A t ^ 2 else 0) +
            L * (∑ BC ∈ C.cells ×ˢ C.cells,
              differenceRepresentation BC.1 BC.2 t ^ 2)) := by
      apply Finset.sum_le_sum
      intro t ht
      by_cases hex : t ∈ W.exceptionalDifferenceSet A
      · have hrep := differenceRepresentation_mono
          C.y_subset C.y_subset t
        have hsq : differenceRepresentation Y Y t ^ 2 ≤
            differenceRepresentation A A t ^ 2 :=
          Nat.pow_le_pow_left hrep 2
        simpa [hex] using hsq.trans
          (Nat.le_add_right
            (differenceRepresentation A A t ^ 2)
            (L * ∑ BC ∈ C.cells ×ˢ C.cells,
              differenceRepresentation BC.1 BC.2 t ^ 2))
      · rw [C.first_decomposition t ht]
        simpa [hex] using
          sq_sum_le_mul_sum_sq_of_active_card_le
            (C.cells ×ˢ C.cells)
            (fun BC => differenceRepresentation BC.1 BC.2 t) L
            (C.first_active_support t ht hex)
    _ = W.exceptionalEnergy A +
        L * (∑ t ∈ differenceSet A A,
          ∑ BC ∈ C.cells ×ˢ C.cells,
            differenceRepresentation BC.1 BC.2 t ^ 2) := by
      rw [Finset.sum_add_distrib, sum_exceptionalIndicator]
      rw [Finset.mul_sum]

private theorem sum_diagonalSquares_eq_sum_energy
    (C : CrossingCertificate W A Y L) :
    (∑ u ∈ differenceSet A A,
        ∑ B ∈ C.cells, differenceRepresentation B B u ^ 2) =
      ∑ B ∈ C.cells, energy B := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B hB
  exact (energy_eq_sum_differenceRepresentation_sq_of_subset
    (C.cell_subset B hB)).symm

/-- The second Cauchy--Schwarz crossing, including the exact rearrangement. -/
theorem second_crossing
    (C : CrossingCertificate W A Y L) :
    (∑ t ∈ differenceSet A A,
        ∑ BC ∈ C.cells ×ˢ C.cells,
          differenceRepresentation BC.1 BC.2 t ^ 2) ≤
      W.exceptionalEnergy A + L * ∑ B ∈ C.cells, energy B := by
  classical
  rw [mixed_rearrangement A C.cells C.cell_subset]
  calc
    (∑ u ∈ differenceSet A A,
        (∑ B ∈ C.cells, differenceRepresentation B B u) ^ 2) ≤
        ∑ u ∈ differenceSet A A,
          ((if u ∈ W.exceptionalDifferenceSet A then
              differenceRepresentation A A u ^ 2 else 0) +
            L * (∑ B ∈ C.cells,
              differenceRepresentation B B u ^ 2)) := by
      apply Finset.sum_le_sum
      intro u hu
      by_cases hex : u ∈ W.exceptionalDifferenceSet A
      · rcases C.diagonal_decomposition u hu with ⟨remainder, hdecomp⟩
        have hdiag : (∑ B ∈ C.cells,
            differenceRepresentation B B u) ≤
            differenceRepresentation A A u := by omega
        have hsq : (∑ B ∈ C.cells,
            differenceRepresentation B B u) ^ 2 ≤
            differenceRepresentation A A u ^ 2 :=
          Nat.pow_le_pow_left hdiag 2
        simpa [hex] using hsq.trans
          (Nat.le_add_right
            (differenceRepresentation A A u ^ 2)
            (L * ∑ B ∈ C.cells,
              differenceRepresentation B B u ^ 2))
      · simpa [hex] using
          sq_sum_le_mul_sum_sq_of_active_card_le C.cells
            (fun B => differenceRepresentation B B u) L
            (C.second_active_support u hu hex)
    _ = W.exceptionalEnergy A +
        L * (∑ u ∈ differenceSet A A,
          ∑ B ∈ C.cells,
            differenceRepresentation B B u ^ 2) := by
      rw [Finset.sum_add_distrib, sum_exceptionalIndicator]
      rw [Finset.mul_sum]
    _ = W.exceptionalEnergy A + L * ∑ B ∈ C.cells, energy B := by
      rw [C.sum_diagonalSquares_eq_sum_energy]

/-- Pure two-crossing estimate before inserting the exceptional-energy
bound.  Both appearances of `exceptionalEnergy` arise from explicit
exceptional summands in the two Cauchy--Schwarz steps. -/
theorem two_crossing
    (C : CrossingCertificate W A Y L) :
    energy Y ≤ (L + 1) * W.exceptionalEnergy A +
      L ^ 2 * ∑ B ∈ C.cells, energy B := by
  calc
    energy Y ≤ W.exceptionalEnergy A +
        L * (∑ t ∈ differenceSet A A,
          ∑ BC ∈ C.cells ×ˢ C.cells,
            differenceRepresentation BC.1 BC.2 t ^ 2) := C.first_crossing
    _ ≤ W.exceptionalEnergy A +
        L * (W.exceptionalEnergy A +
          L * ∑ B ∈ C.cells, energy B) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left L C.second_crossing) _
    _ = (L + 1) * W.exceptionalEnergy A +
        L ^ 2 * ∑ B ∈ C.cells, energy B := by ring

/-- The two-crossing estimate with Lemma 3.1 inserted.  The concentration
parameter is still exactly the node-local `energyLocalLambda W A`. -/
theorem two_crossing_local_lambda
    (C : CrossingCertificate W A Y L)
    (hA : ∀ x ∈ A, x ∈ W.realPoints) :
    energy Y ≤
      2 * (L + 1) * W.energyLocalLambda A * A.card ^ 2 +
        L ^ 2 * ∑ B ∈ C.cells, energy B := by
  calc
    energy Y ≤ (L + 1) * W.exceptionalEnergy A +
        L ^ 2 * ∑ B ∈ C.cells, energy B := C.two_crossing
    _ ≤ (L + 1) *
          (2 * W.energyLocalLambda A * A.card ^ 2) +
        L ^ 2 * ∑ B ∈ C.cells, energy B :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_left (L + 1) (W.exceptionalEnergy_le A hA)) _
    _ = 2 * (L + 1) * W.energyLocalLambda A * A.card ^ 2 +
        L ^ 2 * ∑ B ∈ C.cells, energy B := by ring

/-- A paper-shaped simplification of the local estimate.  The only extra
input is the natural geometric fact that the crossing number is positive. -/
theorem two_crossing_local_lambda_four
    (C : CrossingCertificate W A Y L)
    (hA : ∀ x ∈ A, x ∈ W.realPoints) (hL : 1 ≤ L) :
    energy Y ≤
      4 * L * W.energyLocalLambda A * A.card ^ 2 +
        L ^ 2 * ∑ B ∈ C.cells, energy B := by
  have hcoef : 2 * (L + 1) ≤ 4 * L := by omega
  have hmain := C.two_crossing_local_lambda hA
  exact hmain.trans <| Nat.add_le_add_right
    (by
      simpa only [mul_assoc] using
        Nat.mul_le_mul_right (W.energyLocalLambda A * A.card ^ 2) hcoef) _

end CrossingCertificate

end ComplexitySensitiveEnergy.PaperVariety
