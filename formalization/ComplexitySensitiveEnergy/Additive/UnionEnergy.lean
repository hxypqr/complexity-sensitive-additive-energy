import ComplexitySensitiveEnergy.Additive.Energy
import Mathlib

/-!
# Additive energy of finite disjoint unions

This file proves the finite union estimate needed by the flagged recurrence
using only finite counting and Cauchy--Schwarz.  No Fourier or Minkowski
statement is taken as an input.
-/

open scoped BigOperators Pointwise

namespace ComplexitySensitiveEnergy

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Quadruples from `A² × B²` whose two internal differences agree. -/
def sameDifferenceWitnesses (A B : Finset G) :
    Finset ((G × G) × (G × G)) :=
  ((A ×ˢ A) ×ˢ (B ×ˢ B)).filter fun q =>
    q.1.1 - q.1.2 = q.2.1 - q.2.2

/-- Regroup an additive-energy quadruple and reverse the `B` pair. -/
def addEnergyToSameDifferenceEquiv :
    ((G × G) × (G × G)) ≃ ((G × G) × (G × G)) where
  toFun q := ((q.1.1, q.2.1), (q.2.2, q.1.2))
  invFun q := ((q.1.1, q.2.2), (q.1.2, q.2.1))
  left_inv q := by rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
  right_inv q := by rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl

/-- Mixed difference energy is the cardinality of the equal-difference
correlation witness set. -/
theorem differenceEnergy_eq_card_sameDifferenceWitnesses
    (A B : Finset G) :
    differenceEnergy A B = (sameDifferenceWitnesses A B).card := by
  rw [differenceEnergy_eq_addEnergy, Finset.addEnergy_eq_card_filter]
  apply Finset.card_equiv (addEnergyToSameDifferenceEquiv (G := G))
  rintro ⟨⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩
  have heq : a₁ + b₁ = a₂ + b₂ ↔ a₁ - a₂ = b₂ - b₁ := by
    simpa [add_comm] using
      (sub_eq_sub_iff_add_eq_add
        (a := a₁) (b := a₂) (c := b₂) (d := b₁)).symm
  simp [sameDifferenceWitnesses, addEnergyToSameDifferenceEquiv,
    heq, and_assoc, and_left_comm, and_comm]

/-- A common finite support for the two self-difference representation
functions. -/
def correlationSupport (A B : Finset G) : Finset G :=
  differenceSet A A ∪ differenceSet B B

private def correlationFiber (A B : Finset G) (t : G) :
    Finset ((G × G) × (G × G)) :=
  (((A ×ˢ A).filter fun aa => aa.1 - aa.2 = t) ×ˢ
    ((B ×ˢ B).filter fun bb => bb.1 - bb.2 = t))

private theorem correlationFiber_pairwiseDisjoint (A B : Finset G) :
    ((correlationSupport A B : Finset G) : Set G).PairwiseDisjoint
      (correlationFiber A B) := by
  intro t ht u hu htu
  change Disjoint (correlationFiber A B t) (correlationFiber A B u)
  rw [Finset.disjoint_left]
  intro q hqt hqu
  have htEq := (Finset.mem_filter.mp (Finset.mem_product.mp hqt).1).2
  have huEq := (Finset.mem_filter.mp (Finset.mem_product.mp hqu).1).2
  exact htu (htEq.symm.trans huEq)

private theorem biUnion_correlationFiber (A B : Finset G) :
    (correlationSupport A B).biUnion (correlationFiber A B) =
      sameDifferenceWitnesses A B := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_biUnion.mp hq with ⟨t, ht, hqt⟩
    rcases Finset.mem_product.mp hqt with ⟨hA, hB⟩
    rcases Finset.mem_filter.mp hA with ⟨hAA, hAt⟩
    rcases Finset.mem_filter.mp hB with ⟨hBB, hBt⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hAA, hBB⟩, hAt.trans hBt.symm⟩
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hprod, heq⟩
    rcases Finset.mem_product.mp hprod with ⟨hAA, hBB⟩
    let t : G := q.1.1 - q.1.2
    have ht : t ∈ correlationSupport A B := by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨q.1, hAA, rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨t, ht, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨hAA, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hBB, heq.symm⟩

/-- Correlation identity
`E(A,B)=∑ₜ r_{A-A}(t) r_{B-B}(t)`. -/
theorem differenceEnergy_eq_sum_selfRepresentation_mul
    (A B : Finset G) :
    differenceEnergy A B =
      ∑ t ∈ correlationSupport A B,
        differenceRepresentation A A t * differenceRepresentation B B t := by
  rw [differenceEnergy_eq_card_sameDifferenceWitnesses,
    ← biUnion_correlationFiber]
  rw [Finset.card_biUnion (correlationFiber_pairwiseDisjoint A B)]
  apply Finset.sum_congr rfl
  intro t ht
  simp [correlationFiber, differenceRepresentation]

private theorem sum_selfRepresentation_sq_on_correlationSupport
    (A B : Finset G) :
    (∑ t ∈ correlationSupport A B,
      differenceRepresentation A A t ^ 2) = energy A := by
  unfold energy differenceEnergy
  apply (Finset.sum_subset (Finset.subset_union_left) ?_).symm
  intro t ht htA
  rw [differenceRepresentation_eq_zero_of_not_mem_differenceSet htA]
  simp

/-- Cauchy--Schwarz for mixed energy, in a square-root-free natural-number
form. -/
theorem differenceEnergy_sq_le_energy_mul_energy (A B : Finset G) :
    differenceEnergy A B ^ 2 ≤ energy A * energy B := by
  rw [differenceEnergy_eq_sum_selfRepresentation_mul]
  calc
    (∑ t ∈ correlationSupport A B,
        differenceRepresentation A A t *
          differenceRepresentation B B t) ^ 2 ≤
        (∑ t ∈ correlationSupport A B,
          differenceRepresentation A A t ^ 2) *
        (∑ t ∈ correlationSupport A B,
          differenceRepresentation B B t ^ 2) := by
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = energy A * energy B := by
      have hBsum :
          (∑ t ∈ correlationSupport A B,
            differenceRepresentation B B t ^ 2) = energy B := by
        rw [show correlationSupport A B = correlationSupport B A by
          simp [correlationSupport, Finset.union_comm]]
        exact sum_selfRepresentation_sq_on_correlationSupport B A
      rw [sum_selfRepresentation_sq_on_correlationSupport A B, hBsum]

/-- Arithmetic--geometric mean consequence of mixed-energy
Cauchy--Schwarz. -/
theorem two_mul_differenceEnergy_le_energy_add_energy (A B : Finset G) :
    2 * differenceEnergy A B ≤ energy A + energy B := by
  have hsq := differenceEnergy_sq_le_energy_mul_energy A B
  have hsqR :
      (differenceEnergy A B : ℝ) ^ 2 ≤ (energy A : ℝ) * (energy B : ℝ) := by
    exact_mod_cast hsq
  have hreal :
      (2 : ℝ) * differenceEnergy A B ≤ (energy A : ℝ) + energy B := by
    nlinarith [sq_nonneg ((energy A : ℝ) - energy B)]
  exact_mod_cast hreal

section DisjointUnion

variable {ι : Type*} [DecidableEq ι]

private def differenceFiber (A B : Finset G) (t : G) : Finset (G × G) :=
  (A ×ˢ B).filter fun ab => ab.1 - ab.2 = t

private def differenceFiberRow (s : Finset ι) (piece : ι → Finset G)
    (i : ι) (t : G) : Finset (G × G) :=
  s.biUnion fun j => differenceFiber (piece i) (piece j) t

omit [DecidableEq ι] in
private theorem differenceFiber_pairwiseDisjoint_right
    (s : Finset ι) (piece : ι → Finset G)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (piece i) (piece j))
    (i : ι) (t : G) :
    ((s : Finset ι) : Set ι).PairwiseDisjoint fun j =>
      differenceFiber (piece i) (piece j) t := by
  intro j hj k hk hjk
  change Disjoint (differenceFiber (piece i) (piece j) t)
    (differenceFiber (piece i) (piece k) t)
  rw [Finset.disjoint_left]
  intro ab habj habk
  have hbj := (Finset.mem_product.mp (Finset.mem_filter.mp habj).1).2
  have hbk := (Finset.mem_product.mp (Finset.mem_filter.mp habk).1).2
  exact (Finset.disjoint_left.mp (hdisj j hj k hk hjk)) hbj hbk

omit [DecidableEq ι] in
private theorem differenceFiberRow_pairwiseDisjoint
    (s : Finset ι) (piece : ι → Finset G)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (piece i) (piece j))
    (t : G) :
    ((s : Finset ι) : Set ι).PairwiseDisjoint fun i =>
      differenceFiberRow s piece i t := by
  intro i hi k hk hik
  change Disjoint (differenceFiberRow s piece i t)
    (differenceFiberRow s piece k t)
  rw [Finset.disjoint_left]
  intro ab habi habk
  rcases Finset.mem_biUnion.mp habi with ⟨j, hj, habij⟩
  rcases Finset.mem_biUnion.mp habk with ⟨l, hl, habkl⟩
  have hai := (Finset.mem_product.mp (Finset.mem_filter.mp habij).1).1
  have hak := (Finset.mem_product.mp (Finset.mem_filter.mp habkl).1).1
  exact (Finset.disjoint_left.mp (hdisj i hi k hk hik)) hai hak

omit [DecidableEq ι] in
private theorem differenceFiber_biUnion
    (s : Finset ι) (piece : ι → Finset G) (t : G) :
    differenceFiber (s.biUnion piece) (s.biUnion piece) t =
      s.biUnion fun i => differenceFiberRow s piece i t := by
  ext ab
  constructor
  · intro hab
    rcases Finset.mem_filter.mp hab with ⟨habU, habEq⟩
    rcases Finset.mem_product.mp habU with ⟨ha, hb⟩
    rcases Finset.mem_biUnion.mp ha with ⟨i, hi, hai⟩
    rcases Finset.mem_biUnion.mp hb with ⟨j, hj, hbj⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨i, hi, Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hai, hbj⟩, habEq⟩
  · intro hab
    rcases Finset.mem_biUnion.mp hab with ⟨i, hi, habi⟩
    rcases Finset.mem_biUnion.mp habi with ⟨j, hj, habij⟩
    rcases Finset.mem_filter.mp habij with ⟨habPiece, habEq⟩
    rcases Finset.mem_product.mp habPiece with ⟨hai, hbj⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_biUnion.mpr ⟨i, hi, hai⟩,
          Finset.mem_biUnion.mpr ⟨j, hj, hbj⟩⟩,
        habEq⟩

omit [DecidableEq ι] in
/-- The representation function of a disjoint union is the sum of all
ordered mixed representation functions. -/
theorem differenceRepresentation_biUnion
    (s : Finset ι) (piece : ι → Finset G)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (piece i) (piece j))
    (t : G) :
    differenceRepresentation (s.biUnion piece) (s.biUnion piece) t =
      ∑ i ∈ s, ∑ j ∈ s, differenceRepresentation (piece i) (piece j) t := by
  change (differenceFiber (s.biUnion piece) (s.biUnion piece) t).card = _
  rw [differenceFiber_biUnion]
  rw [Finset.card_biUnion (differenceFiberRow_pairwiseDisjoint s piece hdisj t)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [differenceFiberRow]
  rw [Finset.card_biUnion
    (differenceFiber_pairwiseDisjoint_right s piece hdisj i t)]
  rfl

omit [DecidableEq ι] in
private theorem differenceSet_piece_subset_biUnion
    (s : Finset ι) (piece : ι → Finset G)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    differenceSet (piece i) (piece j) ⊆
      differenceSet (s.biUnion piece) (s.biUnion piece) := by
  intro t ht
  rcases mem_differenceSet.mp ht with ⟨a, hai, b, hbj, hab⟩
  exact mem_differenceSet.mpr
    ⟨a, Finset.mem_biUnion.mpr ⟨i, hi, hai⟩,
      b, Finset.mem_biUnion.mpr ⟨j, hj, hbj⟩, hab⟩

omit [DecidableEq ι] in
private theorem sum_representation_sq_on_biUnion_differenceSet
    (s : Finset ι) (piece : ι → Finset G)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    (∑ t ∈ differenceSet (s.biUnion piece) (s.biUnion piece),
      differenceRepresentation (piece i) (piece j) t ^ 2) =
        differenceEnergy (piece i) (piece j) := by
  unfold differenceEnergy
  apply (Finset.sum_subset
    (differenceSet_piece_subset_biUnion s piece hi hj) ?_).symm
  intro t htU htPiece
  rw [differenceRepresentation_eq_zero_of_not_mem_differenceSet htPiece]
  simp

omit [DecidableEq ι] in
/-- Two nested finite Cauchy--Schwarz inequalities. -/
private theorem sq_double_sum_le_card_sq_mul_double_sum_sq
    (s : Finset ι) (f : ι → ι → ℕ) :
    (∑ i ∈ s, ∑ j ∈ s, f i j) ^ 2 ≤
      s.card ^ 2 * ∑ i ∈ s, ∑ j ∈ s, f i j ^ 2 := by
  calc
    (∑ i ∈ s, ∑ j ∈ s, f i j) ^ 2 ≤
        s.card * ∑ i ∈ s, (∑ j ∈ s, f i j) ^ 2 := by
      exact sq_sum_le_card_mul_sum_sq
    _ ≤ s.card * ∑ i ∈ s, (s.card * ∑ j ∈ s, f i j ^ 2) := by
      exact Nat.mul_le_mul_left _
        (Finset.sum_le_sum fun i hi => sq_sum_le_card_mul_sum_sq)
    _ = s.card ^ 2 * ∑ i ∈ s, ∑ j ∈ s, f i j ^ 2 := by
      rw [← Finset.mul_sum]
      simp [pow_two, mul_assoc]

omit [DecidableEq ι] in
/-- Sum of all ordered mixed energies is controlled by one copy of the
number of pieces times the sum of the self-energies. -/
theorem sum_differenceEnergy_le_card_mul_sum_energy
    (s : Finset ι) (piece : ι → Finset G) :
    (∑ i ∈ s, ∑ j ∈ s, differenceEnergy (piece i) (piece j)) ≤
      s.card * ∑ i ∈ s, energy (piece i) := by
  have hdouble :
      2 * (∑ i ∈ s, ∑ j ∈ s, differenceEnergy (piece i) (piece j)) ≤
        2 * (s.card * ∑ i ∈ s, energy (piece i)) := by
    calc
      2 * (∑ i ∈ s, ∑ j ∈ s,
          differenceEnergy (piece i) (piece j)) =
          ∑ i ∈ s, ∑ j ∈ s,
            2 * differenceEnergy (piece i) (piece j) := by
        simp_rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ s, ∑ j ∈ s,
          (energy (piece i) + energy (piece j)) := by
        exact Finset.sum_le_sum fun i hi =>
          Finset.sum_le_sum fun j hj =>
            two_mul_differenceEnergy_le_energy_add_energy _ _
      _ = 2 * (s.card * ∑ i ∈ s, energy (piece i)) := by
        simp_rw [Finset.sum_add_distrib]
        simp
        rw [← Finset.mul_sum]
        omega
  omega

omit [DecidableEq ι] in
/-- The unconditional finite disjoint-union bound used by the flagged
recurrence.  The exponent `3` comes from two Cauchy--Schwarz factors for the
ordered pair of piece indices and one mixed-energy Young factor. -/
theorem energy_biUnion_le_card_cube_mul_sum_nat
    (s : Finset ι) (piece : ι → Finset G)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (piece i) (piece j)) :
    energy (s.biUnion piece) ≤
      s.card ^ 3 * ∑ i ∈ s, energy (piece i) := by
  let U : Finset G := s.biUnion piece
  let D : Finset G := differenceSet U U
  change (∑ t ∈ D, differenceRepresentation U U t ^ 2) ≤
    s.card ^ 3 * ∑ i ∈ s, energy (piece i)
  calc
    (∑ t ∈ D, differenceRepresentation U U t ^ 2) =
        ∑ t ∈ D,
          (∑ i ∈ s, ∑ j ∈ s,
            differenceRepresentation (piece i) (piece j) t) ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [show U = s.biUnion piece by rfl]
      rw [differenceRepresentation_biUnion s piece hdisj t]
    _ ≤ ∑ t ∈ D, s.card ^ 2 *
          ∑ i ∈ s, ∑ j ∈ s,
            differenceRepresentation (piece i) (piece j) t ^ 2 := by
      exact Finset.sum_le_sum fun t ht =>
        sq_double_sum_le_card_sq_mul_double_sum_sq s fun i j =>
          differenceRepresentation (piece i) (piece j) t
    _ = s.card ^ 2 * ∑ i ∈ s, ∑ j ∈ s, ∑ t ∈ D,
          differenceRepresentation (piece i) (piece j) t ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = s.card ^ 2 * ∑ i ∈ s, ∑ j ∈ s,
          differenceEnergy (piece i) (piece j) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      change (∑ t ∈ differenceSet U U,
        differenceRepresentation (piece i) (piece j) t ^ 2) = _
      simpa only [U] using
        sum_representation_sq_on_biUnion_differenceSet s piece hi hj
    _ ≤ s.card ^ 2 *
        (s.card * ∑ i ∈ s, energy (piece i)) :=
      Nat.mul_le_mul_left _
        (sum_differenceEnergy_le_card_mul_sum_energy s piece)
    _ = s.card ^ 3 * ∑ i ∈ s, energy (piece i) := by
      ring

omit [DecidableEq ι] in
/-- Real-cast form, with the exact right-hand side expected by
`Flagged.Main`. -/
theorem energy_biUnion_le_card_cube_mul_sum_unconditional
    (s : Finset ι) (piece : ι → Finset G)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (piece i) (piece j)) :
    (energy (s.biUnion piece) : ℝ) ≤
      (s.card : ℝ) ^ (3 : ℕ) *
        ∑ i ∈ s, (energy (piece i) : ℝ) := by
  exact_mod_cast energy_biUnion_le_card_cube_mul_sum_nat s piece hdisj

/-- The two-set constant `8`, obtained by specializing the general theorem
to the two Boolean pieces. -/
theorem energy_union_le_eight_nat
    (A B : Finset G) (hdisj : Disjoint A B) :
    energy (A ∪ B) ≤ 8 * (energy A + energy B) := by
  classical
  let piece : Bool → Finset G := fun b => if b then A else B
  have hpair : ∀ i ∈ (Finset.univ : Finset Bool),
      ∀ j ∈ (Finset.univ : Finset Bool), i ≠ j →
        Disjoint (piece i) (piece j) := by
    intro i hi j hj hij
    fin_cases i <;> fin_cases j <;>
      simp_all [piece, hdisj.symm]
  have h := energy_biUnion_le_card_cube_mul_sum_nat
    (Finset.univ : Finset Bool) piece hpair
  convert h using 1 <;> norm_num [piece, add_comm]

/-- Real-cast two-set form for direct use in recurrence inequalities. -/
theorem energy_union_le_eight_unconditional
    (A B : Finset G) (hdisj : Disjoint A B) :
    (energy (A ∪ B) : ℝ) ≤
      8 * ((energy A : ℝ) + (energy B : ℝ)) := by
  exact_mod_cast energy_union_le_eight_nat A B hdisj

end DisjointUnion

end ComplexitySensitiveEnergy
