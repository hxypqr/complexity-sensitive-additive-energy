import ComplexitySensitiveEnergy.Additive.Energy
import ComplexitySensitiveEnergy.Algebraic.LocalLambda

/-!
# Exceptional translations at one partition node

This file proves the finite combinatorial content of Lemma 3.1 in the
paper.  The concentration parameter is always the node-local
`energyLocalLambda W A`; no global flag parameter occurs here.
-/

open scoped BigOperators Pointwise

namespace ComplexitySensitiveEnergy

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A fixed difference is determined by its first entry. -/
theorem differenceRepresentation_eq_card_filter_sub_mem
    (A B : Finset G) (t : G) :
    differenceRepresentation A B t =
      (A.filter fun a => a - t ∈ B).card := by
  classical
  unfold differenceRepresentation
  apply Finset.card_bij (fun ab _ => ab.1)
  · intro ab hab
    rcases Finset.mem_filter.mp hab with ⟨habAB, habt⟩
    rcases Finset.mem_product.mp habAB with ⟨ha, hb⟩
    exact Finset.mem_filter.mpr ⟨ha, by simpa [← habt] using hb⟩
  · intro ab₁ hab₁ ab₂ hab₂ hfst
    apply Prod.ext hfst
    have hdiff₁ := (Finset.mem_filter.mp hab₁).2
    have hdiff₂ := (Finset.mem_filter.mp hab₂).2
    calc
      ab₁.2 = ab₁.1 - (ab₁.1 - ab₁.2) := by simp
      _ = ab₁.1 - (ab₂.1 - ab₂.2) := by rw [hdiff₁, hdiff₂]
      _ = ab₂.1 - (ab₂.1 - ab₂.2) := by rw [hfst]
      _ = ab₂.2 := by simp
  · intro a ha
    rcases Finset.mem_filter.mp ha with ⟨haA, hatB⟩
    refine ⟨(a, a - t), ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨haA, hatB⟩, by simp⟩

theorem differenceRepresentation_le_card_left
    (A B : Finset G) (t : G) :
    differenceRepresentation A B t ≤ A.card := by
  rw [differenceRepresentation_eq_card_filter_sub_mem]
  exact Finset.card_filter_le _ _

end ComplexitySensitiveEnergy

namespace ComplexitySensitiveEnergy.PaperVariety

variable {n : ℕ}

/-- Differences from `A` which lie in the literal translation stabilizer. -/
noncomputable def stabilizerDifferenceSet
    (W : PaperVariety n) (A : Finset (RVec n)) : Finset (RVec n) := by
  classical
  exact (differenceSet A A).filter (· ∈ W.stabilizer)

/-- Differences from `A` which are exceptional non-stabilizer translations. -/
noncomputable def badDifferenceSet
    (W : PaperVariety n) (A : Finset (RVec n)) : Finset (RVec n) := by
  classical
  exact (differenceSet A A).filter (· ∈ W.badTranslations)

/-- The two exceptional families together. -/
noncomputable def exceptionalDifferenceSet
    (W : PaperVariety n) (A : Finset (RVec n)) : Finset (RVec n) := by
  classical
  exact (differenceSet A A).filter fun t =>
    t ∈ W.stabilizer ∨ t ∈ W.badTranslations

/-- The stabilizer part of the exceptional energy. -/
noncomputable def stabilizerEnergy
    (W : PaperVariety n) (A : Finset (RVec n)) : ℕ :=
  ∑ t ∈ W.stabilizerDifferenceSet A,
    differenceRepresentation A A t ^ 2

/-- The excess-fiber part of the exceptional energy. -/
noncomputable def badTranslationEnergy
    (W : PaperVariety n) (A : Finset (RVec n)) : ℕ :=
  ∑ t ∈ W.badDifferenceSet A,
    differenceRepresentation A A t ^ 2

/-- Energy of the union of the stabilizer and excess-fiber differences. -/
noncomputable def exceptionalEnergy
    (W : PaperVariety n) (A : Finset (RVec n)) : ℕ :=
  ∑ t ∈ W.exceptionalDifferenceSet A,
    differenceRepresentation A A t ^ 2

private noncomputable def stabilizerPairSet
    (W : PaperVariety n) (A : Finset (RVec n)) :
    Finset (RVec n × RVec n) := by
  classical
  exact (A ×ˢ A).filter fun xy => xy.1 - xy.2 ∈ W.stabilizer

private theorem stabilizerFiber_card
    (W : PaperVariety n) (A : Finset (RVec n)) (y : RVec n)
    (hy : y ∈ A) :
    ((W.stabilizerPairSet A).filter fun xy => xy.2 = y).card =
      W.stabilizerCosetOccupancy A y := by
  classical
  unfold stabilizerPairSet stabilizerCosetOccupancy
  apply Finset.card_bij (fun xy _ => xy.1)
  · intro xy hxy
    simp only [Finset.mem_filter, Finset.mem_product] at hxy ⊢
    rcases hxy with ⟨⟨⟨hx, hy⟩, hstab⟩, hsecond⟩
    subst y
    exact ⟨hx, hstab⟩
  · intro xy₁ hxy₁ xy₂ hxy₂ hfirst
    apply Prod.ext hfirst
    exact (Finset.mem_filter.mp hxy₁).2.trans
      (Finset.mem_filter.mp hxy₂).2.symm
  · intro x hx
    simp only [Finset.mem_filter] at hx
    refine ⟨(x, y), ?_, rfl⟩
    simp [hx.1, hy, hx.2]

/-- The number of ordered pairs in one stabilizer relation is at most
`lambda_W(A) |A|`. -/
private theorem card_stabilizerPairSet_le
    (W : PaperVariety n) (A : Finset (RVec n)) :
    (W.stabilizerPairSet A).card ≤ W.energyLocalLambda A * A.card := by
  classical
  have hsum :
      ∑ y ∈ A,
          ((W.stabilizerPairSet A).filter fun xy => xy.2 = y).card =
        (W.stabilizerPairSet A).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    apply congrArg Finset.card
    ext xy
    simp only [stabilizerPairSet, Finset.mem_filter, Finset.mem_product]
    aesop
  rw [← hsum]
  calc
    (∑ y ∈ A,
        ((W.stabilizerPairSet A).filter fun xy => xy.2 = y).card) =
        ∑ y ∈ A, W.stabilizerCosetOccupancy A y := by
          apply Finset.sum_congr rfl
          intro y hy
          exact W.stabilizerFiber_card A y hy
    _ ≤ ∑ _y ∈ A, W.energyLocalLambda A := by
      apply Finset.sum_le_sum
      intro y hy
      calc
        W.stabilizerCosetOccupancy A y ≤
            W.finiteStabilizerOccupancy A :=
          Finset.le_sup hy
        _ ≤ W.energyLocalLambda A := by
          simp [energyLocalLambda]
    _ = W.energyLocalLambda A * A.card := by
      simp [mul_comm]

private theorem sum_stabilizerRepresentation_eq_card
    (W : PaperVariety n) (A : Finset (RVec n)) :
    (∑ t ∈ W.stabilizerDifferenceSet A,
      differenceRepresentation A A t) =
      (W.stabilizerPairSet A).card := by
  classical
  unfold differenceRepresentation
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  apply congrArg Finset.card
  ext xy
  simp only [stabilizerDifferenceSet, stabilizerPairSet,
    Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨hxy, ⟨_, hstab⟩⟩
    exact ⟨hxy, hstab⟩
  · rintro ⟨hxy, hstab⟩
    exact ⟨hxy,
      ⟨mem_differenceSet.mpr ⟨xy.1, hxy.1, xy.2, hxy.2, rfl⟩, hstab⟩⟩

/-- Stabilizer differences contribute at most the local concentration scale. -/
theorem stabilizerEnergy_le
    (W : PaperVariety n) (A : Finset (RVec n)) :
    W.stabilizerEnergy A ≤ W.energyLocalLambda A * A.card ^ 2 := by
  classical
  calc
    W.stabilizerEnergy A ≤
        ∑ t ∈ W.stabilizerDifferenceSet A,
          A.card * differenceRepresentation A A t := by
      apply Finset.sum_le_sum
      intro t ht
      rw [pow_two]
      exact Nat.mul_le_mul_right _
        (differenceRepresentation_le_card_left A A t)
    _ = A.card * (W.stabilizerPairSet A).card := by
      rw [← Finset.mul_sum, W.sum_stabilizerRepresentation_eq_card A]
    _ ≤ A.card * (W.energyLocalLambda A * A.card) :=
      Nat.mul_le_mul_left _ (W.card_stabilizerPairSet_le A)
    _ = W.energyLocalLambda A * A.card ^ 2 := by
      simp [pow_two]
      ac_rfl

/-- On a bad translation, the representation count is bounded by the
occupancy of the corresponding translate fiber. -/
theorem differenceRepresentation_le_translateFiberOccupancy
    (W : PaperVariety n) (A : Finset (RVec n))
    (hA : ∀ x ∈ A, x ∈ W.realPoints) (t : RVec n) :
    differenceRepresentation A A t ≤ W.translateFiberOccupancy A t := by
  classical
  rw [differenceRepresentation_eq_card_filter_sub_mem]
  unfold translateFiberOccupancy realTranslateFiber
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, hA x hx.1, ?_⟩
  exact hA (x - t) hx.2

private theorem translateFiberOccupancy_le_energyLocalLambda
    (W : PaperVariety n) (A : Finset (RVec n))
    {t : RVec n} (htdiff : t ∈ differenceSet A A)
    (htbad : t ∈ W.badTranslations) :
    W.translateFiberOccupancy A t ≤ W.energyLocalLambda A := by
  classical
  calc
    W.translateFiberOccupancy A t =
        (if t ∈ W.badTranslations then
          W.translateFiberOccupancy A t else 0) := by simp [htbad]
    _ ≤ W.finiteBadFiberOccupancy A :=
      Finset.le_sup (f := fun u =>
        if u ∈ W.badTranslations then
          W.translateFiberOccupancy A u else 0) htdiff
    _ ≤ W.energyLocalLambda A := by simp [energyLocalLambda]

/-- Excess-dimensional translate fibers contribute at most the same local
concentration scale. -/
theorem badTranslationEnergy_le
    (W : PaperVariety n) (A : Finset (RVec n))
    (hA : ∀ x ∈ A, x ∈ W.realPoints) :
    W.badTranslationEnergy A ≤ W.energyLocalLambda A * A.card ^ 2 := by
  classical
  calc
    W.badTranslationEnergy A ≤
        ∑ t ∈ W.badDifferenceSet A,
          W.energyLocalLambda A * differenceRepresentation A A t := by
      apply Finset.sum_le_sum
      intro t ht
      have htdiff : t ∈ differenceSet A A :=
        (Finset.mem_filter.mp ht).1
      have htbad : t ∈ W.badTranslations :=
        (Finset.mem_filter.mp ht).2
      rw [pow_two]
      exact Nat.mul_le_mul_right _ <|
        (W.differenceRepresentation_le_translateFiberOccupancy A hA t).trans
          (W.translateFiberOccupancy_le_energyLocalLambda A htdiff htbad)
    _ = W.energyLocalLambda A *
        ∑ t ∈ W.badDifferenceSet A,
          differenceRepresentation A A t := by
      rw [Finset.mul_sum]
    _ ≤ W.energyLocalLambda A *
        ∑ t ∈ differenceSet A A,
          differenceRepresentation A A t := by
      apply Nat.mul_le_mul_left
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        exact (Finset.mem_filter.mp ht).1
      · intro t ht _
        exact Nat.zero_le _
    _ = W.energyLocalLambda A * A.card ^ 2 := by
      rw [← card_product_eq_sum_differenceRepresentation]
      simp [pow_two]

/-- The union of the two exceptional families is bounded by twice the
node-local scale, exactly as in Lemma 3.1. -/
theorem exceptionalEnergy_le
    (W : PaperVariety n) (A : Finset (RVec n))
    (hA : ∀ x ∈ A, x ∈ W.realPoints) :
    W.exceptionalEnergy A ≤
      2 * W.energyLocalLambda A * A.card ^ 2 := by
  classical
  have hdisj : Disjoint (W.stabilizerDifferenceSet A)
      (W.badDifferenceSet A) := by
    rw [Finset.disjoint_left]
    intro t htstab htbad
    have htstab' : t ∈ W.stabilizer :=
      (Finset.mem_filter.mp htstab).2
    have htbad' : t ∈ W.badTranslations :=
      (Finset.mem_filter.mp htbad).2
    exact htbad'.1 htstab'
  have hunion : W.exceptionalDifferenceSet A =
      W.stabilizerDifferenceSet A ∪ W.badDifferenceSet A := by
    ext t
    simp only [exceptionalDifferenceSet, stabilizerDifferenceSet,
      badDifferenceSet, Finset.mem_filter, Finset.mem_union]
    tauto
  calc
    W.exceptionalEnergy A =
        W.stabilizerEnergy A + W.badTranslationEnergy A := by
      unfold exceptionalEnergy stabilizerEnergy badTranslationEnergy
      rw [hunion, Finset.sum_union hdisj]
    _ ≤ W.energyLocalLambda A * A.card ^ 2 +
        W.energyLocalLambda A * A.card ^ 2 :=
      Nat.add_le_add (W.stabilizerEnergy_le A)
        (W.badTranslationEnergy_le A hA)
    _ = 2 * W.energyLocalLambda A * A.card ^ 2 := by
      simp [two_mul, add_mul]

end ComplexitySensitiveEnergy.PaperVariety
