import ComplexitySensitiveEnergy.Basic
import Mathlib.Combinatorics.Additive.Convolution
import Mathlib.Combinatorics.Additive.Energy

set_option linter.style.header false

/-!
# Difference representation functions and additive energy

The paper uses the difference representation function
`r_{A-B}(t) = #{(a,b) ∈ A × B | a - b = t}` and its squared `ℓ²` norm.
Mathlib's `Finset.addEnergy`, on the other hand, is defined by equal sums.
This file keeps the two definitions separate and proves their equality by an
explicit finite equivalence; the two meanings are never identified merely by
notation.
-/

open scoped BigOperators Pointwise Combinatorics.Additive

namespace ComplexitySensitiveEnergy

variable {G H : Type*}

section DifferenceDefinitions

variable [AddCommGroup G] [DecidableEq G]

/-- The paper's difference representation function `r_{A-B}(t)`. -/
def differenceRepresentation (A B : Finset G) (t : G) : ℕ :=
  ((A ×ˢ B).filter fun ab => ab.1 - ab.2 = t).card

/-- The finite support `A - B` of the difference representation function,
written first as the image of the actual pair map. -/
def differenceSet (A B : Finset G) : Finset G :=
  (A ×ˢ B).image fun ab => ab.1 - ab.2

@[simp]
theorem mem_differenceSet {A B : Finset G} {t : G} :
    t ∈ differenceSet A B ↔ ∃ a ∈ A, ∃ b ∈ B, a - b = t := by
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨⟨a, b⟩, hab, h⟩
    exact ⟨a, (Finset.mem_product.mp hab).1,
      b, (Finset.mem_product.mp hab).2, h⟩
  · rintro ⟨a, ha, b, hb, h⟩
    exact Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, h⟩

/-- The image definition of `differenceSet` agrees with pointwise subtraction. -/
theorem differenceSet_eq_sub (A B : Finset G) :
    differenceSet A B = A - B := by
  ext t
  rw [mem_differenceSet, Finset.mem_sub]

/-- The paper's mixed difference energy `∑_t r_{A-B}(t)^2`. -/
def differenceEnergy (A B : Finset G) : ℕ :=
  ∑ t ∈ differenceSet A B, differenceRepresentation A B t ^ 2

/-- The number of pairs is the sum of all difference representation counts. -/
theorem card_product_eq_sum_differenceRepresentation (A B : Finset G) :
    (A ×ˢ B).card =
      ∑ t ∈ differenceSet A B, differenceRepresentation A B t := by
  simpa [differenceSet, differenceRepresentation] using
    (Finset.card_eq_sum_card_image
      (fun ab : G × G => ab.1 - ab.2) (A ×ˢ B))

theorem differenceRepresentation_eq_zero_of_not_mem_differenceSet
    {A B : Finset G} {t : G} (ht : t ∉ differenceSet A B) :
    differenceRepresentation A B t = 0 := by
  rw [differenceRepresentation, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro ab hab heq
  apply ht
  exact Finset.mem_image.mpr ⟨ab, hab, heq⟩

end DifferenceDefinitions

section EnergyBridge

variable [AddCommGroup G] [DecidableEq G]

/-- A pair representing a difference is equivalent to a pair representing a
sum after negating its second entry. -/
theorem differenceRepresentation_eq_sumRepresentation_neg
    (A B : Finset G) (t : G) :
    differenceRepresentation A B t =
      ((A ×ˢ (-B)).filter fun ab => ab.1 + ab.2 = t).card := by
  unfold differenceRepresentation
  apply Finset.card_equiv ((Equiv.refl G).prodCongr (Equiv.neg G))
  rintro ⟨a, b⟩
  simp [sub_eq_add_neg]

/-- The same bridge through mathlib's named finite-set convolution. -/
theorem differenceRepresentation_eq_addConvolution_neg
    (A B : Finset G) (t : G) :
    differenceRepresentation A B t =
      Finset.addConvolution A (-B) t := by
  rw [differenceRepresentation_eq_sumRepresentation_neg]
  rfl

private abbrev EnergyTuple (G : Type*) := (G × G) × (G × G)

/-- On an equal-sum quadruple with the second set negated, exchange the two
second-set entries and remove their signs. -/
private def negSwapEnergyTupleEquiv :
    EnergyTuple G ≃ EnergyTuple G where
  toFun q := ((q.1.1, -q.2.2), (q.2.1, -q.1.2))
  invFun q := ((q.1.1, -q.2.2), (q.2.1, -q.1.2))
  left_inv q := by
    rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    simp
  right_inv q := by
    rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    simp

/-- Negating one input does not change cross-additive energy.  This is not
definitionally true: the proof explicitly swaps the two occurrences of that
input in every quadruple. -/
theorem addEnergy_neg_right (A B : Finset G) :
    Finset.addEnergy A (-B) = Finset.addEnergy A B := by
  rw [Finset.addEnergy_eq_card_filter, Finset.addEnergy_eq_card_filter]
  apply Finset.card_equiv (negSwapEnergyTupleEquiv (G := G))
  rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
  have hEq : a + b = c + d ↔ a + -d = c + -b := by
    simpa [sub_eq_add_neg] using
      (sub_eq_sub_iff_add_eq_add (a := a) (b := d) (c := c) (d := b)).symm
  simp [negSwapEnergyTupleEquiv, hEq, and_assoc, and_left_comm, and_comm]

/-- First bridge: the paper's difference energy is the equal-sum energy of
`A` and the reflected set `-B`. -/
theorem differenceEnergy_eq_addEnergy_neg (A B : Finset G) :
    differenceEnergy A B = Finset.addEnergy A (-B) := by
  rw [differenceEnergy, differenceSet_eq_sub, sub_eq_add_neg,
    Finset.addEnergy_eq_sum_sq']
  apply Finset.sum_congr rfl
  intro t _
  rw [differenceRepresentation_eq_sumRepresentation_neg]

/-- Main semantic bridge: the paper's squared difference-representation
count equals mathlib's equal-sum additive energy. -/
theorem differenceEnergy_eq_addEnergy (A B : Finset G) :
    differenceEnergy A B = Finset.addEnergy A B :=
  (differenceEnergy_eq_addEnergy_neg A B).trans (addEnergy_neg_right A B)

/-- Self-energy in the paper-facing notation. -/
abbrev energy (A : Finset G) : ℕ := differenceEnergy A A

theorem energy_eq_addEnergy (A : Finset G) :
    energy A = Finset.addEnergy A A :=
  differenceEnergy_eq_addEnergy A A

theorem differenceEnergy_comm (A B : Finset G) :
    differenceEnergy A B = differenceEnergy B A := by
  rw [differenceEnergy_eq_addEnergy, differenceEnergy_eq_addEnergy,
    Finset.addEnergy_comm]

theorem differenceEnergy_mono {A A' B B' : Finset G}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    differenceEnergy A B ≤ differenceEnergy A' B' := by
  simpa only [differenceEnergy_eq_addEnergy] using Finset.addEnergy_mono hA hB

/-- The basic diagonal lower bound. -/
theorem card_mul_card_le_differenceEnergy (A B : Finset G) :
    A.card * B.card ≤ differenceEnergy A B := by
  simpa only [differenceEnergy_eq_addEnergy] using
    (Finset.le_addEnergy (s := A) (t := B))

theorem card_sq_le_energy (A : Finset G) :
    A.card ^ 2 ≤ energy A := by
  simpa only [energy, differenceEnergy_eq_addEnergy] using
    (Finset.le_addEnergy_self (s := A))

/-- Cross-energy is at most `|A|² |B|`: in an equal-sum quadruple, the
first three entries determine the fourth. -/
theorem differenceEnergy_le_card_sq_mul_card (A B : Finset G) :
    differenceEnergy A B ≤ A.card ^ 2 * B.card := by
  rw [differenceEnergy_eq_addEnergy, Finset.addEnergy_eq_card_filter]
  calc
    _ ≤ ((A ×ˢ B) ×ˢ A).card := by
      apply Finset.card_le_card_of_injOn (fun q => (q.1, q.2.1))
      · intro q hq
        have hmem := (Finset.mem_filter.mp hq).1
        exact Finset.mem_product.mpr
          ⟨(Finset.mem_product.mp hmem).1,
            (Finset.mem_product.mp (Finset.mem_product.mp hmem).2).1⟩
      · intro q₁ hq₁ q₂ hq₂ h
        have hsum₁ := (Finset.mem_filter.mp hq₁).2
        have hsum₂ := (Finset.mem_filter.mp hq₂).2
        have hpairs : q₁.1 = q₂.1 :=
          congrArg (fun z : (G × G) × G => z.1) h
        have hfirst : q₁.2.1 = q₂.2.1 :=
          congrArg (fun z : (G × G) × G => z.2) h
        apply Prod.ext hpairs
        apply Prod.ext hfirst
        apply add_left_cancel (a := q₁.2.1)
        calc
          q₁.2.1 + q₁.2.2 = q₁.1.1 + q₁.1.2 := hsum₁.symm
          _ = q₂.1.1 + q₂.1.2 := by rw [hpairs]
          _ = q₂.2.1 + q₂.2.2 := hsum₂
          _ = q₁.2.1 + q₂.2.2 := by rw [hfirst]
    _ = A.card ^ 2 * B.card := by
      simp [pow_two]
      ac_rfl

/-- The paper's universal self-energy upper bound `E(A) ≤ |A|³`. -/
theorem energy_le_card_cubed (A : Finset G) :
    energy A ≤ A.card ^ 3 := by
  simpa [energy, pow_succ, pow_two, mul_assoc] using
    (differenceEnergy_le_card_sq_mul_card A A)

end EnergyBridge

section EnergyMaps

variable [AddCommGroup G] [DecidableEq G]
variable [AddCommGroup H] [DecidableEq H]

/-- Mathlib's equal-sum energy is preserved by an injective additive map. -/
theorem addEnergy_mapFinset (f : G →+ H) (hf : Function.Injective f)
    (A B : Finset G) :
    Finset.addEnergy (mapFinset f hf A) (mapFinset f hf B) =
      Finset.addEnergy A B := by
  rw [Finset.addEnergy_eq_card_filter, Finset.addEnergy_eq_card_filter]
  symm
  apply Finset.card_bij
    (fun q _ => ((f q.1.1, f q.1.2), (f q.2.1, f q.2.2)))
  · intro q hq
    have hmem := Finset.mem_filter.mp hq
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · simpa [mapFinset, additiveEmbedding] using hmem.1
    · simpa using congrArg f hmem.2
  · rintro ⟨⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ _
      ⟨⟨c₁, d₁⟩, ⟨c₂, d₂⟩⟩ _ heq
    simpa only [Prod.mk.injEq, hf.eq_iff] using heq
  · rintro ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩ hq
    have hmem := (Finset.mem_filter.mp hq).1
    have hleft := (Finset.mem_product.mp hmem).1
    have hright := (Finset.mem_product.mp hmem).2
    rcases Finset.mem_map.mp (Finset.mem_product.mp hleft).1 with
      ⟨a₁, ha₁, rfl⟩
    rcases Finset.mem_map.mp (Finset.mem_product.mp hleft).2 with
      ⟨b₁, hb₁, rfl⟩
    rcases Finset.mem_map.mp (Finset.mem_product.mp hright).1 with
      ⟨a₂, ha₂, rfl⟩
    rcases Finset.mem_map.mp (Finset.mem_product.mp hright).2 with
      ⟨b₂, hb₂, rfl⟩
    have hsum : a₁ + b₁ = a₂ + b₂ := by
      apply hf
      simpa [additiveEmbedding] using (Finset.mem_filter.mp hq).2
    refine ⟨((a₁, b₁), (a₂, b₂)), ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨ha₁, hb₁⟩,
          Finset.mem_product.mpr ⟨ha₂, hb₂⟩⟩,
        hsum⟩

/-- The paper's difference energy is preserved by an injective additive map. -/
theorem differenceEnergy_mapFinset (f : G →+ H)
    (hf : Function.Injective f) (A B : Finset G) :
    differenceEnergy (mapFinset f hf A) (mapFinset f hf B) =
      differenceEnergy A B := by
  rw [differenceEnergy_eq_addEnergy, differenceEnergy_eq_addEnergy]
  exact addEnergy_mapFinset f hf A B

/-- Additive equivalences preserve difference energy. -/
theorem differenceEnergy_map_addEquiv (e : G ≃+ H) (A B : Finset G) :
    differenceEnergy
        (mapFinset e.toAddMonoidHom e.injective A)
        (mapFinset e.toAddMonoidHom e.injective B) =
      differenceEnergy A B :=
  differenceEnergy_mapFinset e.toAddMonoidHom e.injective A B

theorem energy_mapFinset (f : G →+ H) (hf : Function.Injective f)
    (A : Finset G) :
    energy (mapFinset f hf A) = energy A :=
  differenceEnergy_mapFinset f hf A A

theorem energy_map_addEquiv (e : G ≃+ H) (A : Finset G) :
    energy (mapFinset e.toAddMonoidHom e.injective A) = energy A :=
  differenceEnergy_map_addEquiv e A A

end EnergyMaps

end ComplexitySensitiveEnergy
