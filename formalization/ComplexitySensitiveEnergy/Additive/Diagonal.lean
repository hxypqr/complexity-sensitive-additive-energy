import ComplexitySensitiveEnergy.Additive.Energy

/-!
# The sharp universal diagonal lower bound

For a finite set `A`, there are two canonical families of equal-sum
quadruples:

* `((a,b),(a,b))`;
* `((a,b),(b,a))`.

Both families have cardinality `|A|²`.  Their intersection is not merely
bounded by `|A|`: it is proved below to be exactly the true diagonal
`((a,a),(a,a))`, of cardinality `|A|`.  Inclusion--exclusion then gives the
sharp universal contribution `2|A|²-|A|` to additive energy.
-/

open scoped Pointwise Combinatorics.Additive

namespace ComplexitySensitiveEnergy

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The quadruple type used by the equal-sum definition of additive energy. -/
abbrev EnergyQuadruple (G : Type*) := (G × G) × (G × G)

/-- All equal-sum quadruples from `A`. -/
def energyWitnesses (A : Finset G) : Finset (EnergyQuadruple G) :=
  ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter fun q ↦
    q.1.1 + q.1.2 = q.2.1 + q.2.2

/-- The first diagonal family `((a,b),(a,b))`. -/
def fixedPairDiagonal (A : Finset G) : Finset (EnergyQuadruple G) :=
  (A ×ˢ A).image fun p ↦ (p, p)

/-- The second diagonal family `((a,b),(b,a))`. -/
def swappedPairDiagonal (A : Finset G) : Finset (EnergyQuadruple G) :=
  (A ×ˢ A).image fun p ↦ (p, (p.2, p.1))

/-- The genuine diagonal, where all four entries coincide. -/
def trueDiagonal (A : Finset G) : Finset (EnergyQuadruple G) :=
  A.image fun a ↦ ((a, a), (a, a))

theorem card_energyWitnesses (A : Finset G) :
    (energyWitnesses A).card = energy A := by
  rw [energy_eq_addEnergy, Finset.addEnergy_eq_card_filter]
  rfl

theorem card_fixedPairDiagonal (A : Finset G) :
    (fixedPairDiagonal A).card = A.card ^ 2 := by
  rw [fixedPairDiagonal,
    Finset.card_image_of_injective _ (fun p q h ↦ congrArg Prod.fst h)]
  simp [pow_two]

theorem card_swappedPairDiagonal (A : Finset G) :
    (swappedPairDiagonal A).card = A.card ^ 2 := by
  rw [swappedPairDiagonal,
    Finset.card_image_of_injective _ (fun p q h ↦ congrArg Prod.fst h)]
  simp [pow_two]

theorem card_trueDiagonal (A : Finset G) :
    (trueDiagonal A).card = A.card := by
  rw [trueDiagonal,
    Finset.card_image_of_injective _ (fun a b h ↦
      congrArg (fun q : EnergyQuadruple G ↦ q.1.1) h)]

/-- The overlap of the two size-`|A|²` diagonal families consists precisely
of quadruples for which all four entries are the same. -/
theorem fixedPairDiagonal_inter_swappedPairDiagonal (A : Finset G) :
    fixedPairDiagonal A ∩ swappedPairDiagonal A = trueDiagonal A := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_inter.mp hq with ⟨hfixed, hswapped⟩
    rcases Finset.mem_image.mp hfixed with ⟨⟨a, b⟩, hab, rfl⟩
    rcases Finset.mem_image.mp hswapped with ⟨⟨c, d⟩, hcd, hEq⟩
    have hca : c = a := congrArg (fun z : EnergyQuadruple G ↦ z.1.1) hEq
    have hcb : c = b := congrArg (fun z : EnergyQuadruple G ↦ z.2.2) hEq
    have habEq : a = b := hca.symm.trans hcb
    refine Finset.mem_image.mpr
      ⟨a, (Finset.mem_product.mp hab).1, ?_⟩
    simp [habEq]
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨a, ha, rfl⟩
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr
        ⟨(a, a), Finset.mem_product.mpr ⟨ha, ha⟩, rfl⟩
    · exact Finset.mem_image.mpr
        ⟨(a, a), Finset.mem_product.mpr ⟨ha, ha⟩, rfl⟩

theorem card_fixedPairDiagonal_inter_swappedPairDiagonal (A : Finset G) :
    (fixedPairDiagonal A ∩ swappedPairDiagonal A).card = A.card := by
  rw [fixedPairDiagonal_inter_swappedPairDiagonal, card_trueDiagonal]

/-- Both diagonal families consist of genuine equal-sum energy witnesses. -/
theorem diagonal_union_subset_energyWitnesses (A : Finset G) :
    fixedPairDiagonal A ∪ swappedPairDiagonal A ⊆ energyWitnesses A := by
  intro q hq
  rcases Finset.mem_union.mp hq with hfixed | hswapped
  · rcases Finset.mem_image.mp hfixed with ⟨⟨a, b⟩, hab, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hab, hab⟩, rfl⟩
  · rcases Finset.mem_image.mp hswapped with ⟨⟨a, b⟩, hab, rfl⟩
    have ha := (Finset.mem_product.mp hab).1
    have hb := (Finset.mem_product.mp hab).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨hab, Finset.mem_product.mpr ⟨hb, ha⟩⟩,
        add_comm a b⟩

/-- Inclusion--exclusion for the two diagonal families. -/
theorem card_diagonal_union (A : Finset G) :
    (fixedPairDiagonal A ∪ swappedPairDiagonal A).card =
      2 * A.card ^ 2 - A.card := by
  rw [Finset.card_union, card_fixedPairDiagonal, card_swappedPairDiagonal,
    card_fixedPairDiagonal_inter_swappedPairDiagonal]
  omega

/-- Every finite subset of an additive commutative group satisfies the sharp
universal diagonal lower bound `2|A|²-|A| ≤ E(A)`. -/
theorem two_mul_card_sq_sub_card_le_energy (A : Finset G) :
    2 * A.card ^ 2 - A.card ≤ energy A := by
  calc
    2 * A.card ^ 2 - A.card =
        (fixedPairDiagonal A ∪ swappedPairDiagonal A).card :=
      (card_diagonal_union A).symm
    _ ≤ (energyWitnesses A).card :=
      Finset.card_le_card (diagonal_union_subset_energyWitnesses A)
    _ = energy A := card_energyWitnesses A

end ComplexitySensitiveEnergy
