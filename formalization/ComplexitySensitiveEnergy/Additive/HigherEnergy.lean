import ComplexitySensitiveEnergy.Additive.Energy

set_option linter.style.header false

/-!
# Third additive energy

`J3 A` is defined literally as the number of six-tuples in `A⁶` whose first
three entries and last three entries have the same sum.  No surrogate moment
or informal notation is used in its definition.
-/

open scoped BigOperators

namespace ComplexitySensitiveEnergy

variable {G H : Type*}

/-- A labelled additive triple, represented as `((a₁,a₂),a₃)`. -/
abbrev AdditiveTriple (G : Type*) := (G × G) × G

/-- The Cartesian cube `A³` with labels retained. -/
def tripleProduct (A : Finset G) : Finset (AdditiveTriple G) :=
  (A ×ˢ A) ×ˢ A

/-- Sum of the three entries of a labelled triple. -/
def tripleSum [Add G] (x : AdditiveTriple G) : G :=
  x.1.1 + x.1.2 + x.2

/-- The actual finite set of six-tuple witnesses counted by `J3`. -/
def j3Witnesses [Add G] [DecidableEq G] (A : Finset G) :
    Finset (AdditiveTriple G × AdditiveTriple G) :=
  ((tripleProduct A) ×ˢ (tripleProduct A)).filter fun q =>
    tripleSum q.1 = tripleSum q.2

/-- Third additive energy: the number of labelled solutions
`a₁+a₂+a₃ = a₄+a₅+a₆` in `A⁶`. -/
def J3 [Add G] [DecidableEq G] (A : Finset G) : ℕ :=
  (j3Witnesses A).card

section Bounds

variable [AddCommGroup G] [DecidableEq G]

omit [AddCommGroup G] [DecidableEq G] in
@[simp]
theorem card_tripleProduct (A : Finset G) :
    (tripleProduct A).card = A.card ^ 3 := by
  simp [tripleProduct, pow_succ]

/-- The diagonal embedding `x ↦ (x,x)` gives `|A|³ ≤ J3(A)`. -/
theorem card_cubed_le_J3 (A : Finset G) :
    A.card ^ 3 ≤ J3 A := by
  rw [← card_tripleProduct]
  unfold J3
  apply Finset.card_le_card_of_injOn (fun x => (x, x))
  · intro x hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hx, hx⟩, rfl⟩
  · intro x _ y _ hxy
    exact congrArg Prod.fst hxy

/-- Universal bound `J3(A) ≤ |A|⁵`: five entries determine the sixth. -/
theorem J3_le_card_fifth (A : Finset G) :
    J3 A ≤ A.card ^ 5 := by
  unfold J3
  calc
    (j3Witnesses A).card ≤
        ((tripleProduct A) ×ˢ (A ×ˢ A)).card := by
      apply Finset.card_le_card_of_injOn (fun q => (q.1, q.2.1))
      · intro q hq
        have hmem := (Finset.mem_filter.mp hq).1
        exact Finset.mem_product.mpr
          ⟨(Finset.mem_product.mp hmem).1,
            (Finset.mem_product.mp
              (Finset.mem_product.mp hmem).2).1⟩
      · intro q₁ hq₁ q₂ hq₂ h
        have hsum₁ := (Finset.mem_filter.mp hq₁).2
        have hsum₂ := (Finset.mem_filter.mp hq₂).2
        have hleft : q₁.1 = q₂.1 :=
          congrArg (fun z : AdditiveTriple G × (G × G) => z.1) h
        have hrightPair : q₁.2.1 = q₂.2.1 :=
          congrArg (fun z : AdditiveTriple G × (G × G) => z.2) h
        have hlast : q₁.2.2 = q₂.2.2 := by
          apply add_left_cancel (a := q₁.2.1.1 + q₁.2.1.2)
          calc
            q₁.2.1.1 + q₁.2.1.2 + q₁.2.2 = tripleSum q₁.2 := rfl
            _ = tripleSum q₁.1 := hsum₁.symm
            _ = tripleSum q₂.1 := by rw [hleft]
            _ = tripleSum q₂.2 := hsum₂
            _ = q₂.2.1.1 + q₂.2.1.2 + q₂.2.2 := rfl
            _ = q₁.2.1.1 + q₁.2.1.2 + q₂.2.2 := by rw [hrightPair]
        exact Prod.ext hleft (Prod.ext hrightPair hlast)
    _ = A.card ^ 5 := by
      rw [Finset.card_product, card_tripleProduct,
        Finset.card_product]
      simp [pow_succ]
      ac_rfl

end Bounds

section Maps

variable [AddCommGroup G] [DecidableEq G]
variable [AddCommGroup H] [DecidableEq H]

/-- Coordinatewise action of an additive homomorphism on a triple. -/
def mapTriple (f : G →+ H) (x : AdditiveTriple G) : AdditiveTriple H :=
  ((f x.1.1, f x.1.2), f x.2)

omit [DecidableEq G] [DecidableEq H] in
@[simp]
theorem tripleSum_mapTriple (f : G →+ H) (x : AdditiveTriple G) :
    tripleSum (mapTriple f x) = f (tripleSum x) := by
  simp [mapTriple, tripleSum]

/-- `J3` is preserved by every injective additive map. -/
theorem J3_mapFinset (f : G →+ H) (hf : Function.Injective f)
    (A : Finset G) :
    J3 (mapFinset f hf A) = J3 A := by
  unfold J3
  symm
  apply Finset.card_bij
    (fun q _ => (mapTriple f q.1, mapTriple f q.2))
  · intro q hq
    rcases q with ⟨⟨⟨a₁, a₂⟩, a₃⟩, ⟨⟨b₁, b₂⟩, b₃⟩⟩
    have hmem := Finset.mem_filter.mp hq
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · simpa [tripleProduct, mapTriple, mapFinset, additiveEmbedding] using hmem.1
    · simpa [mapTriple, tripleSum] using congrArg f hmem.2
  · rintro ⟨⟨⟨a₁, a₂⟩, a₃⟩, ⟨⟨b₁, b₂⟩, b₃⟩⟩ _
      ⟨⟨⟨c₁, c₂⟩, c₃⟩, ⟨⟨d₁, d₂⟩, d₃⟩⟩ _ heq
    simpa only [mapTriple, Prod.mk.injEq, hf.eq_iff] using heq
  · rintro ⟨⟨⟨x₁, x₂⟩, x₃⟩, ⟨⟨y₁, y₂⟩, y₃⟩⟩ hq
    have hmem := (Finset.mem_filter.mp hq).1
    have hx := (Finset.mem_product.mp hmem).1
    have hy := (Finset.mem_product.mp hmem).2
    have hxPair := (Finset.mem_product.mp hx).1
    have hyPair := (Finset.mem_product.mp hy).1
    rcases Finset.mem_map.mp (Finset.mem_product.mp hxPair).1 with
      ⟨a₁, ha₁, rfl⟩
    rcases Finset.mem_map.mp (Finset.mem_product.mp hxPair).2 with
      ⟨a₂, ha₂, rfl⟩
    rcases Finset.mem_map.mp (Finset.mem_product.mp hx).2 with
      ⟨a₃, ha₃, rfl⟩
    rcases Finset.mem_map.mp (Finset.mem_product.mp hyPair).1 with
      ⟨b₁, hb₁, rfl⟩
    rcases Finset.mem_map.mp (Finset.mem_product.mp hyPair).2 with
      ⟨b₂, hb₂, rfl⟩
    rcases Finset.mem_map.mp (Finset.mem_product.mp hy).2 with
      ⟨b₃, hb₃, rfl⟩
    have hsum : tripleSum ((a₁, a₂), a₃) =
        tripleSum ((b₁, b₂), b₃) := by
      apply hf
      simpa [additiveEmbedding, tripleSum] using
        (Finset.mem_filter.mp hq).2
    refine ⟨(((a₁, a₂), a₃), ((b₁, b₂), b₃)), ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨ha₁, ha₂⟩, ha₃⟩,
         Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨hb₁, hb₂⟩, hb₃⟩⟩,
       hsum⟩

/-- Additive equivalences preserve `J3`. -/
theorem J3_map_addEquiv (e : G ≃+ H) (A : Finset G) :
    J3 (mapFinset e.toAddMonoidHom e.injective A) = J3 A :=
  J3_mapFinset e.toAddMonoidHom e.injective A

end Maps

end ComplexitySensitiveEnergy
