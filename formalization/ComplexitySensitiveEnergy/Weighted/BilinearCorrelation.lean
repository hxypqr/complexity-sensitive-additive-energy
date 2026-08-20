import ComplexitySensitiveEnergy.External.Analysis

/-!
# The finite bilinear correlation identity

This file proves the finite-support identity (2.3) directly from the literal
definitions in `External.Analysis`.  No Fourier transform or Plancherel
statement is used.  The proof first groups `A × B` by its sum, expands the
square, and then applies the explicit bijection

`((a,b),(c,d)) ↦ ((a,c),(d,b))`

between equal-sum and equal-difference quadruples.
-/

open scoped BigOperators Pointwise

namespace ComplexitySensitiveEnergy

noncomputable section

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A support large enough for both autocorrelations.  Terms outside the
individual difference sets vanish; using the union lets the subsequent
Cauchy--Schwarz sums have a common, explicit finite index set. -/
def bilinearCorrelationSupport (A B : Finset G) : Finset G :=
  differenceSet A A ∪ differenceSet B B

/-- The literal squared `ℓ²` sum of the convolution from `External.Analysis`. -/
def convolutionSquareSum (A B : Finset G) (f g : G → ℂ) : ℝ :=
  ∑ z ∈ A + B, ‖External.finiteConvolution A B f g z‖ ^ 2

/-- Equal-sum pairs of pairs from `A × B`. -/
private def convolutionQuadruples (A B : Finset G) :
    Finset ((G × G) × (G × G)) :=
  (((A ×ˢ B) ×ˢ (A ×ˢ B)).filter fun q ↦
    q.1.1 + q.1.2 = q.2.1 + q.2.2)

/-- A pair from `A × A` and a pair from `B × B` representing the same
difference. -/
private def correlationQuadruples (A B : Finset G) :
    Finset ((G × G) × (G × G)) :=
  (((A ×ˢ A) ×ˢ (B ×ˢ B)).filter fun q ↦
    q.1.1 - q.1.2 = q.2.1 - q.2.2)

/-- Finite fiber pairing.  This is the elementary finite-sum mechanism behind
both sides of the correlation identity. -/
private theorem sum_fiber_pairing
    {α β κ : Type*} [DecidableEq κ]
    (S : Finset α) (T : Finset β) (K : Finset κ)
    (keyS : α → κ) (keyT : β → κ) (u : α → ℂ) (v : β → ℂ)
    (hS : ∀ a ∈ S, keyS a ∈ K) :
    (∑ k ∈ K,
        (∑ a ∈ S.filter (fun a ↦ keyS a = k), u a) *
          ∑ b ∈ T.filter (fun b ↦ keyT b = k), v b) =
      ∑ p ∈ (S ×ˢ T).filter (fun p ↦ keyS p.1 = keyT p.2),
        u p.1 * v p.2 := by
  classical
  let P := (S ×ˢ T).filter (fun p ↦ keyS p.1 = keyT p.2)
  have hP : ∀ p ∈ P, keyS p.1 ∈ K := by
    intro p hp
    have hpST := (Finset.mem_filter.mp hp).1
    exact hS p.1 (Finset.mem_product.mp hpST).1
  calc
    (∑ k ∈ K,
        (∑ a ∈ S.filter (fun a ↦ keyS a = k), u a) *
          ∑ b ∈ T.filter (fun b ↦ keyT b = k), v b) =
        ∑ k ∈ K,
          ∑ p ∈ P.filter (fun p ↦ keyS p.1 = k),
            u p.1 * v p.2 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hfiber :
          P.filter (fun p ↦ keyS p.1 = k) =
            S.filter (fun a ↦ keyS a = k) ×ˢ
              T.filter (fun b ↦ keyT b = k) := by
        ext p
        simp only [P, Finset.mem_filter, Finset.mem_product]
        constructor
        · rintro ⟨⟨⟨hpS, hpT⟩, hkeys⟩, hpKey⟩
          exact ⟨⟨hpS, hpKey⟩, hpT, hkeys ▸ hpKey⟩
        · rintro ⟨⟨hpS, hpKeyS⟩, hpT, hpKeyT⟩
          exact ⟨⟨⟨hpS, hpT⟩, hpKeyS.trans hpKeyT.symm⟩, hpKeyS⟩
      rw [Finset.sum_mul_sum, hfiber, Finset.sum_product]
    _ = ∑ p ∈ P, u p.1 * v p.2 :=
      Finset.sum_fiberwise_of_maps_to hP _
    _ = ∑ p ∈ (S ×ˢ T).filter (fun p ↦ keyS p.1 = keyT p.2),
        u p.1 * v p.2 := rfl

/-- The literal convolution is the weighted sum over the sum fiber in
`A × B`.  In particular, its displayed support `A + B` is exact. -/
theorem finiteConvolution_eq_pairFiberSum
    (A B : Finset G) (f g : G → ℂ) (z : G) :
    External.finiteConvolution A B f g z =
      ∑ p ∈ (A ×ˢ B).filter (fun p ↦ p.1 + p.2 = z),
        f p.1 * g p.2 := by
  rw [External.finiteConvolution, ← Finset.sum_filter]
  apply Finset.sum_bij (fun x _ ↦ (x, z - x))
  · intro x hx
    have hx' := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hx'.1, hx'.2⟩, ?_⟩
    simp [sub_eq_add_neg]
  · intro x₁ hx₁ x₂ hx₂ h
    exact congrArg Prod.fst h
  · rintro ⟨a, b⟩ hp
    have hp' := Finset.mem_filter.mp hp
    have hab := Finset.mem_product.mp hp'.1
    have hza : z - a = b := by
      apply sub_eq_iff_eq_add.mpr
      simpa [add_comm] using hp'.2.symm
    refine ⟨a, Finset.mem_filter.mpr ⟨hab.1, hza ▸ hab.2⟩, ?_⟩
    simp [hza]
  · intro x hx
    rfl

/-- The restricted convolution has no support outside the literal sumset. -/
theorem finiteConvolution_eq_zero_of_not_mem_add
    (A B : Finset G) (f g : G → ℂ) {z : G} (hz : z ∉ A + B) :
    External.finiteConvolution A B f g z = 0 := by
  rw [finiteConvolution_eq_pairFiberSum]
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpAB := Finset.mem_product.mp hp'.1
  exact (hz (by
    rw [Finset.mem_add]
    exact ⟨p.1, hpAB.1, p.2, hpAB.2, hp'.2⟩)).elim

/-- The complex coercion of the real convolution square sum is the finite sum
of `h(z) * conjugate(h(z))`. -/
theorem coe_convolutionSquareSum
    (A B : Finset G) (f g : G → ℂ) :
    ((convolutionSquareSum A B f g : ℝ) : ℂ) =
      ∑ z ∈ A + B,
        External.finiteConvolution A B f g z *
          star (External.finiteConvolution A B f g z) := by
  unfold convolutionSquareSum
  push_cast
  apply Finset.sum_congr rfl
  intro z hz
  simpa using (Complex.mul_conj' (External.finiteConvolution A B f g z)).symm

/-- Expansion of the convolution square as a weighted equal-sum quadruple
sum. -/
private theorem convolutionSquareSum_eq_quadrupleSum
    (A B : Finset G) (f g : G → ℂ) :
    ((convolutionSquareSum A B f g : ℝ) : ℂ) =
      ∑ q ∈ convolutionQuadruples A B,
        (f q.1.1 * g q.1.2) * star (f q.2.1 * g q.2.2) := by
  rw [coe_convolutionSquareSum]
  simp_rw [finiteConvolution_eq_pairFiberSum]
  have hmap : ∀ p ∈ A ×ˢ B, p.1 + p.2 ∈ A + B := by
    intro p hp
    have hp' := Finset.mem_product.mp hp
    exact Finset.add_mem_add hp'.1 hp'.2
  simpa [convolutionQuadruples, map_sum] using
    (sum_fiber_pairing (A ×ˢ B) (A ×ˢ B) (A + B)
      (fun p ↦ p.1 + p.2) (fun p ↦ p.1 + p.2)
      (fun p ↦ f p.1 * g p.2) (fun p ↦ star (f p.1 * g p.2))
      hmap)

/-- The involution converting an equal-sum quadruple into two pairs with a
common difference. -/
private def convolutionToCorrelationEquiv :
    ((G × G) × (G × G)) ≃ ((G × G) × (G × G)) where
  toFun q := ((q.1.1, q.2.1), (q.2.2, q.1.2))
  invFun q := ((q.1.1, q.2.2), (q.1.2, q.2.1))
  left_inv q := by rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
  right_inv q := by rcases q with ⟨⟨a, c⟩, ⟨d, b⟩⟩; rfl

/-- Reindex the equal-sum quadruple expansion by common differences. -/
private theorem convolutionQuadrupleSum_eq_correlationQuadrupleSum
    (A B : Finset G) (f g : G → ℂ) :
    (∑ q ∈ convolutionQuadruples A B,
        (f q.1.1 * g q.1.2) * star (f q.2.1 * g q.2.2)) =
      ∑ q ∈ correlationQuadruples A B,
        (f q.1.1 * star (f q.1.2)) *
          (star (g q.2.1) * g q.2.2) := by
  apply Finset.sum_equiv (convolutionToCorrelationEquiv (G := G))
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    constructor
    · intro hq
      have hq' := Finset.mem_filter.mp hq
      have hpairs := Finset.mem_product.mp hq'.1
      have hab := Finset.mem_product.mp hpairs.1
      have hcd := Finset.mem_product.mp hpairs.2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hab.1, hcd.1⟩,
          Finset.mem_product.mpr ⟨hcd.2, hab.2⟩⟩, ?_⟩
      change a - c = d - b
      apply (sub_eq_sub_iff_add_eq_add
        (a := a) (b := c) (c := d) (d := b)).2
      simpa [add_comm] using hq'.2
    · intro hq
      have hq' := Finset.mem_filter.mp hq
      have hpairs := Finset.mem_product.mp hq'.1
      have hac := Finset.mem_product.mp hpairs.1
      have hdb := Finset.mem_product.mp hpairs.2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hac.1, hdb.2⟩,
          Finset.mem_product.mpr ⟨hac.2, hdb.1⟩⟩, ?_⟩
      have hdiff : a - c = d - b := by
        simpa [convolutionToCorrelationEquiv] using hq'.2
      have hsum : a + b = d + c :=
        (sub_eq_sub_iff_add_eq_add
          (a := a) (b := c) (c := d) (d := b)).1 hdiff
      simpa [add_comm] using hsum
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq
    simp [convolutionToCorrelationEquiv]
    ring

/-- Expanding the correlation pairing gives the same common-difference
quadruple sum. -/
private theorem correlationPairing_eq_quadrupleSum
    (A B : Finset G) (f g : G → ℂ) :
    (∑ t ∈ bilinearCorrelationSupport A B,
        weightedDifferenceCorrelation A f t *
          star (weightedDifferenceCorrelation B g t)) =
      ∑ q ∈ correlationQuadruples A B,
        (f q.1.1 * star (f q.1.2)) *
          (star (g q.2.1) * g q.2.2) := by
  have hA : ∀ p ∈ A ×ˢ A,
      p.1 - p.2 ∈ bilinearCorrelationSupport A B := by
    intro p hp
    apply Finset.mem_union_left
    rw [mem_differenceSet]
    have hp' := Finset.mem_product.mp hp
    exact ⟨p.1, hp'.1, p.2, hp'.2, rfl⟩
  simpa [bilinearCorrelationSupport, correlationQuadruples,
    weightedDifferenceCorrelation, map_sum] using
    (sum_fiber_pairing (A ×ˢ A) (B ×ˢ B)
      (bilinearCorrelationSupport A B)
      (fun p ↦ p.1 - p.2) (fun p ↦ p.1 - p.2)
      (fun p ↦ f p.1 * star (f p.2))
      (fun p ↦ star (g p.1) * g p.2) hA)

/-- Paper identity (2.3), as an equality in `ℂ`.  The left side is real and
nonnegative; the complex formulation records at the same time that the
correlation pairing has zero imaginary part. -/
theorem convolutionSquareSum_eq_correlationPairing
    (A B : Finset G) (f g : G → ℂ) :
    ((convolutionSquareSum A B f g : ℝ) : ℂ) =
      ∑ t ∈ bilinearCorrelationSupport A B,
        weightedDifferenceCorrelation A f t *
          star (weightedDifferenceCorrelation B g t) := by
  calc
    ((convolutionSquareSum A B f g : ℝ) : ℂ) =
        ∑ q ∈ convolutionQuadruples A B,
          (f q.1.1 * g q.1.2) * star (f q.2.1 * g q.2.2) :=
      convolutionSquareSum_eq_quadrupleSum A B f g
    _ = ∑ q ∈ correlationQuadruples A B,
          (f q.1.1 * star (f q.1.2)) *
            (star (g q.2.1) * g q.2.2) :=
      convolutionQuadrupleSum_eq_correlationQuadrupleSum A B f g
    _ = ∑ t ∈ bilinearCorrelationSupport A B,
          weightedDifferenceCorrelation A f t *
            star (weightedDifferenceCorrelation B g t) :=
      (correlationPairing_eq_quadrupleSum A B f g).symm

/-! ## Finite Cauchy--Schwarz and the geometric endpoint -/

theorem convolutionSquareSum_nonneg
    (A B : Finset G) (f g : G → ℂ) :
    0 ≤ convolutionSquareSum A B f g := by
  unfold convolutionSquareSum
  positivity

/-- A correlation vanishes off its literal difference support. -/
theorem weightedDifferenceCorrelation_eq_zero_of_not_mem_differenceSet
    (A : Finset G) (f : G → ℂ) {t : G}
    (ht : t ∉ differenceSet A A) :
    weightedDifferenceCorrelation A f t = 0 := by
  unfold weightedDifferenceCorrelation
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpA := Finset.mem_product.mp hp'.1
  exact (ht (mem_differenceSet.mpr
    ⟨p.1, hpA.1, p.2, hpA.2, hp'.2⟩)).elim

/-- Enlarging the summation set to the common bilinear support adds only zero
terms to the first autocorrelation square sum. -/
theorem sum_norm_correlation_sq_bilinearSupport_left
    (A B : Finset G) (f : G → ℂ) :
    (∑ t ∈ bilinearCorrelationSupport A B,
        ‖weightedDifferenceCorrelation A f t‖ ^ 2) =
      weightedCorrelationSquareSum A f := by
  unfold weightedCorrelationSquareSum
  symm
  apply Finset.sum_subset
  · exact Finset.subset_union_left
  · intro t htSupport htA
    rw [weightedDifferenceCorrelation_eq_zero_of_not_mem_differenceSet A f htA]
    simp

/-- The analogous exact support statement for the second autocorrelation. -/
theorem sum_norm_correlation_sq_bilinearSupport_right
    (A B : Finset G) (g : G → ℂ) :
    (∑ t ∈ bilinearCorrelationSupport A B,
        ‖weightedDifferenceCorrelation B g t‖ ^ 2) =
      weightedCorrelationSquareSum B g := by
  unfold weightedCorrelationSquareSum
  symm
  apply Finset.sum_subset
  · exact Finset.subset_union_right
  · intro t htSupport htB
    rw [weightedDifferenceCorrelation_eq_zero_of_not_mem_differenceSet B g htB]
    simp

/-- Triangle inequality for the exact correlation pairing. -/
theorem convolutionSquareSum_le_sum_norm_correlation_mul
    (A B : Finset G) (f g : G → ℂ) :
    convolutionSquareSum A B f g ≤
      ∑ t ∈ bilinearCorrelationSupport A B,
        ‖weightedDifferenceCorrelation A f t‖ *
          ‖weightedDifferenceCorrelation B g t‖ := by
  have hnonneg := convolutionSquareSum_nonneg A B f g
  calc
    convolutionSquareSum A B f g =
        ‖((convolutionSquareSum A B f g : ℝ) : ℂ)‖ := by
      simp [abs_of_nonneg hnonneg]
    _ = ‖∑ t ∈ bilinearCorrelationSupport A B,
          weightedDifferenceCorrelation A f t *
            star (weightedDifferenceCorrelation B g t)‖ := by
      rw [convolutionSquareSum_eq_correlationPairing]
    _ ≤ ∑ t ∈ bilinearCorrelationSupport A B,
          ‖weightedDifferenceCorrelation A f t *
            star (weightedDifferenceCorrelation B g t)‖ :=
      norm_sum_le _ _
    _ = ∑ t ∈ bilinearCorrelationSupport A B,
          ‖weightedDifferenceCorrelation A f t‖ *
            ‖weightedDifferenceCorrelation B g t‖ := by
      apply Finset.sum_congr rfl
      intro t ht
      simp

/-- The finite Cauchy--Schwarz geometric endpoint, at the level of squared
`ℓ²` norm. -/
theorem convolutionSquareSum_le_geometricCorrelation
    (A B : Finset G) (f g : G → ℂ) :
    convolutionSquareSum A B f g ≤
      √(weightedCorrelationSquareSum A f) *
        √(weightedCorrelationSquareSum B g) := by
  calc
    convolutionSquareSum A B f g ≤
        ∑ t ∈ bilinearCorrelationSupport A B,
          ‖weightedDifferenceCorrelation A f t‖ *
            ‖weightedDifferenceCorrelation B g t‖ :=
      convolutionSquareSum_le_sum_norm_correlation_mul A B f g
    _ ≤ √(∑ t ∈ bilinearCorrelationSupport A B,
          ‖weightedDifferenceCorrelation A f t‖ ^ 2) *
        √(∑ t ∈ bilinearCorrelationSupport A B,
          ‖weightedDifferenceCorrelation B g t‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = √(weightedCorrelationSquareSum A f) *
        √(weightedCorrelationSquareSum B g) := by
      rw [sum_norm_correlation_sq_bilinearSupport_left,
        sum_norm_correlation_sq_bilinearSupport_right]

/-- The literal `finiteLpNorm 2` squares to `convolutionSquareSum`; no
normalization factor is present. -/
theorem finiteLpNorm_two_sq_eq_convolutionSquareSum
    (A B : Finset G) (f g : G → ℂ) :
    External.finiteLpNorm 2 (A + B)
        (External.finiteConvolution A B f g) ^ 2 =
      convolutionSquareSum A B f g := by
  have hsum : 0 ≤ ∑ z ∈ A + B,
      ‖External.finiteConvolution A B f g z‖ ^ 2 := by
    positivity
  unfold External.finiteLpNorm convolutionSquareSum
  simp_rw [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hsum]

/-- Literal `finiteLpNorm 2` version of (2.3), as a complex equality. -/
theorem finiteLpNorm_two_sq_eq_correlationPairing
    (A B : Finset G) (f g : G → ℂ) :
    ((External.finiteLpNorm 2 (A + B)
        (External.finiteConvolution A B f g) ^ 2 : ℝ) : ℂ) =
      ∑ t ∈ bilinearCorrelationSupport A B,
        weightedDifferenceCorrelation A f t *
          star (weightedDifferenceCorrelation B g t) := by
  rw [finiteLpNorm_two_sq_eq_convolutionSquareSum]
  exact convolutionSquareSum_eq_correlationPairing A B f g

/-- Real-part formulation of (2.3). -/
theorem finiteLpNorm_two_sq_eq_re_correlationPairing
    (A B : Finset G) (f g : G → ℂ) :
    External.finiteLpNorm 2 (A + B)
        (External.finiteConvolution A B f g) ^ 2 =
      (∑ t ∈ bilinearCorrelationSupport A B,
        weightedDifferenceCorrelation A f t *
          star (weightedDifferenceCorrelation B g t)).re := by
  have h := congrArg Complex.re
    (finiteLpNorm_two_sq_eq_correlationPairing A B f g)
  rw [Complex.ofReal_re] at h
  exact h

/-- Squared-`ℓ²` formulation of the geometric endpoint for the literal
external convolution and norm. -/
theorem finiteLpNorm_two_sq_le_geometricCorrelation
    (A B : Finset G) (f g : G → ℂ) :
    External.finiteLpNorm 2 (A + B)
        (External.finiteConvolution A B f g) ^ 2 ≤
      √(weightedCorrelationSquareSum A f) *
        √(weightedCorrelationSquareSum B g) := by
  rw [finiteLpNorm_two_sq_eq_convolutionSquareSum]
  exact convolutionSquareSum_le_geometricCorrelation A B f g

/-- Unsquared geometric endpoint.  The two nested square roots are precisely
the fourth roots of the two weighted autocorrelation energies. -/
theorem finiteLpNorm_two_le_geometricCorrelation
    (A B : Finset G) (f g : G → ℂ) :
    External.finiteLpNorm 2 (A + B)
        (External.finiteConvolution A B f g) ≤
      √(√(weightedCorrelationSquareSum A f)) *
        √(√(weightedCorrelationSquareSum B g)) := by
  have hsq := finiteLpNorm_two_sq_le_geometricCorrelation A B f g
  calc
    External.finiteLpNorm 2 (A + B)
          (External.finiteConvolution A B f g) ≤
        √(√(weightedCorrelationSquareSum A f) *
          √(weightedCorrelationSquareSum B g)) :=
      Real.le_sqrt_of_sq_le hsq
    _ = √(√(weightedCorrelationSquareSum A f)) *
        √(√(weightedCorrelationSquareSum B g)) := by
      rw [Real.sqrt_mul (Real.sqrt_nonneg _)]

/-- Restricted geometric endpoint for arbitrary complex phases bounded by one
on `A` and `B`.  The passage from indicators to complex coefficients is the
internal phase majorant from `Weighted.Correlation`, not an external input. -/
theorem finiteLpNorm_two_le_energy_fourthRoots
    (A B : Finset G) (f g : G → ℂ)
    (hf : ∀ x ∈ A, ‖f x‖ ≤ 1)
    (hg : ∀ y ∈ B, ‖g y‖ ≤ 1) :
    External.finiteLpNorm 2 (A + B)
        (External.finiteConvolution A B f g) ≤
      √(√(energy A : ℝ)) * √(√(energy B : ℝ)) := by
  have hA : weightedCorrelationSquareSum A f ≤ (energy A : ℝ) := by
    simpa using weightedCorrelationSquareSum_le A f 1 (by norm_num) hf
  have hB : weightedCorrelationSquareSum B g ≤ (energy B : ℝ) := by
    simpa using weightedCorrelationSquareSum_le B g 1 (by norm_num) hg
  refine (finiteLpNorm_two_le_geometricCorrelation A B f g).trans ?_
  exact mul_le_mul
    (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hA))
    (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hB))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end

end ComplexitySensitiveEnergy
