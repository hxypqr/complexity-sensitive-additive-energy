import ComplexitySensitiveEnergy.Turning.Definitions

/-!
# Independence of the complementary coordinate

If `m' = c m + d ell`, every adjacent slope changes by the same affine map
`s ↦ c s + d`.  For `c > 0` it preserves increasing/decreasing blocks and
for `c < 0` it swaps them.  The pointwise algebra, including the required
nonzero denominator, is checked here.
-/

namespace ComplexitySensitiveEnergy.Turning

noncomputable def pointSlope
    (ell transverse : LinearMap (RingHom.id ℝ) R2 ℝ)
  (p q : R2) : ℝ :=
  (transverse q - transverse p) / (ell q - ell p)

/-- In the plane, any two complementary coordinates to the same functional
are related by an upper-triangular change of coordinates.  Injectivity of
both coordinate pairs forces the transverse coefficient to be nonzero.

This supplies the linear-algebra step implicit in the paper's assertion
that turning complexity does not depend on the chosen complement. -/
theorem exists_change_of_complement
    (ell transverse transverse' : LinearMap (RingHom.id ℝ) R2 ℝ)
    (hcoordinates : Function.Injective
      (fun x : R2 => (ell x, transverse x)))
    (hcoordinates' : Function.Injective
      (fun x : R2 => (ell x, transverse' x))) :
    ∃ c d : ℝ, c ≠ 0 ∧
      ∀ x, transverse' x = c * transverse x + d * ell x := by
  let coordinates : R2 →ₗ[ℝ] ℝ × ℝ := ell.prod transverse
  have hcoordinatesLinear : Function.Injective coordinates := by
    intro x y hxy
    apply hcoordinates
    simpa only [coordinates, LinearMap.prod_apply, Function.prod_apply] using hxy
  have hdim : Module.finrank ℝ R2 = Module.finrank ℝ (ℝ × ℝ) := by
    simp [R2, Module.finrank_prod]
  let coordinatesEquiv : R2 ≃ₗ[ℝ] ℝ × ℝ :=
    coordinates.linearEquivOfInjective hcoordinatesLinear hdim
  let transformed : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
    transverse'.comp coordinatesEquiv.symm.toLinearMap
  let d : ℝ := transformed (1, 0)
  let c : ℝ := transformed (0, 1)
  have hformula : ∀ y : ℝ × ℝ,
      transformed y = c * y.2 + d * y.1 := by
    rintro ⟨a, b⟩
    have hdecomp : (a, b) = a • (1, 0) + b • (0, 1) := by
      ext <;> simp
    rw [hdecomp, map_add, map_smul, map_smul]
    dsimp only [c, d]
    simp
    ring
  have hchange : ∀ x, transverse' x =
      c * transverse x + d * ell x := by
    intro x
    have hcoordApply : coordinatesEquiv x = (ell x, transverse x) := by
      rfl
    calc
      transverse' x = transformed (coordinatesEquiv x) := by
        simp [transformed]
      _ = c * (coordinatesEquiv x).2 + d * (coordinatesEquiv x).1 :=
        hformula (coordinatesEquiv x)
      _ = c * transverse x + d * ell x := by rw [hcoordApply]
  have hc : c ≠ 0 := by
    intro hc0
    let x : R2 := coordinatesEquiv.symm (0, 1)
    have hellx : ell x = 0 := by
      have hx : coordinatesEquiv x = (0, 1) := by simp [x]
      change (coordinatesEquiv x).1 = 0
      rw [hx]
    have hmx : transverse x = 1 := by
      have hx : coordinatesEquiv x = (0, 1) := by simp [x]
      change (coordinatesEquiv x).2 = 1
      rw [hx]
    have hm'x : transverse' x = 0 := by
      rw [hchange x, hc0, hellx]
      ring
    have hxzero : x = 0 := by
      apply hcoordinates'
      simp [hellx, hm'x]
    have hmxzero : transverse x = 0 := by rw [hxzero]; simp
    linarith
  exact ⟨c, d, hc, hchange⟩

theorem pointSlope_change_of_complement
    (ell transverse transverse' : LinearMap (RingHom.id ℝ) R2 ℝ)
    (c d : ℝ)
    (hchange : ∀ x, transverse' x = c * transverse x + d * ell x)
    {p q : R2} (hell : ell q ≠ ell p) :
    pointSlope ell transverse' p q =
      c * pointSlope ell transverse p q + d := by
  have hden : ell q - ell p ≠ 0 := sub_ne_zero.mpr hell
  rw [pointSlope, pointSlope, hchange q, hchange p]
  field_simp [hden]
  ring

/-- A positive change of complementary coordinate preserves strict slope
order. -/
theorem pointSlope_change_lt_iff_of_pos
    {s t c d : ℝ} (hc : 0 < c) :
    c * s + d < c * t + d ↔ s < t := by
  constructor <;> intro h
  · nlinarith
  · simpa [add_comm] using
      (add_lt_add_right (mul_lt_mul_of_pos_left h hc) d)

/-- A negative change reverses strict slope order, so signed convexity is
unchanged after exchanging “increasing” and “decreasing”. -/
theorem pointSlope_change_lt_iff_of_neg
    {s t c d : ℝ} (hc : c < 0) :
    c * s + d < c * t + d ↔ t < s := by
  constructor <;> intro h
  · nlinarith
  · simpa [add_comm] using
      (add_lt_add_right (mul_lt_mul_of_neg_left h hc) d)

/-- The whole adjacent-slope list is transformed entrywise by
`s ↦ c*s+d`.  Strict `ell`-ordering supplies every nonzero denominator. -/
theorem adjacentSlopes_change_of_complement
    (ell transverse transverse' : LinearMap (RingHom.id ℝ) R2 ℝ)
    (c d : ℝ)
    (hchange : ∀ x, transverse' x = c * transverse x + d * ell x)
    (points : List R2)
    (hell : (points.map ell).Pairwise (fun x y => x < y)) :
    adjacentSlopes ell transverse' points =
      (adjacentSlopes ell transverse points).map (fun s => c * s + d) := by
  induction points with
  | nil => rfl
  | cons p tail ih =>
      cases tail with
      | nil => rfl
      | cons q rest =>
          simp only [List.map_cons, List.pairwise_cons] at hell
          have hpq : ell p < ell q := hell.1 _ (by simp)
          simp only [adjacentSlopes, List.map_cons, List.cons.injEq]
          constructor
          · exact pointSlope_change_of_complement ell transverse transverse'
              c d hchange (ne_of_gt hpq)
          · have htail : ((q :: rest).map ell).Pairwise
                (fun x y => x < y) := by
              simpa only [List.map_cons, List.pairwise_cons] using hell.2
            exact ih htail

private theorem affine_pairwise_signed_iff
    (c d : ℝ) (hc : c ≠ 0) (slopes : List ℝ) :
    ((slopes.map fun s => c * s + d).Pairwise (fun x y => x < y) ∨
      (slopes.map fun s => c * s + d).Pairwise (fun x y => x > y)) ↔
    (slopes.Pairwise (fun x y => x < y) ∨
      slopes.Pairwise (fun x y => x > y)) := by
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · simp only [List.pairwise_map, pointSlope_change_lt_iff_of_neg hcneg]
    tauto
  · simp only [List.pairwise_map, pointSlope_change_lt_iff_of_pos hcpos]

/-- Signed convexity of a block is invariant under every nondegenerate
change `m' = c m + d ell`; a negative `c` swaps its two orientations. -/
theorem isSignedConvexBlock_change_of_complement_iff
    (ell transverse transverse' : LinearMap (RingHom.id ℝ) R2 ℝ)
    (c d : ℝ) (hc : c ≠ 0)
    (hchange : ∀ x, transverse' x = c * transverse x + d * ell x)
    (block : List R2)
    (hell : (block.map ell).Pairwise (fun x y => x < y)) :
    IsSignedConvexBlock ell transverse' block ↔
      IsSignedConvexBlock ell transverse block := by
  unfold IsSignedConvexBlock
  rw [adjacentSlopes_change_of_complement ell transverse transverse'
    c d hchange block hell]
  exact affine_pairwise_signed_iff c d hc _

/-- Partition-level invariance for two ordered configurations with the same
ordered point list and ordering functional. -/
theorem isSignedConvexPartition_change_of_complement_iff
    (P P' : OrderedConfiguration) (c d : ℝ) (hc : c ≠ 0)
    (hpoints : P'.points = P.points) (hellEq : P'.ell = P.ell)
    (hchange : ∀ x,
      P'.transverse x = c * P.transverse x + d * P.ell x)
    (blocks : List (List R2)) :
    IsSignedConvexPartition P' blocks ↔
      IsSignedConvexPartition P blocks := by
  constructor
  · rintro ⟨hflatten', hblocks'⟩
    have hflatten : blocks.flatten = P.points := hflatten'.trans hpoints
    refine ⟨hflatten, ?_⟩
    rw [List.forall_iff_forall_mem] at hblocks' ⊢
    intro block hblock
    rcases hblocks' block hblock with ⟨hne, hconv'⟩
    refine ⟨hne, ?_⟩
    have hsub : List.Sublist (block.map P.ell) (P.points.map P.ell) := by
      have := (List.sublist_flatten_of_mem hblock).map P.ell
      simpa only [hflatten] using this
    have hellBlock : (block.map P.ell).Pairwise (fun x y => x < y) :=
      List.Pairwise.sublist hsub P.ell_strict
    have hconvNormalized :
        IsSignedConvexBlock P.ell P'.transverse block := by
      simpa only [hellEq] using hconv'
    exact (isSignedConvexBlock_change_of_complement_iff
      P.ell P.transverse P'.transverse c d hc hchange block hellBlock).mp
        hconvNormalized
  · rintro ⟨hflatten, hblocks⟩
    refine ⟨hflatten.trans hpoints.symm, ?_⟩
    rw [List.forall_iff_forall_mem] at hblocks ⊢
    intro block hblock
    rcases hblocks block hblock with ⟨hne, hconv⟩
    refine ⟨hne, ?_⟩
    have hsub : List.Sublist (block.map P.ell) (P.points.map P.ell) := by
      have := (List.sublist_flatten_of_mem hblock).map P.ell
      simpa only [hflatten] using this
    have hellBlock : (block.map P.ell).Pairwise (fun x y => x < y) :=
      List.Pairwise.sublist hsub P.ell_strict
    have hconv' := (isSignedConvexBlock_change_of_complement_iff
      P.ell P.transverse P'.transverse c d hc hchange block hellBlock).mpr hconv
    simpa only [hellEq] using hconv'

/-- Every upper bound on the number of signed-convex blocks is invariant. -/
theorem hasSignedConvexPartitionAtMost_change_of_complement_iff
    (P P' : OrderedConfiguration) (c d : ℝ) (hc : c ≠ 0)
    (hpoints : P'.points = P.points) (hellEq : P'.ell = P.ell)
    (hchange : ∀ x,
      P'.transverse x = c * P.transverse x + d * P.ell x)
    (K : ℕ) :
    HasSignedConvexPartitionAtMost P' K ↔
      HasSignedConvexPartitionAtMost P K := by
  constructor
  · rintro ⟨blocks, hblocks, hcard⟩
    exact ⟨blocks,
      (isSignedConvexPartition_change_of_complement_iff
        P P' c d hc hpoints hellEq hchange blocks).mp hblocks,
      hcard⟩
  · rintro ⟨blocks, hblocks, hcard⟩
    exact ⟨blocks,
      (isSignedConvexPartition_change_of_complement_iff
        P P' c d hc hpoints hellEq hchange blocks).mpr hblocks,
      hcard⟩

/-- Hence the exact minimal turning complexity is independent of the chosen
complementary coordinate. -/
theorem hasTurningComplexity_change_of_complement_iff
    (P P' : OrderedConfiguration) (c d : ℝ) (hc : c ≠ 0)
    (hpoints : P'.points = P.points) (hellEq : P'.ell = P.ell)
    (hchange : ∀ x,
      P'.transverse x = c * P.transverse x + d * P.ell x)
    (K : ℕ) :
    HasTurningComplexity P' K ↔ HasTurningComplexity P K := by
  let hAtMost := hasSignedConvexPartitionAtMost_change_of_complement_iff
    P P' c d hc hpoints hellEq hchange
  constructor
  · intro h
    refine ⟨(hAtMost K).mp h.1, ?_⟩
    intro k hk hPk
    exact h.2 k hk ((hAtMost k).mpr hPk)
  · intro h
    refine ⟨(hAtMost K).mpr h.1, ?_⟩
    intro k hk hP'k
    exact h.2 k hk ((hAtMost k).mp hP'k)

/-- The coordinate-change relation for two `OrderedConfiguration`s with the
same ordering functional follows automatically from their coordinate
injectivity fields. -/
theorem orderedConfiguration_exists_change_of_complement
    (P P' : OrderedConfiguration) (hellEq : P'.ell = P.ell) :
    ∃ c d : ℝ, c ≠ 0 ∧ ∀ x,
      P'.transverse x = c * P.transverse x + d * P.ell x := by
  apply exists_change_of_complement P.ell P.transverse P'.transverse
    P.coordinates_injective
  intro x y hxy
  apply P'.coordinates_injective
  simpa only [hellEq] using hxy

/-- Complement-free form of the upper-bound predicate: once the point order
and `ell` agree, no explicit affine relation between the two transverse
coordinates needs to be supplied. -/
theorem hasSignedConvexPartitionAtMost_complements_iff
    (P P' : OrderedConfiguration)
    (hpoints : P'.points = P.points) (hellEq : P'.ell = P.ell)
    (K : ℕ) :
    HasSignedConvexPartitionAtMost P' K ↔
      HasSignedConvexPartitionAtMost P K := by
  obtain ⟨c, d, hc, hchange⟩ :=
    orderedConfiguration_exists_change_of_complement P P' hellEq
  exact hasSignedConvexPartitionAtMost_change_of_complement_iff
    P P' c d hc hpoints hellEq hchange K

/-- Complement-free form of exact minimal turning complexity. -/
theorem hasTurningComplexity_complements_iff
    (P P' : OrderedConfiguration)
    (hpoints : P'.points = P.points) (hellEq : P'.ell = P.ell)
    (K : ℕ) :
    HasTurningComplexity P' K ↔ HasTurningComplexity P K := by
  obtain ⟨c, d, hc, hchange⟩ :=
    orderedConfiguration_exists_change_of_complement P P' hellEq
  exact hasTurningComplexity_change_of_complement_iff
    P P' c d hc hpoints hellEq hchange K

end ComplexitySensitiveEnergy.Turning
