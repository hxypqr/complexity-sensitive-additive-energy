import Mathlib

/-!
# Strictly convex interpolation: certificates and the curvature reduction

Lemma 6.1 of the paper starts with finitely many graph points whose adjacent
secant slopes are strictly increasing and constructs a globally strictly
convex interpolant.  This file isolates the parts of that construction that
do not depend on a particular encoding of the finite ordered data.

The central reduction is non-circular.  After choosing a sufficiently small
`δ > 0`, subtract `δ x ^ 2` from the ordinates.  The adjusted adjacent slopes
are still increasing.  Thus any *convex* polygonal interpolant of the adjusted
data becomes a *strictly convex* interpolant after adding `δ x ^ 2` back.

`ConvexInterpolationCertificate` records the exact conclusion needed by the
paper.  The final construction below proves the finite polygonal step: every
adjacent secant line of the adjusted data is below every node, so their finite
upper envelope is a convex interpolant.  Adding the quadratic then gives a
global strictly convex interpolant.  The decreasing-slope case follows by
negating the ordinates.
-/

namespace ComplexitySensitiveEnergy.Turning

open Set

/-- A function together with the two properties required of the convex
interpolant in Lemma 6.1.  The index type is deliberately general; finite
ordered data can use `Fin n`, or a subtype of positions in a list. -/
structure ConvexInterpolationCertificate {ι : Type*} (x y : ι → ℝ) where
  interpolant : ℝ → ℝ
  interpolates : ∀ i, interpolant (x i) = y i
  strictConvex : StrictConvexOn ℝ univ interpolant

/-- Concave counterpart of `ConvexInterpolationCertificate`. -/
structure ConcaveInterpolationCertificate {ι : Type*} (x y : ι → ℝ) where
  interpolant : ℝ → ℝ
  interpolates : ∀ i, interpolant (x i) = y i
  strictConcave : StrictConcaveOn ℝ univ interpolant

/-- Negating a strictly convex interpolant negates all its ordinates and
produces a strictly concave interpolant. -/
def ConvexInterpolationCertificate.neg {ι : Type*} {x y : ι → ℝ}
    (C : ConvexInterpolationCertificate x y) :
    ConcaveInterpolationCertificate x (fun i => -y i) where
  interpolant := -C.interpolant
  interpolates i := by simp [C.interpolates i]
  strictConcave := C.strictConvex.neg

/-- Negating a strictly concave interpolant negates all its ordinates and
produces a strictly convex interpolant. -/
def ConcaveInterpolationCertificate.neg {ι : Type*} {x y : ι → ℝ}
    (C : ConcaveInterpolationCertificate x y) :
    ConvexInterpolationCertificate x (fun i => -y i) where
  interpolant := -C.interpolant
  interpolates i := by simp [C.interpolates i]
  strictConvex := C.strictConcave.neg

/-- The decreasing-slope case of Lemma 6.1 is exactly the increasing-slope
case applied to the negated ordinates. -/
def concaveCertificateOfConvexNeg {ι : Type*} {x y : ι → ℝ}
    (C : ConvexInterpolationCertificate x (fun i => -y i)) :
    ConcaveInterpolationCertificate x y := by
  simpa only [neg_neg] using C.neg

/-- The symmetric conversion, useful when a caller starts with concave data. -/
def convexCertificateOfConcaveNeg {ι : Type*} {x y : ι → ℝ}
    (C : ConcaveInterpolationCertificate x (fun i => -y i)) :
    ConvexInterpolationCertificate x y := by
  simpa only [neg_neg] using C.neg

/-- The midpoint of two real numbers, used to make canonical choices in open
intervals. -/
noncomputable def openMidpoint (a b : ℝ) : ℝ := (a + b) / 2

theorem lt_openMidpoint {a b : ℝ} (h : a < b) :
    a < openMidpoint a b := by
  dsimp [openMidpoint]
  linarith

theorem openMidpoint_lt {a b : ℝ} (h : a < b) :
    openMidpoint a b < b := by
  dsimp [openMidpoint]
  linarith

/-- A finite family of positive gaps admits one positive parameter which is
smaller than every gap after multiplication by the corresponding positive
span.  This is the uniform numerical choice needed for the small-curvature
quadratic perturbation. -/
theorem exists_uniform_small_positive {ι : Type*} (s : Finset ι)
    (gap span : ι → ℝ)
    (hgap : ∀ i ∈ s, 0 < gap i)
    (hspan : ∀ i ∈ s, 0 < span i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ * span i < gap i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨1, zero_lt_one, by simp⟩
  | @insert a s ha ih =>
      have hgapA : 0 < gap a := hgap a (Finset.mem_insert_self a s)
      have hspanA : 0 < span a := hspan a (Finset.mem_insert_self a s)
      obtain ⟨δ, hδ, hδs⟩ := ih
        (fun i hi => hgap i (Finset.mem_insert_of_mem hi))
        (fun i hi => hspan i (Finset.mem_insert_of_mem hi))
      let r : ℝ := gap a / span a
      have hr : 0 < r := by
        dsimp [r]
        exact div_pos hgapA hspanA
      let ε : ℝ := min δ r / 2
      have hmin : 0 < min δ r := lt_min hδ hr
      have hε : 0 < ε := by
        dsimp [ε]
        positivity
      have hεδ : ε < δ := by
        dsimp [ε]
        have hle : min δ r ≤ δ := min_le_left _ _
        linarith
      have hεr : ε < r := by
        dsimp [ε]
        have hle : min δ r ≤ r := min_le_right _ _
        linarith
      refine ⟨ε, hε, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact (lt_div_iff₀ hspanA).mp hεr
      · exact lt_trans
          (mul_lt_mul_of_pos_right hεδ
            (hspan i (Finset.mem_insert_of_mem hi)))
          (hδs i hi)

/-- The secant slope remaining after subtracting the quadratic `δ x^2`.
Indeed `(x₁^2 - x₀^2)/(x₁-x₀) = x₀+x₁` when the endpoints differ. -/
def quadraticAdjustedSlope (δ x₀ x₁ σ : ℝ) : ℝ :=
  σ - δ * (x₀ + x₁)

/-- Subtracting `δ x^2` from two ordinates changes their secant slope by
exactly `δ (x₀+x₁)`.  This is the algebraic bridge between graph data and
`quadraticAdjustedSlope`. -/
theorem secantSlope_sub_quadratic
    {δ x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≠ x₁) :
    ((y₁ - δ * x₁ ^ 2) - (y₀ - δ * x₀ ^ 2)) / (x₁ - x₀) =
      (y₁ - y₀) / (x₁ - x₀) - δ * (x₀ + x₁) := by
  have hden : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx.symm
  field_simp
  ring

/-! ## Supporting lines for finite ordered data -/

/-- The slope between nodes `i` and `i+1` of a sequence of graph points. -/
noncomputable def adjacentSecantSlope (x y : ℕ → ℝ) (i : ℕ) : ℝ :=
  (y (i + 1) - y i) / (x (i + 1) - x i)

/-- The affine line through node `i` with its adjacent secant slope. -/
noncomputable def adjacentSecantLine (x y : ℕ → ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  y i + adjacentSecantSlope x y i * (t - x i)

@[simp]
theorem adjacentSecantLine_left (x y : ℕ → ℝ) (i : ℕ) :
    adjacentSecantLine x y i (x i) = y i := by
  simp [adjacentSecantLine]

theorem adjacentSecantSlope_mul_gap (x y : ℕ → ℝ) {i : ℕ}
    (hx : x i < x (i + 1)) :
    adjacentSecantSlope x y i * (x (i + 1) - x i) =
      y (i + 1) - y i := by
  unfold adjacentSecantSlope
  exact div_mul_cancel₀ _ (sub_ne_zero.mpr hx.ne.symm)

theorem adjacentSecantLine_right (x y : ℕ → ℝ) {i : ℕ}
    (hx : x i < x (i + 1)) :
    adjacentSecantLine x y i (x (i + 1)) = y (i + 1) := by
  unfold adjacentSecantLine
  rw [adjacentSecantSlope_mul_gap x y hx]
  ring

/-- Adjacent strict inequalities imply pairwise strict ordering on a finite
initial segment.  This is the finite form of `strictMono_nat_of_lt_succ`; no
values outside the displayed edge set are constrained. -/
theorem adjacent_lt_implies_lt {σ : ℕ → ℝ} {N i j : ℕ}
    (hadj : ∀ k < N, σ k < σ (k + 1))
    (hij : i < j) (hj : j ≤ N) : σ i < σ j := by
  have hi1j : i + 1 ≤ j := Nat.succ_le_iff.mpr hij
  exact Nat.le_induction (m := i + 1)
    (P := fun j _ => j ≤ N → σ i < σ j)
    (fun hiN => hadj i (by omega))
    (fun j _ ih hjN => (ih (by omega)).trans (hadj j (by omega)))
    j hi1j hj

/-- To the right of an edge, increasing adjacent slopes keep that edge's
affine continuation below every later node. -/
theorem adjacentSecantLine_le_node_of_right
    (x y : ℕ → ℝ) {N i k : ℕ}
    (hx : ∀ r < N, x r < x (r + 1))
    (hslope : ∀ r < N - 1,
      adjacentSecantSlope x y r < adjacentSecantSlope x y (r + 1))
    (hi : i < N) (hik : i ≤ k) (hk : k ≤ N) :
    adjacentSecantLine x y i (x k) ≤ y k := by
  induction k, hik using Nat.le_induction with
  | base => simp
  | succ k hik ih =>
      have hkN : k < N := by omega
      have hihk : adjacentSecantSlope x y i ≤
          adjacentSecantSlope x y k := by
        rcases eq_or_lt_of_le hik with rfl | hik'
        · exact le_rfl
        · exact (adjacent_lt_implies_lt hslope hik' (by omega)).le
      have hgap : 0 ≤ x (k + 1) - x k := sub_nonneg.mpr (hx k hkN).le
      have hmul := mul_le_mul_of_nonneg_right hihk hgap
      have hline : adjacentSecantLine x y i (x (k + 1)) =
          adjacentSecantLine x y i (x k) +
            adjacentSecantSlope x y i * (x (k + 1) - x k) := by
        unfold adjacentSecantLine
        ring
      have hy : y (k + 1) = y k +
          adjacentSecantSlope x y k * (x (k + 1) - x k) := by
        rw [adjacentSecantSlope_mul_gap x y (hx k hkN)]
        ring
      rw [hline, hy]
      exact add_le_add (ih (Nat.le_trans (Nat.le_succ k) hk)) hmul

/-- To the left of an edge, increasing adjacent slopes keep that edge's
affine continuation below every earlier node. -/
theorem adjacentSecantLine_le_node_of_left
    (x y : ℕ → ℝ) {N i k : ℕ}
    (hx : ∀ r < N, x r < x (r + 1))
    (hslope : ∀ r < N - 1,
      adjacentSecantSlope x y r < adjacentSecantSlope x y (r + 1))
    (hi : i < N) (hki : k ≤ i) :
    adjacentSecantLine x y i (x k) ≤ y k := by
  induction hki using Nat.decreasingInduction with
  | self => simp
  | of_succ k hki ih =>
      have hkN : k < N := lt_of_lt_of_le hki hi.le
      have hski : adjacentSecantSlope x y k ≤
          adjacentSecantSlope x y i := by
        exact (adjacent_lt_implies_lt hslope hki (by omega)).le
      have hgap : 0 ≤ x (k + 1) - x k := sub_nonneg.mpr (hx k hkN).le
      have hmul := mul_le_mul_of_nonneg_right hski hgap
      have hline : adjacentSecantLine x y i (x (k + 1)) =
          adjacentSecantLine x y i (x k) +
            adjacentSecantSlope x y i * (x (k + 1) - x k) := by
        unfold adjacentSecantLine
        ring
      have hy : y (k + 1) = y k +
          adjacentSecantSlope x y k * (x (k + 1) - x k) := by
        rw [adjacentSecantSlope_mul_gap x y (hx k hkN)]
        ring
      rw [hline, hy] at ih
      linarith

/-- Every adjacent secant line of finite ordered data with increasing slopes
is a genuine supporting line at every displayed node. -/
theorem adjacentSecantLine_le_node
    (x y : ℕ → ℝ) {N i k : ℕ}
    (hx : ∀ r < N, x r < x (r + 1))
    (hslope : ∀ r < N - 1,
      adjacentSecantSlope x y r < adjacentSecantSlope x y (r + 1))
    (hi : i < N) (hk : k ≤ N) :
    adjacentSecantLine x y i (x k) ≤ y k := by
  rcases le_total i k with hik | hki
  · exact adjacentSecantLine_le_node_of_right x y hx hslope hi hik hk
  · exact adjacentSecantLine_le_node_of_left x y hx hslope hi hki

/-- The exact algebraic condition under which subtracting `δ x^2` preserves
the strict ordering of two consecutive secant slopes. -/
theorem quadraticAdjustedSlope_lt
    {δ x₀ x₁ x₂ σ₀ σ₁ : ℝ}
    (hsmall : δ * (x₂ - x₀) < σ₁ - σ₀) :
    quadraticAdjustedSlope δ x₀ x₁ σ₀ <
      quadraticAdjustedSlope δ x₁ x₂ σ₁ := by
  dsimp [quadraticAdjustedSlope]
  nlinarith

/-- A single positive curvature works simultaneously for every adjacent
triple in a finite family.  This packages the two preceding numerical
lemmas in the form used by the interpolation construction. -/
theorem exists_curvature_preserving_slope_order {ι : Type*} (s : Finset ι)
    (x₀ x₁ x₂ σ₀ σ₁ : ι → ℝ)
    (hspan : ∀ i ∈ s, 0 < x₂ i - x₀ i)
    (hgap : ∀ i ∈ s, 0 < σ₁ i - σ₀ i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s,
      quadraticAdjustedSlope δ (x₀ i) (x₁ i) (σ₀ i) <
        quadraticAdjustedSlope δ (x₁ i) (x₂ i) (σ₁ i) := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_uniform_small_positive s
      (fun i => σ₁ i - σ₀ i) (fun i => x₂ i - x₀ i) hgap hspan
  refine ⟨δ, hδ, ?_⟩
  intro i hi
  exact quadraticAdjustedSlope_lt (hsmall i hi)

/-- Positive scalar multiplication preserves strict convexity for real-valued
functions.  Mathlib has the non-strict scalar lemma; the strict version is
proved directly here because positivity of the scalar is essential. -/
theorem StrictConvexOn.pos_mul {s : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConvexOn ℝ s f) {c : ℝ} (hc : 0 < c) :
    StrictConvexOn ℝ s (fun t => c * f t) := by
  have hconv : ConvexOn ℝ s (fun t => c • f t) := hf.convexOn.smul hc.le
  refine ⟨hconv.1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hstrict := hf.2 hx hy hxy ha hb hab
  have hscaled := mul_lt_mul_of_pos_left hstrict hc
  simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Every positive multiple of `x^2` is globally strictly convex. -/
theorem strictConvexOn_positive_quadratic {δ : ℝ} (hδ : 0 < δ) :
    StrictConvexOn ℝ univ (fun t : ℝ => δ * t ^ 2) := by
  exact StrictConvexOn.pos_mul
    (even_two.strictConvexOn_pow two_ne_zero) hδ

/-- Add a small positive quadratic to a convex function.  This is the
strictness-producing step of the proof of Lemma 6.1. -/
theorem strictConvexOn_quadratic_add {δ : ℝ} (hδ : 0 < δ)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g) :
    StrictConvexOn ℝ univ (fun t => δ * t ^ 2 + g t) := by
  exact (strictConvexOn_positive_quadratic hδ).add_convexOn hg

/-- A real affine function is convex on the whole line. -/
theorem convexOn_affineLine (m b : ℝ) :
    ConvexOn ℝ univ (fun t : ℝ => m * t + b) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a c _ _ hac
  dsimp
  have heq :
      m * (a * x + c * y) + b =
        a * (m * x + b) + c * (m * y + b) := by
    linear_combination -b * hac
  exact heq.le

/-- Pointwise upper envelope of a nonempty finite family of real-valued
functions. -/
noncomputable def finiteUpperEnvelope {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (F : ι → ℝ → ℝ) : ℝ → ℝ :=
  fun t => s.sup' hs (fun i => F i t)

/-- A finite upper envelope of convex functions is convex.  This is proved
directly from the defining convexity inequality, so no analytic or Fourier
input is involved. -/
theorem convexOn_finiteUpperEnvelope {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (F : ι → ℝ → ℝ)
    (hF : ∀ i ∈ s, ConvexOn ℝ univ (F i)) :
    ConvexOn ℝ univ (finiteUpperEnvelope s hs F) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  apply (Finset.sup'_le_iff hs (fun i => F i (a • x + b • y))).2
  intro i hi
  have hix : F i x ≤ finiteUpperEnvelope s hs F x := by
    exact Finset.le_sup' (fun j => F j x) hi
  have hiy : F i y ≤ finiteUpperEnvelope s hs F y := by
    exact Finset.le_sup' (fun j => F j y) hi
  calc
    F i (a • x + b • y) ≤ a • F i x + b • F i y :=
      (hF i hi).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    _ ≤ a • finiteUpperEnvelope s hs F x +
        b • finiteUpperEnvelope s hs F y := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hix ha)
        (mul_le_mul_of_nonneg_left hiy hb)

/-- If every affine function lies below each prescribed ordinate and at least
one is active there, their finite upper envelope interpolates the data. -/
theorem finiteUpperEnvelope_interpolates {ι κ : Type*}
    (s : Finset ι) (hs : s.Nonempty) (F : ι → ℝ → ℝ)
    (x y : κ → ℝ)
    (hbelow : ∀ k, ∀ i ∈ s, F i (x k) ≤ y k)
    (hactive : ∀ k, ∃ i ∈ s, F i (x k) = y k) :
    ∀ k, finiteUpperEnvelope s hs F (x k) = y k := by
  classical
  intro k
  apply le_antisymm
  · exact (Finset.sup'_le_iff hs (fun i => F i (x k))).2 (hbelow k)
  · obtain ⟨i, hi, hieq⟩ := hactive k
    rw [← hieq]
    exact Finset.le_sup' (fun j => F j (x k)) hi

/-- Turning a convex interpolant of the quadratically adjusted ordinates into
the required strict-convex interpolation certificate.  Notice that the input
asks only for ordinary convexity of `g`; it is therefore strictly weaker than
the certificate being constructed. -/
def certificateOfAdjustedConvexInterpolator {ι : Type*} (x y : ι → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (g : ℝ → ℝ)
    (hg : ConvexOn ℝ univ g)
    (hinterp : ∀ i, g (x i) = y i - δ * (x i) ^ 2) :
    ConvexInterpolationCertificate x y where
  interpolant t := δ * t ^ 2 + g t
  interpolates i := by rw [hinterp i]; ring
  strictConvex := strictConvexOn_quadratic_add hδ hg

/-- Completely explicit finite-envelope version of the curvature reduction.
The hypotheses are only the elementary supporting-line inequalities for the
adjusted ordinates.  Taking the maximum of those lines supplies the convex
polygonal interpolant, and the positive quadratic supplies strictness. -/
noncomputable def certificateOfFiniteAffineSupport {ι κ : Type*}
    (s : Finset ι) (hs : s.Nonempty) (m b : ι → ℝ)
    (x y : κ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hbelow : ∀ k, ∀ i ∈ s,
      m i * x k + b i ≤ y k - δ * (x k) ^ 2)
    (hactive : ∀ k, ∃ i ∈ s,
      m i * x k + b i = y k - δ * (x k) ^ 2) :
    ConvexInterpolationCertificate x y := by
  let F : ι → ℝ → ℝ := fun i t => m i * t + b i
  let g : ℝ → ℝ := finiteUpperEnvelope s hs F
  apply certificateOfAdjustedConvexInterpolator x y δ hδ g
  · exact convexOn_finiteUpperEnvelope s hs F
      (fun i _ => convexOn_affineLine (m i) (b i))
  · exact finiteUpperEnvelope_interpolates s hs F x
      (fun k => y k - δ * (x k) ^ 2)
      (fun k i hi => hbelow k i hi)
      (fun k => hactive k)

/-! ## Complete finite ordered-data construction -/

/-- Rewriting an adjusted secant slope in terms of the original slope. -/
theorem adjacentSecantSlope_sub_quadratic
    (x y : ℕ → ℝ) {δ : ℝ} {i : ℕ} (hx : x i < x (i + 1)) :
    adjacentSecantSlope x (fun k => y k - δ * (x k) ^ 2) i =
      quadraticAdjustedSlope δ (x i) (x (i + 1))
        (adjacentSecantSlope x y i) := by
  simpa [adjacentSecantSlope, quadraticAdjustedSlope] using
    (secantSlope_sub_quadratic
      (δ := δ) (x₀ := x i) (x₁ := x (i + 1))
      (y₀ := y i) (y₁ := y (i + 1)) hx.ne)

/-- For `n+2` ordered nodes, one positive quadratic curvature preserves all
`n` strict comparisons between the `n+1` adjacent slopes. -/
theorem exists_curvature_for_finite_ordered_data
    (n : ℕ) (x y : ℕ → ℝ)
    (hx : ∀ i < n + 1, x i < x (i + 1))
    (hslope : ∀ i < n,
      adjacentSecantSlope x y i < adjacentSecantSlope x y (i + 1)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i < n,
      adjacentSecantSlope x (fun k => y k - δ * (x k) ^ 2) i <
        adjacentSecantSlope x (fun k => y k - δ * (x k) ^ 2) (i + 1) := by
  obtain ⟨δ, hδ, horder⟩ :=
    exists_curvature_preserving_slope_order (Finset.range n)
      (fun i => x i) (fun i => x (i + 1)) (fun i => x (i + 2))
      (fun i => adjacentSecantSlope x y i)
      (fun i => adjacentSecantSlope x y (i + 1))
      (by
        intro i hi
        have hi' : i < n := Finset.mem_range.mp hi
        have h₀ := hx i (by omega)
        have h₁ := hx (i + 1) (by omega)
        linarith)
      (by
        intro i hi
        exact sub_pos.mpr (hslope i (Finset.mem_range.mp hi)))
  refine ⟨δ, hδ, ?_⟩
  intro i hi
  have h := horder i (Finset.mem_range.mpr hi)
  rw [adjacentSecantSlope_sub_quadratic x y (hx i (by omega)),
    adjacentSecantSlope_sub_quadratic x y (hx (i + 1) (by omega))]
  exact h

/-- **Finite ordered-data form of Lemma 6.1 (increasing case).**

For `n+2` nodes with strictly increasing abscissae and strictly increasing
adjacent secant slopes, this constructs a globally strictly convex real
function taking exactly the prescribed values at all nodes.  The construction
uses only the supporting-line lemmas above and the explicit positive
quadratic perturbation. -/
noncomputable def convexInterpolationCertificate_of_adjacentSlopes
    (n : ℕ) (x y : ℕ → ℝ)
    (hx : ∀ i < n + 1, x i < x (i + 1))
    (hslope : ∀ i < n,
      adjacentSecantSlope x y i < adjacentSecantSlope x y (i + 1)) :
    ConvexInterpolationCertificate
      (fun i : Fin (n + 2) => x i.1)
      (fun i : Fin (n + 2) => y i.1) := by
  let hcurvature :=
    exists_curvature_for_finite_ordered_data n x y hx hslope
  let δ : ℝ := Classical.choose hcurvature
  have hδ : 0 < δ := (Classical.choose_spec hcurvature).1
  have hadjusted : ∀ i < n,
      adjacentSecantSlope x (fun k => y k - δ * (x k) ^ 2) i <
        adjacentSecantSlope x (fun k => y k - δ * (x k) ^ 2) (i + 1) :=
    (Classical.choose_spec hcurvature).2
  let yδ : ℕ → ℝ := fun k => y k - δ * (x k) ^ 2
  let m : ℕ → ℝ := fun i => adjacentSecantSlope x yδ i
  let b : ℕ → ℝ := fun i => yδ i - m i * x i
  apply certificateOfFiniteAffineSupport (Finset.range (n + 1))
    (by simp) m b
    (fun i : Fin (n + 2) => x i.1)
    (fun i : Fin (n + 2) => y i.1) δ hδ
  · intro k i hi
    have hi' : i < n + 1 := Finset.mem_range.mp hi
    have hk' : k.1 ≤ n + 1 := by omega
    have hsupport := adjacentSecantLine_le_node x yδ
      hx (by simpa [yδ] using hadjusted) hi' hk'
    dsimp [m, b, yδ]
    unfold adjacentSecantLine at hsupport
    linarith
  · intro k
    by_cases hk : k.1 < n + 1
    · refine ⟨k.1, Finset.mem_range.mpr hk, ?_⟩
      simp [m, b, yδ]
    · have hk_eq : k.1 = n + 1 := by omega
      refine ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), ?_⟩
      have hright := adjacentSecantLine_right x yδ (hx n (by omega))
      dsimp [m, b, yδ]
      rw [hk_eq]
      unfold adjacentSecantLine at hright
      linarith

/-- Negating the ordinates negates every adjacent secant slope. -/
theorem adjacentSecantSlope_neg (x y : ℕ → ℝ) (i : ℕ) :
    adjacentSecantSlope x (fun k => -y k) i =
      -adjacentSecantSlope x y i := by
  unfold adjacentSecantSlope
  ring

/-- **Finite ordered-data form of Lemma 6.1 (decreasing case).**
Strictly decreasing adjacent slopes have a globally strictly concave
interpolant, obtained from the increasing case without any new analytic
input. -/
noncomputable def concaveInterpolationCertificate_of_adjacentSlopes
    (n : ℕ) (x y : ℕ → ℝ)
    (hx : ∀ i < n + 1, x i < x (i + 1))
    (hslope : ∀ i < n,
      adjacentSecantSlope x y (i + 1) < adjacentSecantSlope x y i) :
    ConcaveInterpolationCertificate
      (fun i : Fin (n + 2) => x i.1)
      (fun i : Fin (n + 2) => y i.1) := by
  apply concaveCertificateOfConvexNeg
    (convexInterpolationCertificate_of_adjacentSlopes n x
      (fun k => -y k) hx ?_)
  intro i hi
  rw [adjacentSecantSlope_neg, adjacentSecantSlope_neg]
  exact neg_lt_neg (hslope i hi)

end ComplexitySensitiveEnergy.Turning
