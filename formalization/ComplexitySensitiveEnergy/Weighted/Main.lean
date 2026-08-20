import Mathlib
import ComplexitySensitiveEnergy.Weighted.Definitions
import ComplexitySensitiveEnergy.Weighted.BilinearCorrelation

/-!
# Verifier for the weighted off-diagonal theorem

This file connects the internally proved finite correlation identity and
phase estimates to the standard bilinear interpolation input.  The endpoint
interfaces below are deliberately one-variable fourth-norm estimates; they
are not aliases for `ConvolutionBound` and cannot assume the desired bilinear
conclusion.
-/

open scoped BigOperators Pointwise

namespace ComplexitySensitiveEnergy

open External

noncomputable section

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A finite function regarded as a vector in a genuine Euclidean space. -/
def finiteL2Vector (A : Finset G) (f : G → ℂ) :
    EuclideanSpace ℂ {x // x ∈ A} :=
  WithLp.toLp 2 (fun x => f x.1)

/-- The literal `finiteLpNorm 2` is the Euclidean norm of
`finiteL2Vector`. -/
theorem finiteLpNorm_two_eq_norm (A : Finset G) (f : G → ℂ) :
    finiteLpNorm 2 A f = ‖finiteL2Vector A f‖ := by
  unfold finiteLpNorm finiteL2Vector
  rw [EuclideanSpace.norm_eq]
  simp_rw [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow]
  congr 1
  simpa only [Finset.univ_eq_attach] using
    (Finset.sum_attach A (fun x => ‖f x‖ ^ 2)).symm

theorem finiteLpNorm_two_eq_sqrt_sum (A : Finset G) (f : G → ℂ) :
    finiteLpNorm 2 A f = √(∑ x ∈ A, ‖f x‖ ^ 2) := by
  unfold finiteLpNorm
  simp_rw [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow]

/-- Minkowski's inequality for a finite sum, obtained by putting the displayed
support into a genuine finite-dimensional Euclidean space. -/
theorem finiteLpNorm_two_finset_sum_le {ι : Type*}
    (A : Finset G) (s : Finset ι) (f : ι → G → ℂ) :
    finiteLpNorm 2 A (∑ i ∈ s, f i) ≤
      ∑ i ∈ s, finiteLpNorm 2 A (f i) := by
  classical
  rw [finiteLpNorm_two_eq_norm]
  have hvec : finiteL2Vector A (∑ i ∈ s, f i) =
      ∑ i ∈ s, finiteL2Vector A (f i) := by
    ext x
    simp [finiteL2Vector]
  rw [hvec]
  calc
    ‖∑ i ∈ s, finiteL2Vector A (f i)‖ ≤
        ∑ i ∈ s, ‖finiteL2Vector A (f i)‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, finiteLpNorm 2 A (f i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (finiteLpNorm_two_eq_norm A (f i)).symm

/-- Change variables `z = x + b` inside the displayed Minkowski summand. -/
theorem sum_translate_indicator (A B : Finset G) {x : G} (hx : x ∈ A)
    (φ : G → ℝ) :
    (∑ z ∈ A + B, if z - x ∈ B then φ (z - x) else 0) =
      ∑ b ∈ B, φ b := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun b _ => x + b)
  · intro b hb
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_add]
      exact ⟨x, hx, b, hb, rfl⟩
    · simpa
  · intro b₁ hb₁ b₂ hb₂ heq
    exact add_left_cancel heq
  · intro z hz
    have hzB : z - x ∈ B := (Finset.mem_filter.mp hz).2
    refine ⟨z - x, hzB, ?_⟩
    simp
  · intro b hb
    simp

/-- The summand indexed by `x` in the left-sided Young decomposition. -/
def leftYoungSummand (B : Finset G) (f g : G → ℂ) (x z : G) : ℂ :=
  if z - x ∈ B then f x * g (z - x) else 0

theorem finiteConvolution_eq_sum_leftYoungSummand
    (A B : Finset G) (f g : G → ℂ) :
    finiteConvolution A B f g = ∑ x ∈ A, leftYoungSummand B f g x := by
  funext z
  simp [finiteConvolution, leftYoungSummand]

/-- Translation invariance and scalar homogeneity of the finite `ℓ²` norm
for one Young summand. -/
theorem finiteLpNorm_two_leftYoungSummand
    (A B : Finset G) (f g : G → ℂ) {x : G} (hx : x ∈ A) :
    finiteLpNorm 2 (A + B) (leftYoungSummand B f g x) =
      ‖f x‖ * finiteLpNorm 2 B g := by
  rw [finiteLpNorm_two_eq_sqrt_sum, finiteLpNorm_two_eq_sqrt_sum]
  have hsum :
      (∑ z ∈ A + B, ‖leftYoungSummand B f g x z‖ ^ 2) =
        ‖f x‖ ^ 2 * ∑ b ∈ B, ‖g b‖ ^ 2 := by
    calc
      (∑ z ∈ A + B, ‖leftYoungSummand B f g x z‖ ^ 2) =
          ∑ z ∈ A + B,
            if z - x ∈ B then (‖f x‖ * ‖g (z - x)‖) ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hzB : z - x ∈ B <;> simp [leftYoungSummand, hzB]
      _ = ∑ b ∈ B, (‖f x‖ * ‖g b‖) ^ 2 :=
        sum_translate_indicator A B hx
          (fun b => (‖f x‖ * ‖g b‖) ^ 2)
      _ = ‖f x‖ ^ 2 * ∑ b ∈ B, ‖g b‖ ^ 2 := by
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
  rw [hsum, Real.sqrt_mul (sq_nonneg ‖f x‖)]
  simp

theorem finiteLpNorm_one_eq_sum (A : Finset G) (f : G → ℂ) :
    finiteLpNorm 1 A f = ∑ x ∈ A, ‖f x‖ := by
  simp [finiteLpNorm]

theorem finiteLpNorm_nonneg (r : ℝ) (A : Finset G) (f : G → ℂ) :
    0 ≤ finiteLpNorm r A f := by
  unfold finiteLpNorm
  exact Real.rpow_nonneg (by positivity) _

/-- The counting-measure Young endpoint `ℓ¹ * ℓ² → ℓ²`, proved for the
literal support-restricted convolution. -/
theorem youngConvolutionBound_one_two (A B : Finset G) :
    ConvolutionBound A B 1 2 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro f g
  rw [finiteConvolution_eq_sum_leftYoungSummand]
  calc
    finiteLpNorm 2 (A + B) (∑ x ∈ A, leftYoungSummand B f g x) ≤
        ∑ x ∈ A, finiteLpNorm 2 (A + B) (leftYoungSummand B f g x) :=
      finiteLpNorm_two_finset_sum_le (A + B) A
        (leftYoungSummand B f g)
    _ = ∑ x ∈ A, ‖f x‖ * finiteLpNorm 2 B g := by
      apply Finset.sum_congr rfl
      intro x hx
      exact finiteLpNorm_two_leftYoungSummand A B f g hx
    _ = 1 * finiteLpNorm 1 A f * finiteLpNorm 2 B g := by
      rw [finiteLpNorm_one_eq_sum]
      simp [Finset.sum_mul]

/-- Commutativity of the literal finite convolution, proved by swapping the
two coordinates in its pair-fiber formula. -/
theorem finiteConvolution_comm (A B : Finset G) (f g : G → ℂ) :
    finiteConvolution A B f g = finiteConvolution B A g f := by
  funext z
  rw [finiteConvolution_eq_pairFiberSum, finiteConvolution_eq_pairFiberSum]
  apply Finset.sum_equiv (Equiv.prodComm G G)
  · intro p
    simp [add_comm, and_comm]
  · intro p hp
    simp [mul_comm]

/-- The symmetric Young endpoint `ℓ² * ℓ¹ → ℓ²`. -/
theorem youngConvolutionBound_two_one (A B : Finset G) :
    ConvolutionBound A B 2 1 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro f g
  have h := (youngConvolutionBound_one_two B A).2.2.2 g f
  rw [← finiteConvolution_comm A B f g] at h
  simpa [add_comm, mul_comm] using h

/-! ## The one-support fourth-norm endpoint -/

/-- The precise one-variable output of the hereditary restricted-type / dyadic
extension.  This is strictly weaker in shape than a bilinear convolution
bound: it only controls one autocorrelation fourth root. -/
def WeightedFourthRootBound (A : Finset G) (D : ℝ) : Prop :=
  0 ≤ D ∧ ∀ f : G → ℂ,
    √(√(weightedCorrelationSquareSum A f)) ≤
      D * finiteLpNorm 2 A f

/-- Fourier-facing formulation of the same one-support endpoint. -/
def FourierL2FourthBound (F : FourierFourthNormInput G)
    (A : Finset G) (D : ℝ) : Prop :=
  0 ≤ D ∧ ∀ f : G → ℂ,
    F.fourthNorm A f ≤ D * finiteLpNorm 2 A f

/-- The abstract Fourier fourth norm is not merely comparable to the
correlation expression: its supplied identity and nonnegativity determine it
exactly as the nested square root. -/
theorem fourierFourthNorm_eq_nestedSqrt
    (F : FourierFourthNormInput G) (A : Finset G) (f : G → ℂ) :
    F.fourthNorm A f = √(√(weightedCorrelationSquareSum A f)) := by
  have hnonneg := F.nonnegative A f
  have hid := F.correlation_identity A f
  have hsqrt : √(weightedCorrelationSquareSum A f) =
      (F.fourthNorm A f) ^ 2 := by
    rw [← hid]
    rw [show (F.fourthNorm A f) ^ 4 =
      ((F.fourthNorm A f) ^ 2) ^ 2 by ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [hsqrt]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]

theorem FourierL2FourthBound.toWeightedFourthRootBound
    (F : FourierFourthNormInput G) (A : Finset G) {D : ℝ}
    (h : FourierL2FourthBound F A D) :
    WeightedFourthRootBound A D := by
  refine ⟨h.1, ?_⟩
  intro f
  rw [← fourierFourthNorm_eq_nestedSqrt F A f]
  exact h.2 f

/-- The internally proved phase-safe dyadic level estimate, expressed through
the standard Fourier fourth-norm realization. -/
theorem fourierFourthNorm_dyadicLevel_fourthPower_le
    (F : FourierFourthNormInput G) (A : Finset G) (f : G → ℂ)
    (profile : ℕ → ℝ) (henergy : HereditaryEnergyBound A profile)
    (j : ℕ) :
    F.fourthNorm (dyadicLevel A f j) (dyadicRestriction A f j) ^ 4 ≤
      dyadicScale j ^ 4 * profile (dyadicLevel A f j).card := by
  rw [F.correlation_identity]
  exact dyadicLevel_weightedCorrelationSquareSum_le_of_hereditary
    A f profile henergy j

/-- Two one-support fourth-root estimates imply the geometric `(2,2)`
endpoint, using the exact finite correlation identity proved internally. -/
theorem convolutionBound_two_two_of_weightedFourthRoot
    (A B : Finset G) {DA DB : ℝ}
    (hA : WeightedFourthRootBound A DA)
    (hB : WeightedFourthRootBound B DB) :
    ConvolutionBound A B 2 2 (DA * DB) := by
  refine ⟨by norm_num, by norm_num, mul_nonneg hA.1 hB.1, ?_⟩
  intro f g
  have hnormA : 0 ≤ finiteLpNorm 2 A f := by
    rw [finiteLpNorm_two_eq_sqrt_sum]
    exact Real.sqrt_nonneg _
  calc
    finiteLpNorm 2 (A + B) (finiteConvolution A B f g) ≤
        √(√(weightedCorrelationSquareSum A f)) *
          √(√(weightedCorrelationSquareSum B g)) :=
      finiteLpNorm_two_le_geometricCorrelation A B f g
    _ ≤ (DA * finiteLpNorm 2 A f) * (DB * finiteLpNorm 2 B g) := by
      exact mul_le_mul (hA.2 f) (hB.2 g)
        (Real.sqrt_nonneg _) (mul_nonneg hA.1 hnormA)
    _ = (DA * DB) * finiteLpNorm 2 A f * finiteLpNorm 2 B g := by
      ring

/-- Fourier-facing version of the preceding endpoint constructor. -/
theorem convolutionBound_two_two_of_fourierL2Fourth
    (F : FourierFourthNormInput G) (A B : Finset G) {DA DB : ℝ}
    (hA : FourierL2FourthBound F A DA)
    (hB : FourierL2FourthBound F B DB) :
    ConvolutionBound A B 2 2 (DA * DB) :=
  convolutionBound_two_two_of_weightedFourthRoot A B
    (hA.toWeightedFourthRootBound F A)
    (hB.toWeightedFourthRootBound F B)

/-! ## Bilinear interpolation verifier -/

/-- In the interpolation triangle, the internally proved Young vertices, the
geometric endpoint, and the external *standard* bilinear interpolation theorem
give exactly the paper's closed exponent `offDiagonalTheta`.

The hypotheses `WeightedFourthRootBound` are one-support outputs of the
phase-safe dyadic extension.  In particular this theorem does not assume a
`ConvolutionBound` at `(2,2)` or at the requested `(p,q)`. -/
theorem alphaTwo_interior_of_weightedFourthRoot
    {H : Type} [AddCommGroup H] [DecidableEq H]
    (hinterp : AlphaTwoBilinearInterpolationStatement)
    (A B : Finset H) {DA DB p q : ℝ}
    (hA : WeightedFourthRootBound A DA)
    (hB : WeightedFourthRootBound B DB)
    (hx : 1 / 2 ≤ 1 / p) (hy : 1 / 2 ≤ 1 / q)
    (hs : 1 / p + 1 / q ≤ 3 / 2) :
    ConvolutionBound A B p q
      ((DA * DB) ^ offDiagonalTheta (1 / p) (1 / q)) := by
  let theta₀ : ℝ := 3 - 2 * (1 / p + 1 / q)
  let theta₁ : ℝ := 2 * (1 / p) - 1
  let theta₂ : ℝ := 2 * (1 / q) - 1
  have hcoords := alphaTwo_barycentric_coordinates hx hy hs
  have htheta₀ : 0 ≤ theta₀ := by
    simpa [theta₀] using hcoords.1
  have htheta₁ : 0 ≤ theta₁ := by
    simpa [theta₁] using hcoords.2.1
  have htheta₂ : 0 ≤ theta₂ := by
    simpa [theta₂] using hcoords.2.2.1
  have hsum : theta₀ + theta₁ + theta₂ = 1 := by
    simpa [theta₀, theta₁, theta₂] using hcoords.2.2.2.1
  have hpcoord :
      1 / p = theta₀ / 2 + theta₁ + theta₂ / 2 := by
    simpa [theta₀, theta₁, theta₂] using hcoords.2.2.2.2.1
  have hqcoord :
      1 / q = theta₀ / 2 + theta₁ / 2 + theta₂ := by
    simpa [theta₀, theta₁, theta₂] using hcoords.2.2.2.2.2
  have hout := hinterp H inferInstance inferInstance A B (DA * DB) 1 1
    (convolutionBound_two_two_of_weightedFourthRoot A B hA hB)
    (youngConvolutionBound_one_two A B)
    (youngConvolutionBound_two_one A B)
    theta₀ theta₁ theta₂ p q htheta₀ htheta₁ htheta₂ hsum hpcoord hqcoord
  rw [offDiagonalTheta_eq_interior hs]
  simpa [theta₀] using hout

/-- Fourier-facing form of the interpolation verifier. -/
theorem alphaTwo_interior_of_fourierL2Fourth
    {H : Type} [AddCommGroup H] [DecidableEq H]
    (hinterp : AlphaTwoBilinearInterpolationStatement)
    (F : FourierFourthNormInput H) (A B : Finset H)
    {DA DB p q : ℝ}
    (hA : FourierL2FourthBound F A DA)
    (hB : FourierL2FourthBound F B DB)
    (hx : 1 / 2 ≤ 1 / p) (hy : 1 / 2 ≤ 1 / q)
    (hs : 1 / p + 1 / q ≤ 3 / 2) :
    ConvolutionBound A B p q
      ((DA * DB) ^ offDiagonalTheta (1 / p) (1 / q)) :=
  alphaTwo_interior_of_weightedFourthRoot hinterp A B
    (hA.toWeightedFourthRootBound F A)
    (hB.toWeightedFourthRootBound F B) hx hy hs

/-! The part of the alpha-two region above the critical edge uses only the
elementary antitonicity of finite counting-measure `ℓᵖ` norms.  We expose its
exact statement separately, so the interpolation wrapper cannot silently
assume any convolution estimate. -/

def FiniteLpAntitoneStatement : Prop :=
  ∀ (H : Type) (_ : AddCommGroup H) (_ : DecidableEq H)
    (A : Finset H) (f : H → ℂ) (p q : ℝ),
    1 ≤ p → p ≤ q → finiteLpNorm q A f ≤ finiteLpNorm p A f

/-- Antitonicity of unnormalized finite counting-measure `ℓᵖ` norms.  The
proof is a finite induction using the two-coordinate power-mean inequality,
so this is internal rather than an analytic black box. -/
theorem finiteLpNorm_antitone (A : Finset G) (f : G → ℂ)
    {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    finiteLpNorm q A f ≤ finiteLpNorm p A f := by
  classical
  have hp_pos : 0 < p := zero_lt_one.trans_le hp
  have hq_pos : 0 < q := hp_pos.trans_le hpq
  induction A using Finset.induction_on with
  | empty =>
      simp [finiteLpNorm, one_div, Real.zero_rpow,
        hp_pos.ne', hq_pos.ne']
  | @insert x A hx ih =>
      let Sp : ℝ := ∑ a ∈ A, ‖f a‖ ^ p
      let Sq : ℝ := ∑ a ∈ A, ‖f a‖ ^ q
      have hSp : 0 ≤ Sp := by
        dsimp [Sp]
        positivity
      have hSq : 0 ≤ Sq := by
        dsimp [Sq]
        positivity
      have hpowp : (finiteLpNorm p A f) ^ p = Sp := by
        dsimp [Sp]
        unfold finiteLpNorm
        rw [one_div]
        rw [Real.rpow_inv_rpow (by positivity) hp_pos.ne']
      have hpowq : (finiteLpNorm q A f) ^ q = Sq := by
        dsimp [Sq]
        unfold finiteLpNorm
        rw [one_div]
        rw [Real.rpow_inv_rpow (by positivity) hq_pos.ne']
      rw [finiteLpNorm, finiteLpNorm]
      simp only [Finset.sum_insert hx]
      change (‖f x‖ ^ q + Sq) ^ (1 / q) ≤
        (‖f x‖ ^ p + Sp) ^ (1 / p)
      rw [← hpowq, ← hpowp]
      calc
        (‖f x‖ ^ q + (finiteLpNorm q A f) ^ q) ^ (1 / q) ≤
            (‖f x‖ ^ p + (finiteLpNorm q A f) ^ p) ^ (1 / p) :=
          Real.rpow_add_rpow_le (norm_nonneg _)
            (finiteLpNorm_nonneg q A f) hp_pos hpq
        _ ≤ (‖f x‖ ^ p + (finiteLpNorm p A f) ^ p) ^ (1 / p) := by
          apply Real.rpow_le_rpow
          · exact add_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
              (Real.rpow_nonneg (finiteLpNorm_nonneg q A f) _)
          · exact add_le_add_right
              (Real.rpow_le_rpow (finiteLpNorm_nonneg q A f) ih
                (zero_le_one.trans hp)) _
          · exact div_nonneg zero_le_one hp_pos.le

theorem finiteLpAntitone : FiniteLpAntitoneStatement := by
  intro H _ _ A f p q hp hpq
  exact finiteLpNorm_antitone A f hp hpq

/-- A convolution estimate transfers toward smaller input exponents by
finite-`ℓᵖ` antitonicity. -/
theorem convolutionBound_mono_inputExponents
    {H : Type} [AddCommGroup H] [DecidableEq H]
    (hlp : FiniteLpAntitoneStatement)
    (A B : Finset H) {p q p₀ q₀ C : ℝ}
    (hbound : ConvolutionBound A B p₀ q₀ C)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpp₀ : p ≤ p₀) (hqq₀ : q ≤ q₀) :
    ConvolutionBound A B p q C := by
  refine ⟨hp, hq, hbound.2.2.1, ?_⟩
  intro f g
  have hf := hlp H inferInstance inferInstance A f p p₀ hp hpp₀
  have hg := hlp H inferInstance inferInstance B g q q₀ hq hqq₀
  have hC : 0 ≤ C := hbound.2.2.1
  calc
    finiteLpNorm 2 (A + B) (finiteConvolution A B f g) ≤
        C * finiteLpNorm p₀ A f * finiteLpNorm q₀ B g :=
      hbound.2.2.2 f g
    _ ≤ C * finiteLpNorm p A f * finiteLpNorm q₀ B g := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hf hC)
        (finiteLpNorm_nonneg q₀ B g)
    _ ≤ C * finiteLpNorm p A f * finiteLpNorm q B g := by
      exact mul_le_mul_of_nonneg_left hg
        (mul_nonneg hC (finiteLpNorm_nonneg p A f))

/-- Above the critical edge the complexity exponent is zero.  The estimate is
obtained at the boundary and transferred by finite-norm antitonicity. -/
theorem alphaTwo_aboveEdge_of_weightedFourthRoot
    {H : Type} [AddCommGroup H] [DecidableEq H]
    (hinterp : AlphaTwoBilinearInterpolationStatement)
    (hlp : FiniteLpAntitoneStatement)
    (A B : Finset H) {DA DB p q : ℝ}
    (hA : WeightedFourthRootBound A DA)
    (hB : WeightedFourthRootBound B DB)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hs : 3 / 2 ≤ 1 / p + 1 / q) :
    ConvolutionBound A B p q 1 := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp
  have hq_pos : 0 < q := zero_lt_one.trans_le hq
  have hx : 1 / 2 ≤ 1 / p :=
    (one_div_le_one_div (by norm_num) hp_pos).2 hp2
  have hy : 1 / 2 ≤ 1 / q :=
    (one_div_le_one_div (by norm_num) hq_pos).2 hq2
  have hy1 : 1 / q ≤ 1 := by
    simpa using (one_div_le_one_div hq_pos zero_lt_one).2 hq
  let x₀ : ℝ := 3 / 2 - 1 / q
  let p₀ : ℝ := 1 / x₀
  have hboundary := alphaTwo_boundary_point_below hy hy1 hs
  have hx₀half : 1 / 2 ≤ x₀ := by simpa [x₀] using hboundary.1
  have hx₀one : x₀ ≤ 1 := by simpa [x₀] using hboundary.2.1
  have hx₀x : x₀ ≤ 1 / p := by simpa [x₀] using hboundary.2.2.1
  have hx₀pos : 0 < x₀ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hx₀half
  have hp₀recip : 1 / p₀ = x₀ := by
    dsimp [p₀]
    field_simp
  have hp₀ : 1 ≤ p₀ := by
    dsimp [p₀]
    exact (le_div_iff₀ hx₀pos).2 (by simpa using hx₀one)
  have hp₀2 : p₀ ≤ 2 := by
    dsimp [p₀]
    rw [div_le_iff₀ hx₀pos]
    linarith
  have hpp₀ : p ≤ p₀ := by
    apply (one_div_le_one_div (by positivity [hp₀]) hp_pos).1
    rw [hp₀recip]
    exact hx₀x
  have hcritical : 1 / p₀ + 1 / q ≤ 3 / 2 := by
    rw [hp₀recip]
    dsimp [x₀]
    linarith
  have hboundaryBound := alphaTwo_interior_of_weightedFourthRoot
    hinterp A B hA hB (by simpa [hp₀recip] using hx₀half) hy hcritical
  have hboundaryTheta : offDiagonalTheta (1 / p₀) (1 / q) = 0 := by
    apply offDiagonalTheta_eq_zero
    rw [hp₀recip]
    dsimp [x₀]
    linarith
  have hboundaryOne : ConvolutionBound A B p₀ q 1 := by
    rw [hboundaryTheta] at hboundaryBound
    simpa using hboundaryBound
  exact convolutionBound_mono_inputExponents hlp A B hboundaryOne
    hp hq hpp₀ le_rfl

/-- Complete alpha-two polygon wrapper.  It uses complex interpolation below
the critical edge and finite norm antitonicity above it. -/
theorem alphaTwo_of_weightedFourthRoot
    {H : Type} [AddCommGroup H] [DecidableEq H]
    (hinterp : AlphaTwoBilinearInterpolationStatement)
    (hlp : FiniteLpAntitoneStatement)
    (A B : Finset H) {DA DB p q : ℝ}
    (hA : WeightedFourthRootBound A DA)
    (hB : WeightedFourthRootBound B DB)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hq : 1 ≤ q) (hq2 : q ≤ 2) :
    ConvolutionBound A B p q
      ((DA * DB) ^ offDiagonalTheta (1 / p) (1 / q)) := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp
  have hq_pos : 0 < q := zero_lt_one.trans_le hq
  have hx : 1 / 2 ≤ 1 / p :=
    (one_div_le_one_div (by norm_num) hp_pos).2 hp2
  have hy : 1 / 2 ≤ 1 / q :=
    (one_div_le_one_div (by norm_num) hq_pos).2 hq2
  by_cases hs : 1 / p + 1 / q ≤ 3 / 2
  · exact alphaTwo_interior_of_weightedFourthRoot
      hinterp A B hA hB hx hy hs
  · have hs' : 3 / 2 ≤ 1 / p + 1 / q := le_of_not_ge hs
    have habove := alphaTwo_aboveEdge_of_weightedFourthRoot
      hinterp hlp A B hA hB hp hp2 hq hq2 hs'
    have htheta : offDiagonalTheta (1 / p) (1 / q) = 0 :=
      offDiagonalTheta_eq_zero hs'
    rw [htheta]
    simpa using habove

/-- Fourier-facing complete polygon wrapper. -/
theorem alphaTwo_of_fourierL2Fourth
    {H : Type} [AddCommGroup H] [DecidableEq H]
    (hinterp : AlphaTwoBilinearInterpolationStatement)
    (hlp : FiniteLpAntitoneStatement)
    (F : FourierFourthNormInput H) (A B : Finset H)
    {DA DB p q : ℝ}
    (hA : FourierL2FourthBound F A DA)
    (hB : FourierL2FourthBound F B DB)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hq : 1 ≤ q) (hq2 : q ≤ 2) :
    ConvolutionBound A B p q
      ((DA * DB) ^ offDiagonalTheta (1 / p) (1 / q)) :=
  alphaTwo_of_weightedFourthRoot hinterp hlp A B
    (hA.toWeightedFourthRootBound F A)
    (hB.toWeightedFourthRootBound F B) hp hp2 hq hq2

/-- Fourier-facing complete polygon wrapper with the finite-counting-measure
`ℓᵖ` monotonicity discharged internally.  Thus the only analytic external
input in this wrapper is the complex bilinear interpolation statement. -/
theorem alphaTwo_of_fourierL2Fourth_internal
    {H : Type} [AddCommGroup H] [DecidableEq H]
    (hinterp : AlphaTwoBilinearInterpolationStatement)
    (F : FourierFourthNormInput H) (A B : Finset H)
    {DA DB p q : ℝ}
    (hA : FourierL2FourthBound F A DA)
    (hB : FourierL2FourthBound F B DB)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hq : 1 ≤ q) (hq2 : q ≤ 2) :
    ConvolutionBound A B p q
      ((DA * DB) ^ offDiagonalTheta (1 / p) (1 / q)) :=
  alphaTwo_of_fourierL2Fourth hinterp finiteLpAntitone F A B
    hA hB hp hp2 hq hq2

/-- Increasing a nonnegative displayed constant preserves a convolution
bound. -/
theorem convolutionBound_mono_constant
    (A B : Finset G) {p q C D : ℝ}
    (h : ConvolutionBound A B p q C)
    (hCD : C ≤ D) (hD : 0 ≤ D) :
    ConvolutionBound A B p q D := by
  refine ⟨h.1, h.2.1, hD, ?_⟩
  intro f g
  calc
    finiteLpNorm 2 (A + B) (finiteConvolution A B f g) ≤
        C * finiteLpNorm p A f * finiteLpNorm q B g := h.2.2.2 f g
    _ ≤ D * finiteLpNorm p A f * finiteLpNorm q B g := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCD (finiteLpNorm_nonneg p A f))
        (finiteLpNorm_nonneg q B g)

/-- A convolution with an empty left support vanishes identically. -/
theorem convolutionBound_empty_left
    (B : Finset G) {p q C : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hC : 0 ≤ C) :
    ConvolutionBound (∅ : Finset G) B p q C := by
  refine ⟨hp, hq, hC, ?_⟩
  intro f g
  simp [finiteConvolution, finiteLpNorm]
  exact mul_nonneg
    (mul_nonneg hC (Real.rpow_nonneg (le_refl (0 : ℝ)) _))
    (Real.rpow_nonneg (by positivity) _)

/-- A convolution with an empty right support vanishes identically. -/
theorem convolutionBound_empty_right
    (A : Finset G) {p q C : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hC : 0 ≤ C) :
    ConvolutionBound A (∅ : Finset G) p q C := by
  refine ⟨hp, hq, hC, ?_⟩
  intro f g
  simp [finiteConvolution, finiteLpNorm]
  exact mul_nonneg
    (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
    (Real.rpow_nonneg (le_refl (0 : ℝ)) _)

/-- The Fourier fourth-norm realization supplied by the standard-analysis
package, selected once and for all.  The torsion-free hypothesis is present
exactly where it occurs in the paper-facing external input. -/
noncomputable def selectedFourierFourth
    (inputs : AnalysisInputs) (H : Type)
    [AddCommGroup H] [IsAddTorsionFree H] [DecidableEq H] :
    FourierFourthNormInput H :=
  Classical.choice
    (inputs.fourierFourth H inferInstance inferInstance inferInstance)

/-- Pointwise verifier with the exact coefficient displayed in Theorem 1.3.
The only non-numerical premises are the two one-support fourth-norm estimates;
neither a final convolution bound nor `Theorem13Statement` is an input. -/
theorem verify_theorem13_instance
    {H : Type} [AddCommGroup H] [DecidableEq H] [IsAddTorsionFree H]
    (inputs : AnalysisInputs)
    (F : FourierFourthNormInput H)
    (X Y : Finset H) (KX KY CX CY eta eps C DA DB p q : ℝ)
    (_hXenergy : HereditaryQuadraticEnergy X KX CX eta)
    (_hYenergy : HereditaryQuadraticEnergy Y KY CY eta)
    (hXfourth : FourierL2FourthBound F X DA)
    (hYfourth : FourierL2FourthBound F Y DB)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hconstant :
      (DA * DB) ^ offDiagonalTheta (1 / p) (1 / q) ≤
        C * ((CX * CY) * (KX * KY)) ^
            (offDiagonalTheta (1 / p) (1 / q) / 4) *
          ((X.card : ℝ) * (Y.card : ℝ)) ^ eps)
    (htarget_nonneg :
      0 ≤ C * ((CX * CY) * (KX * KY)) ^
            (offDiagonalTheta (1 / p) (1 / q) / 4) *
          ((X.card : ℝ) * (Y.card : ℝ)) ^ eps) :
    ConvolutionBound X Y p q
      (C * ((CX * CY) * (KX * KY)) ^
          (offDiagonalTheta (1 / p) (1 / q) / 4) *
        ((X.card : ℝ) * (Y.card : ℝ)) ^ eps) := by
  apply convolutionBound_mono_constant X Y
    (alphaTwo_of_fourierL2Fourth_internal inputs.bilinearInterpolation F X Y
      hXfourth hYfourth hp hp2 hq hq2)
    hconstant htarget_nonneg

/-! ## Exact remaining endpoint boundary for Theorem 1.3 -/

/-- The part of Theorem 1.3 that remains after the finite correlation,
phase-majorant, Young, and exponent-interpolation arguments in this
repository.

This predicate contains no `ConvolutionBound` and no copy of the final
theorem.  Its substantive premises are precisely the two uniform
one-support `L² → L⁴` estimates produced by the hereditary-energy/dyadic
argument (Proposition 5.1 in the manuscript), together with the elementary
comparison between their constants and the displayed theorem constant.
The Fourier realization is the one actually supplied by `inputs`, rather
than an unrelated existential realization. -/
def Theorem13EndpointInputs (inputs : AnalysisInputs) : Prop :=
  ∀ (p q eps : ℝ), 1 ≤ p → p ≤ 2 →
    1 ≤ q → q ≤ 2 → 1 ≤ 1 / p + 1 / q →
    0 < eps →
    ∃ eta : ℝ, 0 < eta ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (H : Type) (_ : AddCommGroup H) (_ : IsAddTorsionFree H)
        (_ : DecidableEq H)
        (X Y : Finset H) (KX KY CX CY : ℝ),
        HereditaryQuadraticEnergy X KX CX eta →
        HereditaryQuadraticEnergy Y KY CY eta →
        X.Nonempty → Y.Nonempty →
        ∃ DA DB : ℝ,
          FourierL2FourthBound (selectedFourierFourth inputs H) X DA ∧
          FourierL2FourthBound (selectedFourierFourth inputs H) Y DB ∧
          (DA * DB) ^ offDiagonalTheta (1 / p) (1 / q) ≤
            C * ((CX * CY) * (KX * KY)) ^
                (offDiagonalTheta (1 / p) (1 / q) / 4) *
              ((X.card : ℝ) * (Y.card : ℝ)) ^ eps ∧
          0 ≤ C * ((CX * CY) * (KX * KY)) ^
                (offDiagonalTheta (1 / p) (1 / q) / 4) *
              ((X.card : ℝ) * (Y.card : ℝ)) ^ eps

/-- Once the uniform one-support endpoint package is supplied, the full
constant-explicit Theorem 1.3 follows.  All bilinear work in this implication
is internal except for the standard complex interpolation statement stored
in `AnalysisInputs`. -/
theorem theorem13_of_endpointInputs
    (inputs : AnalysisInputs)
    (hendpoint : Theorem13EndpointInputs inputs) :
    Theorem13Statement := by
  intro p q eps hp hp2 hq hq2 hpq heps
  obtain ⟨eta, heta, C, hC, hendpoint⟩ :=
    hendpoint p q eps hp hp2 hq hq2 hpq heps
  refine ⟨eta, heta, C, hC, ?_⟩
  intro H hH htf hdec X Y KX KY CX CY hX hY
  letI : AddCommGroup H := hH
  letI : IsAddTorsionFree H := htf
  letI : DecidableEq H := hdec
  have htarget_nonneg :
      0 ≤ C * ((CX * CY) * (KX * KY)) ^
            (offDiagonalTheta (1 / p) (1 / q) / 4) *
          ((X.card : ℝ) * (Y.card : ℝ)) ^ eps := by
    have hcomplexity : 0 ≤ (CX * CY) * (KX * KY) := by
      exact mul_nonneg
        (mul_nonneg (zero_le_one.trans hX.2.1)
          (zero_le_one.trans hY.2.1))
        (mul_nonneg (zero_le_one.trans hX.1)
          (zero_le_one.trans hY.1))
    exact mul_nonneg
      (mul_nonneg hC (Real.rpow_nonneg hcomplexity _))
      (Real.rpow_nonneg (by positivity) _)
  by_cases hXne : X.Nonempty
  · by_cases hYne : Y.Nonempty
    · obtain ⟨DA, DB, hXfourth, hYfourth, hconstant, htarget⟩ :=
        hendpoint H inferInstance inferInstance inferInstance
          X Y KX KY CX CY hX hY hXne hYne
      exact verify_theorem13_instance inputs
        (selectedFourierFourth inputs H) X Y KX KY CX CY eta eps C DA DB p q
        hX hY hXfourth hYfourth hp hp2 hq hq2 hconstant htarget
    · have hYempty : Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hYne
      subst Y
      exact convolutionBound_empty_right X hp hq htarget_nonneg
  · have hXempty : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hXne
    subst X
    exact convolutionBound_empty_left Y hp hq htarget_nonneg

end

end ComplexitySensitiveEnergy
