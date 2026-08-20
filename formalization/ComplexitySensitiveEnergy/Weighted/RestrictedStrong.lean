import Mathlib
import ComplexitySensitiveEnergy.Weighted.Main

/-!
# Uniform restricted-to-strong fourth-norm extension

This file closes the coefficient-dynamic-range gap in Proposition 5.1.  The
complex phase estimate is the one proved in `Weighted.Correlation`.  We use a
finite dyadic decomposition only after normalizing by the literal finite
`ℓ²` norm, and sum the *fourth roots* by the triangle inequality.  A geometric
split makes the resulting constant independent of the number of nonempty
levels.
-/

open scoped BigOperators Pointwise

namespace ComplexitySensitiveEnergy

open External

noncomputable section

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-! ## Correlations depend only on the actual coefficient support -/

/-- Enlarging the displayed finite support does not change a weighted
correlation when the coefficients vanish on the added points. -/
theorem weightedDifferenceCorrelation_eq_of_subset_of_support
    (A B : Finset G) (hBA : B ⊆ A) (f : G → ℂ)
    (hf : ∀ x ∈ A, x ∉ B → f x = 0) (t : G) :
    weightedDifferenceCorrelation A f t =
      weightedDifferenceCorrelation B f t := by
  classical
  unfold weightedDifferenceCorrelation
  symm
  apply Finset.sum_subset
  · intro ab hab
    rw [Finset.mem_filter] at hab ⊢
    exact ⟨Finset.mem_product.mpr
      ⟨hBA (Finset.mem_product.mp hab.1).1,
        hBA (Finset.mem_product.mp hab.1).2⟩, hab.2⟩
  · intro ab habA habB
    have habProd := (Finset.mem_filter.mp habA).1
    have haA := (Finset.mem_product.mp habProd).1
    have hbA := (Finset.mem_product.mp habProd).2
    have hnot : ab.1 ∉ B ∨ ab.2 ∉ B := by
      by_contra h
      push_neg at h
      apply habB
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨h.1, h.2⟩,
          (Finset.mem_filter.mp habA).2⟩
    rcases hnot with haB | hbB
    · simp [hf ab.1 haA haB]
    · simp [hf ab.2 hbA hbB]

/-- The squared-correlation sum likewise depends only on the actual support. -/
theorem weightedCorrelationSquareSum_eq_of_subset_of_support
    (A B : Finset G) (hBA : B ⊆ A) (f : G → ℂ)
    (hf : ∀ x ∈ A, x ∉ B → f x = 0) :
    weightedCorrelationSquareSum A f =
      weightedCorrelationSquareSum B f := by
  classical
  have hcorr := weightedDifferenceCorrelation_eq_of_subset_of_support
    A B hBA f hf
  unfold weightedCorrelationSquareSum
  simp_rw [hcorr]
  symm
  apply Finset.sum_subset
  · intro t ht
    rw [mem_differenceSet] at ht ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := ht
    exact ⟨a, hBA ha, b, hBA hb, rfl⟩
  · intro t htA htB
    rw [weightedDifferenceCorrelation_eq_zero_of_not_mem_differenceSet
      B f htB]
    simp

/-- A dyadic restriction has the same correlation square sum whether it is
displayed on the original support or on its actual dyadic level. -/
theorem weightedCorrelationSquareSum_dyadicRestriction
    (A : Finset G) (f : G → ℂ) (j : ℕ) :
    weightedCorrelationSquareSum A (dyadicRestriction A f j) =
      weightedCorrelationSquareSum (dyadicLevel A f j)
        (dyadicRestriction A f j) := by
  apply weightedCorrelationSquareSum_eq_of_subset_of_support
    A (dyadicLevel A f j) (dyadicLevel_subset A f j)
  intro x hxA hx
  exact dyadicRestriction_of_not_mem hx

/-! ## Homogeneity and fixed-support dyadic fourth-root bounds -/

theorem weightedDifferenceCorrelation_smul
    (A : Finset G) (c : ℂ) (f : G → ℂ) (t : G) :
    weightedDifferenceCorrelation A (c • f) t =
      (c * star c) * weightedDifferenceCorrelation A f t := by
  classical
  unfold weightedDifferenceCorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem weightedCorrelationSquareSum_smul
    (A : Finset G) (c : ℂ) (f : G → ℂ) :
    weightedCorrelationSquareSum A (c • f) =
      ‖c‖ ^ 4 * weightedCorrelationSquareSum A f := by
  classical
  unfold weightedCorrelationSquareSum
  simp_rw [weightedDifferenceCorrelation_smul, norm_mul, norm_star]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- Homogeneity is forced by the correlation identity and nonnegativity; it
does not need to be added to the external Fourier interface. -/
theorem fourierFourthNorm_smul
    (F : FourierFourthNormInput G) (A : Finset G)
    (c : ℂ) (f : G → ℂ) :
    F.fourthNorm A (c • f) = ‖c‖ * F.fourthNorm A f := by
  apply (pow_left_inj₀ (F.nonnegative A (c • f))
    (mul_nonneg (norm_nonneg c) (F.nonnegative A f))
    (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [F.correlation_identity, weightedCorrelationSquareSum_smul,
    mul_pow, F.correlation_identity]

theorem fourierFourthNorm_zero
    (F : FourierFourthNormInput G) (A : Finset G) :
    F.fourthNorm A (0 : G → ℂ) = 0 := by
  have h := fourierFourthNorm_smul F A (0 : ℂ) (0 : G → ℂ)
  simpa using h

theorem finiteLpNorm_two_smul
    (A : Finset G) (c : ℂ) (f : G → ℂ) :
    finiteLpNorm 2 A (c • f) = ‖c‖ * finiteLpNorm 2 A f := by
  rw [finiteLpNorm_two_eq_norm, finiteLpNorm_two_eq_norm]
  have hvec : finiteL2Vector A (c • f) = c • finiteL2Vector A f := by
    ext x
    simp [finiteL2Vector]
  rw [hvec, norm_smul]

/-- A coordinate on the displayed finite support is bounded by the literal
finite `ℓ²` norm. -/
theorem norm_le_finiteLpNorm_two (A : Finset G) (f : G → ℂ)
    {x : G} (hx : x ∈ A) :
    ‖f x‖ ≤ finiteLpNorm 2 A f := by
  rw [finiteLpNorm_two_eq_sqrt_sum]
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum
    (fun y _ => sq_nonneg ‖f y‖) hx

/-- A hereditary quadratic-energy hypothesis in the paper's notation is the
power-profile hypothesis consumed by the dyadic phase lemma. -/
theorem HereditaryQuadraticEnergy.toHereditaryEnergyBound
    (A : Finset G) {K C eta : ℝ}
    (h : HereditaryQuadraticEnergy A K C eta) :
    HereditaryEnergyBound A (powerEnergyProfile (C * K) (2 + eta)) := by
  intro B hBA
  simpa [powerEnergyProfile, mul_assoc] using h.2.2.2 B hBA

/-- The fixed-support Fourier fourth norm of one dyadic restriction satisfies
the phase-safe hereditary energy estimate. -/
theorem fourierFourthNorm_dyadicRestriction_le
    (F : FourierFourthNormInput G) (A : Finset G) (f : G → ℂ)
    {K C eta : ℝ} (henergy : HereditaryQuadraticEnergy A K C eta)
    (j : ℕ) :
    F.fourthNorm A (dyadicRestriction A f j) ≤
      dyadicScale j * (C * K) ^ (1 / 4 : ℝ) *
        ((dyadicLevel A f j).card : ℝ) ^ ((2 + eta) / 4) := by
  let B := dyadicLevel A f j
  let u := dyadicRestriction A f j
  have hCK : 0 ≤ C * K := mul_nonneg
    (zero_le_one.trans henergy.2.1) (zero_le_one.trans henergy.1)
  have hcard : 0 ≤ (B.card : ℝ) := by positivity
  have hrhs : 0 ≤ dyadicScale j * (C * K) ^ (1 / 4 : ℝ) *
      (B.card : ℝ) ^ ((2 + eta) / 4) :=
    mul_nonneg
      (mul_nonneg (dyadicScale_nonneg j) (Real.rpow_nonneg hCK _))
      (Real.rpow_nonneg hcard _)
  change F.fourthNorm A u ≤
    dyadicScale j * (C * K) ^ (1 / 4 : ℝ) *
      (B.card : ℝ) ^ ((2 + eta) / 4)
  apply (pow_le_pow_iff_left₀ (F.nonnegative A u) hrhs
    (by norm_num : (4 : ℕ) ≠ 0)).mp
  calc
    F.fourthNorm A u ^ 4 = weightedCorrelationSquareSum A u :=
      F.correlation_identity A u
    _ = weightedCorrelationSquareSum B u := by
      simpa [B, u] using weightedCorrelationSquareSum_dyadicRestriction A f j
    _ ≤ dyadicScale j ^ 4 *
        powerEnergyProfile (C * K) (2 + eta) B.card :=
      dyadicLevel_weightedCorrelationSquareSum_le_of_hereditary
        A f (powerEnergyProfile (C * K) (2 + eta))
          henergy.toHereditaryEnergyBound j
    _ = (dyadicScale j * (C * K) ^ (1 / 4 : ℝ) *
        (B.card : ℝ) ^ ((2 + eta) / 4)) ^ 4 := by
      rw [powerEnergyProfile, mul_pow, mul_pow]
      have hrootCK : ((C * K) ^ (1 / 4 : ℝ)) ^ 4 = C * K := by
        convert
          (Real.rpow_inv_natCast_pow hCK (by norm_num : (4 : ℕ) ≠ 0))
            using 1 <;> norm_num
      have hrootCard :
          ((B.card : ℝ) ^ ((2 + eta) / 4)) ^ 4 =
            (B.card : ℝ) ^ (2 + eta) := by
        rw [← Real.rpow_mul_natCast hcard]
        congr 1
        norm_num
      rw [hrootCK, hrootCard]
      ring

/-! ## The normalized `ℓ²` distribution bound -/

/-- The lower cutoff on a dyadic level charges its cardinality against the
literal finite `ℓ²` square sum. -/
theorem dyadicLevel_card_mul_scale_sq_le
    (A : Finset G) (f : G → ℂ) (j : ℕ) :
    ((dyadicLevel A f j).card : ℝ) * dyadicScale (j + 1) ^ 2 ≤
      ∑ x ∈ A, ‖f x‖ ^ 2 := by
  calc
    ((dyadicLevel A f j).card : ℝ) * dyadicScale (j + 1) ^ 2 =
        ∑ _x ∈ dyadicLevel A f j, dyadicScale (j + 1) ^ 2 := by
      simp
    _ ≤ ∑ x ∈ dyadicLevel A f j, ‖f x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      exact pow_le_pow_left₀ (dyadicScale_nonneg (j + 1))
        (mem_dyadicLevel.mp hx).2.1.le 2
    _ ≤ ∑ x ∈ A, ‖f x‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (dyadicLevel_subset A f j)
      intro x hxA hxlevel
      exact sq_nonneg ‖f x‖

theorem finiteLpNorm_two_eq_one_iff_squareSum
    (A : Finset G) (f : G → ℂ) :
    finiteLpNorm 2 A f = 1 ↔ (∑ x ∈ A, ‖f x‖ ^ 2) = 1 := by
  rw [finiteLpNorm_two_eq_sqrt_sum]
  constructor
  · intro h
    have hsq := congrArg (fun r : ℝ => r ^ 2) h
    simpa [Real.sq_sqrt (by positivity :
      0 ≤ ∑ x ∈ A, ‖f x‖ ^ 2)] using hsq
  · intro h
    rw [h]
    norm_num

/-- For an `ℓ²`-normalized coefficient function, level `j` has at most
`4^(j+1)` points.  This is the weak-`ℓ²` distribution estimate used in the
Lorentz summation. -/
theorem dyadicLevel_card_le_four_pow
    (A : Finset G) (f : G → ℂ)
    (hnorm : finiteLpNorm 2 A f = 1) (j : ℕ) :
    ((dyadicLevel A f j).card : ℝ) ≤ (4 : ℝ) ^ (j + 1) := by
  have hmass : ((dyadicLevel A f j).card : ℝ) *
      dyadicScale (j + 1) ^ 2 ≤ 1 := by
    rw [← (finiteLpNorm_two_eq_one_iff_squareSum A f).mp hnorm]
    exact dyadicLevel_card_mul_scale_sq_le A f j
  have hscale : 0 < dyadicScale (j + 1) ^ 2 :=
    sq_pos_of_pos (dyadicScale_pos (j + 1))
  have hscaled : ((dyadicLevel A f j).card : ℝ) *
      dyadicScale (j + 1) ^ 2 ≤
        (4 : ℝ) ^ (j + 1) * dyadicScale (j + 1) ^ 2 := by
    calc
    ((dyadicLevel A f j).card : ℝ) * dyadicScale (j + 1) ^ 2 ≤ 1 := hmass
    _ = (4 : ℝ) ^ (j + 1) * dyadicScale (j + 1) ^ 2 := by
      simp only [dyadicScale, pow_two]
      rw [← mul_assoc, ← mul_pow]
      norm_num
      rw [← mul_pow]
      norm_num
  exact le_of_mul_le_mul_right hscaled hscale

/-! ## Uniform Lorentz summation -/

/-- The exponent assigned to the weak-`ℓ²` distribution estimate. -/
def dyadicLorentzBeta (eta : ℝ) : ℝ := 1 / 2 - eta / 4

/-- The geometric ratio arising after the mixed cardinality estimate. -/
def dyadicLorentzRatio (eta : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (4 : ℝ) ^ dyadicLorentzBeta eta

/-- An explicit dynamic-range-independent Lorentz constant. -/
def dyadicLorentzConstant (eta : ℝ) : ℝ :=
  (4 : ℝ) ^ dyadicLorentzBeta eta *
    (1 - dyadicLorentzRatio eta)⁻¹

theorem dyadicLorentzBeta_pos {eta : ℝ} (heta2 : eta < 2) :
    0 < dyadicLorentzBeta eta := by
  dsimp [dyadicLorentzBeta]
  linarith

theorem dyadicLorentzBeta_lt_half {eta : ℝ} (heta : 0 < eta) :
    dyadicLorentzBeta eta < 1 / 2 := by
  dsimp [dyadicLorentzBeta]
  linarith

theorem four_rpow_half : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
  rw [← Real.sqrt_eq_rpow]
  norm_num

theorem dyadicLorentzRatio_nonneg (eta : ℝ) :
    0 ≤ dyadicLorentzRatio eta := by
  unfold dyadicLorentzRatio
  positivity

theorem dyadicLorentzRatio_lt_one {eta : ℝ} (heta : 0 < eta) :
    dyadicLorentzRatio eta < 1 := by
  have hpow : (4 : ℝ) ^ dyadicLorentzBeta eta < 2 := by
    rw [← four_rpow_half]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      (dyadicLorentzBeta_lt_half heta)
  unfold dyadicLorentzRatio
  nlinarith

theorem dyadicLorentzConstant_nonneg {eta : ℝ} (heta : 0 < eta) :
    0 ≤ dyadicLorentzConstant eta := by
  unfold dyadicLorentzConstant
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (inv_nonneg.mpr (sub_nonneg.mpr (dyadicLorentzRatio_lt_one heta).le))

/-- The summable geometric majorant before inserting the ambient-cardinality
factor. -/
def dyadicLorentzSequence (eta : ℝ) (j : ℕ) : ℝ :=
  dyadicScale j * ((4 : ℝ) ^ (j + 1)) ^ dyadicLorentzBeta eta

theorem dyadicLorentzSequence_nonneg (eta : ℝ) (j : ℕ) :
    0 ≤ dyadicLorentzSequence eta j := by
  unfold dyadicLorentzSequence
  exact mul_nonneg (dyadicScale_nonneg j)
    (Real.rpow_nonneg (by positivity) _)

theorem dyadicLorentzSequence_succ (eta : ℝ) (j : ℕ) :
    dyadicLorentzSequence eta (j + 1) =
      dyadicLorentzRatio eta * dyadicLorentzSequence eta j := by
  unfold dyadicLorentzSequence dyadicLorentzRatio
  rw [dyadicScale_succ]
  have hpow : (4 : ℝ) ^ (j + 1 + 1) =
      (4 : ℝ) ^ (j + 1) * 4 := by
    rw [pow_succ]
  rw [hpow, Real.mul_rpow (by positivity) (by norm_num : (0 : ℝ) ≤ 4)]
  ring

theorem dyadicLorentzSequence_eq (eta : ℝ) (j : ℕ) :
    dyadicLorentzSequence eta j =
      (4 : ℝ) ^ dyadicLorentzBeta eta *
        dyadicLorentzRatio eta ^ j := by
  induction j with
  | zero => simp [dyadicLorentzSequence]
  | succ j ih =>
      rw [dyadicLorentzSequence_succ, ih, pow_succ]
      ring

theorem summable_dyadicLorentzSequence {eta : ℝ} (heta : 0 < eta) :
    Summable (dyadicLorentzSequence eta) := by
  have hs := summable_geometric_of_lt_one
    (dyadicLorentzRatio_nonneg eta) (dyadicLorentzRatio_lt_one heta)
  exact (hs.mul_left ((4 : ℝ) ^ dyadicLorentzBeta eta)).congr
    (fun j => (dyadicLorentzSequence_eq eta j).symm)

theorem tsum_dyadicLorentzSequence {eta : ℝ} (heta : 0 < eta) :
    ∑' j : ℕ, dyadicLorentzSequence eta j =
      dyadicLorentzConstant eta := by
  simp_rw [dyadicLorentzSequence_eq]
  rw [tsum_mul_left, tsum_geometric_of_lt_one
    (dyadicLorentzRatio_nonneg eta) (dyadicLorentzRatio_lt_one heta)]
  rfl

/-- The numerical heart of the restricted-to-strong argument.  It combines
the trivial bound `m≤N` with the weak-`ℓ²` bound `m≤4^(j+1)` and produces a
summable geometric majorant. -/
theorem dyadicLorentzTerm_le
    {eta N m : ℝ} {j : ℕ}
    (heta : 0 < eta) (heta2 : eta < 2)
    (hm : 0 ≤ m) (hmN : m ≤ N)
    (hm4 : m ≤ (4 : ℝ) ^ (j + 1)) :
    dyadicScale j * m ^ ((2 + eta) / 4) ≤
      N ^ (eta / 2) * dyadicLorentzSequence eta j := by
  have hN : 0 ≤ N := hm.trans hmN
  have hetaHalf : 0 ≤ eta / 2 := by positivity
  have hbeta : 0 ≤ dyadicLorentzBeta eta :=
    (dyadicLorentzBeta_pos heta2).le
  have hexp : eta / 2 + dyadicLorentzBeta eta =
      (2 + eta) / 4 := by
    dsimp [dyadicLorentzBeta]
    ring
  rw [← hexp, Real.rpow_add_of_nonneg hm hetaHalf hbeta]
  calc
    dyadicScale j * (m ^ (eta / 2) * m ^ dyadicLorentzBeta eta) ≤
        dyadicScale j *
          (N ^ (eta / 2) *
            ((4 : ℝ) ^ (j + 1)) ^ dyadicLorentzBeta eta) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul
          (Real.rpow_le_rpow hm hmN hetaHalf)
          (Real.rpow_le_rpow hm hm4 hbeta)
          (Real.rpow_nonneg hm _)
          (Real.rpow_nonneg hN _)
      · exact dyadicScale_nonneg j
    _ = N ^ (eta / 2) * dyadicLorentzSequence eta j := by
      unfold dyadicLorentzSequence
      ring

/-- Uniform finite-level Lorentz sum.  The right side is independent of the
number and location of the levels. -/
theorem dyadicLorentzSum_le
    {eta N : ℝ} (levels : Finset ℕ) (m : ℕ → ℝ)
    (heta : 0 < eta) (heta2 : eta < 2)
    (hN : 0 ≤ N)
    (hm : ∀ j ∈ levels, 0 ≤ m j)
    (hmN : ∀ j ∈ levels, m j ≤ N)
    (hm4 : ∀ j ∈ levels, m j ≤ (4 : ℝ) ^ (j + 1)) :
    (∑ j ∈ levels,
      dyadicScale j * (m j) ^ ((2 + eta) / 4)) ≤
        dyadicLorentzConstant eta * N ^ (eta / 2) := by
  calc
    (∑ j ∈ levels, dyadicScale j * (m j) ^ ((2 + eta) / 4)) ≤
        ∑ j ∈ levels, N ^ (eta / 2) * dyadicLorentzSequence eta j := by
      apply Finset.sum_le_sum
      intro j hj
      exact dyadicLorentzTerm_le heta heta2 (hm j hj)
        (hmN j hj) (hm4 j hj)
    _ = N ^ (eta / 2) *
        ∑ j ∈ levels, dyadicLorentzSequence eta j := by
      rw [Finset.mul_sum]
    _ ≤ N ^ (eta / 2) * (∑' j : ℕ, dyadicLorentzSequence eta j) := by
      apply mul_le_mul_of_nonneg_left
      · exact (summable_dyadicLorentzSequence heta).sum_le_tsum levels
          (fun j hj => dyadicLorentzSequence_nonneg eta j)
      · exact Real.rpow_nonneg hN _
    _ = dyadicLorentzConstant eta * N ^ (eta / 2) := by
      rw [tsum_dyadicLorentzSequence heta]
      ring

/-- Specialized Lorentz sum for dyadic levels of an `ℓ²`-normalized
coefficient function. -/
theorem normalized_dyadicRootSum_le
    (A : Finset G) (f : G → ℂ) (levels : Finset ℕ)
    {eta : ℝ} (heta : 0 < eta) (heta2 : eta < 2)
    (hnorm : finiteLpNorm 2 A f = 1) :
    (∑ j ∈ levels, dyadicScale j *
      ((dyadicLevel A f j).card : ℝ) ^ ((2 + eta) / 4)) ≤
        dyadicLorentzConstant eta * (A.card : ℝ) ^ (eta / 2) := by
  apply dyadicLorentzSum_le levels
    (fun j => ((dyadicLevel A f j).card : ℝ)) heta heta2 (by positivity)
  · intro j hj
    positivity
  · intro j hj
    exact_mod_cast Finset.card_le_card (dyadicLevel_subset A f j)
  · intro j hj
    exact dyadicLevel_card_le_four_pow A f hnorm j

/-! ## Proposition 5.1: the uniform one-support endpoint -/

/-- Literal restriction of a coefficient function to a finite support. -/
def finiteSupportRestriction (A : Finset G) (f : G → ℂ) : G → ℂ :=
  fun x => if x ∈ A then f x else 0

@[simp]
theorem finiteSupportRestriction_of_mem (A : Finset G) (f : G → ℂ)
    {x : G} (hx : x ∈ A) :
    finiteSupportRestriction A f x = f x := by
  simp [finiteSupportRestriction, hx]

@[simp]
theorem finiteSupportRestriction_of_not_mem (A : Finset G) (f : G → ℂ)
    {x : G} (hx : x ∉ A) :
    finiteSupportRestriction A f x = 0 := by
  simp [finiteSupportRestriction, hx]

theorem finiteLpNorm_two_finiteSupportRestriction
    (A : Finset G) (f : G → ℂ) :
    finiteLpNorm 2 A (finiteSupportRestriction A f) =
      finiteLpNorm 2 A f := by
  rw [finiteLpNorm_two_eq_sqrt_sum, finiteLpNorm_two_eq_sqrt_sum]
  apply congrArg Real.sqrt
  apply Finset.sum_congr rfl
  intro x hx
  simp [finiteSupportRestriction, hx]

theorem fourierFourthNorm_finiteSupportRestriction
    (F : FourierFourthNormInput G) (A : Finset G) (f : G → ℂ) :
    F.fourthNorm A (finiteSupportRestriction A f) =
      F.fourthNorm A f := by
  exact F.supported_ext A _ _
    (fun x hx => finiteSupportRestriction_of_mem A f hx)

/-- The explicit strong-type loss supplied by the uniform Lorentz sum. -/
def restrictedStrongConstant (A : Finset G) (K C eta : ℝ) : ℝ :=
  dyadicLorentzConstant eta * (C * K) ^ (1 / 4 : ℝ) *
    (A.card : ℝ) ^ (eta / 2)

theorem restrictedStrongConstant_nonneg
    (A : Finset G) {K C eta : ℝ}
    (henergy : HereditaryQuadraticEnergy A K C eta) :
    0 ≤ restrictedStrongConstant A K C eta := by
  unfold restrictedStrongConstant
  have hCK : 0 ≤ C * K := mul_nonneg
    (zero_le_one.trans henergy.2.1) (zero_le_one.trans henergy.1)
  exact mul_nonneg
    (mul_nonneg (dyadicLorentzConstant_nonneg henergy.2.2.1)
      (Real.rpow_nonneg hCK _))
    (Real.rpow_nonneg (by positivity) _)

/-- **Proposition 5.1, uniform one-support form.**

The coefficient function is arbitrary.  It is first restricted to `A`, then
normalized by its actual finite `ℓ²` norm.  Minkowski is applied to the
Fourier fourth norm, each dyadic level uses the internally proved complex
phase majorant, and `normalized_dyadicRootSum_le` removes every dependence on
the number of levels. -/
theorem fourierL2FourthBound_of_hereditary
    (F : FourierFourthNormInput G) (A : Finset G)
    {K C eta : ℝ} (henergy : HereditaryQuadraticEnergy A K C eta)
    (heta2 : eta < 2) :
    FourierL2FourthBound F A (restrictedStrongConstant A K C eta) := by
  refine ⟨restrictedStrongConstant_nonneg A henergy, ?_⟩
  intro f
  let fA : G → ℂ := finiteSupportRestriction A f
  let r : ℝ := finiteLpNorm 2 A f
  have hr : 0 ≤ r := finiteLpNorm_nonneg 2 A f
  by_cases hr0 : r = 0
  · have hfzero : ∀ x ∈ A, f x = 0 := by
      intro x hx
      have hxnorm := norm_le_finiteLpNorm_two A f hx
      change ‖f x‖ ≤ r at hxnorm
      rw [hr0] at hxnorm
      exact norm_eq_zero.mp (le_antisymm hxnorm (norm_nonneg _))
    have hFzero : F.fourthNorm A f = F.fourthNorm A (0 : G → ℂ) :=
      F.supported_ext A f 0 (fun x hx => by simp [hfzero x hx])
    rw [hFzero, fourierFourthNorm_zero]
    change 0 ≤ restrictedStrongConstant A K C eta * r
    rw [hr0]
    simp
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    let g : G → ℂ := ((r : ℂ)⁻¹) • fA
    have hsupport : ∀ x ∉ A, g x = 0 := by
      intro x hx
      simp [g, fA, finiteSupportRestriction, hx]
    have hgBounded : ∀ x ∈ A, ‖g x‖ ≤ 1 := by
      intro x hx
      have hfx : ‖f x‖ ≤ r := norm_le_finiteLpNorm_two A f hx
      have hinv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr
      calc
        ‖g x‖ = r⁻¹ * ‖f x‖ := by
          simp [g, fA, finiteSupportRestriction, hx,
            norm_mul, Complex.norm_real, abs_of_pos hrpos]
        _ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hfx hinv
        _ = 1 := inv_mul_cancel₀ hr0
    have hgNorm : finiteLpNorm 2 A g = 1 := by
      change finiteLpNorm 2 A (((r : ℂ)⁻¹) • fA) = 1
      rw [finiteLpNorm_two_smul]
      change ‖(r : ℂ)⁻¹‖ *
        finiteLpNorm 2 A (finiteSupportRestriction A f) = 1
      rw [finiteLpNorm_two_finiteSupportRestriction]
      simp [r, Complex.norm_real, abs_of_pos hrpos, hr0]
    obtain ⟨levels, hcover⟩ := exists_finite_dyadic_cover A g hgBounded
    have hrecover : (∑ j ∈ levels, dyadicRestriction A g j) = g :=
      sum_dyadicRestriction_eq A g levels hsupport hcover
    have htriangle : F.fourthNorm A g ≤
        ∑ j ∈ levels, F.fourthNorm A (dyadicRestriction A g j) := by
      calc
        F.fourthNorm A g =
            F.fourthNorm A (∑ j ∈ levels, dyadicRestriction A g j) := by
          rw [hrecover]
        _ ≤ ∑ j ∈ levels, F.fourthNorm A (dyadicRestriction A g j) :=
          size_finset_sum_le (F.fourthNorm A)
            (fourierFourthNorm_zero F A) (F.triangle A) levels
              (fun j => dyadicRestriction A g j)
    have hlevelSum :
        (∑ j ∈ levels, F.fourthNorm A (dyadicRestriction A g j)) ≤
          (C * K) ^ (1 / 4 : ℝ) *
            ∑ j ∈ levels, dyadicScale j *
              ((dyadicLevel A g j).card : ℝ) ^ ((2 + eta) / 4) := by
      calc
        (∑ j ∈ levels, F.fourthNorm A (dyadicRestriction A g j)) ≤
            ∑ j ∈ levels,
              dyadicScale j * (C * K) ^ (1 / 4 : ℝ) *
                ((dyadicLevel A g j).card : ℝ) ^ ((2 + eta) / 4) := by
          apply Finset.sum_le_sum
          intro j hj
          exact fourierFourthNorm_dyadicRestriction_le F A g henergy j
        _ = (C * K) ^ (1 / 4 : ℝ) *
            ∑ j ∈ levels, dyadicScale j *
              ((dyadicLevel A g j).card : ℝ) ^ ((2 + eta) / 4) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    have hrootSum := normalized_dyadicRootSum_le
      A g levels henergy.2.2.1 heta2 hgNorm
    have hnormalized : F.fourthNorm A g ≤
        restrictedStrongConstant A K C eta := by
      calc
        F.fourthNorm A g ≤
            ∑ j ∈ levels, F.fourthNorm A (dyadicRestriction A g j) := htriangle
        _ ≤ (C * K) ^ (1 / 4 : ℝ) *
            ∑ j ∈ levels, dyadicScale j *
              ((dyadicLevel A g j).card : ℝ) ^ ((2 + eta) / 4) := hlevelSum
        _ ≤ (C * K) ^ (1 / 4 : ℝ) *
            (dyadicLorentzConstant eta *
              (A.card : ℝ) ^ (eta / 2)) := by
          exact mul_le_mul_of_nonneg_left hrootSum
            (Real.rpow_nonneg (mul_nonneg
              (zero_le_one.trans henergy.2.1)
              (zero_le_one.trans henergy.1)) _)
        _ = restrictedStrongConstant A K C eta := by
          unfold restrictedStrongConstant
          ring
    have hfAeq : fA = (r : ℂ) • g := by
      funext x
      simp [g, smul_smul, hr0]
    calc
      F.fourthNorm A f = F.fourthNorm A fA :=
        (fourierFourthNorm_finiteSupportRestriction F A f).symm
      _ = F.fourthNorm A ((r : ℂ) • g) := by rw [← hfAeq]
      _ = r * F.fourthNorm A g := by
        rw [fourierFourthNorm_smul]
        simp [Complex.norm_real, abs_of_pos hrpos]
      _ ≤ r * restrictedStrongConstant A K C eta :=
        mul_le_mul_of_nonneg_left hnormalized hr
      _ = restrictedStrongConstant A K C eta * finiteLpNorm 2 A f := by
        simp [r, mul_comm]

/-! ## Closing the paper-facing Theorem 1.3 interface -/

theorem offDiagonalTheta_nonneg (x y : ℝ) :
    0 ≤ offDiagonalTheta x y := by
  unfold offDiagonalTheta
  exact le_max_left _ _

theorem offDiagonalTheta_le_one_of_one_le_sum
    {x y : ℝ} (hxy : 1 ≤ x + y) :
    offDiagonalTheta x y ≤ 1 := by
  unfold offDiagonalTheta
  apply max_le
  · norm_num
  · linarith

/-- Multiplying the two one-support constants and raising to an interpolation
weight `theta≤1` produces exactly the paper's complexity power and a cardinal
loss bounded by any `eps≥eta`. -/
theorem restrictedStrongConstants_product_rpow_le
    (A B : Finset G) {KX KY CX CY eta eps theta : ℝ}
    (hA : HereditaryQuadraticEnergy A KX CX eta)
    (hB : HereditaryQuadraticEnergy B KY CY eta)
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hetaeps : eta ≤ eps) :
    (restrictedStrongConstant A KX CX eta *
        restrictedStrongConstant B KY CY eta) ^ theta ≤
      (dyadicLorentzConstant eta * dyadicLorentzConstant eta) ^ theta *
        ((CX * CY) * (KX * KY)) ^ (theta / 4) *
          ((A.card : ℝ) * (B.card : ℝ)) ^ eps := by
  let L := dyadicLorentzConstant eta
  let Q := (CX * CY) * (KX * KY)
  let N := (A.card : ℝ) * (B.card : ℝ)
  have heta : 0 < eta := hA.2.2.1
  have hL : 0 ≤ L := by
    dsimp [L]
    exact dyadicLorentzConstant_nonneg heta
  have hCX : 0 ≤ CX := zero_le_one.trans hA.2.1
  have hCY : 0 ≤ CY := zero_le_one.trans hB.2.1
  have hKX : 0 ≤ KX := zero_le_one.trans hA.1
  have hKY : 0 ≤ KY := zero_le_one.trans hB.1
  have hCXKX : 0 ≤ CX * KX := mul_nonneg hCX hKX
  have hCYKY : 0 ≤ CY * KY := mul_nonneg hCY hKY
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hAcard : 0 ≤ (A.card : ℝ) := by positivity
  have hBcard : 0 ≤ (B.card : ℝ) := by positivity
  have hN : 0 ≤ N := by
    dsimp [N]
    positivity
  have hAone : (1 : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast hAne.card_pos
  have hBone : (1 : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast hBne.card_pos
  have hNone : 1 ≤ N := by
    dsimp [N]
    simpa using mul_le_mul hAone hBone (by norm_num : (0 : ℝ) ≤ 1)
      (zero_le_one.trans hAone)
  have hprod :
      restrictedStrongConstant A KX CX eta *
          restrictedStrongConstant B KY CY eta =
        (L * L) *
          (Q ^ (1 / 4 : ℝ) * N ^ (eta / 2)) := by
    calc
      restrictedStrongConstant A KX CX eta *
          restrictedStrongConstant B KY CY eta =
          (L * L) *
            (((CX * KX) * (CY * KY)) ^ (1 / 4 : ℝ) *
              ((A.card : ℝ) * (B.card : ℝ)) ^ (eta / 2)) := by
        unfold restrictedStrongConstant
        dsimp [L]
        rw [Real.mul_rpow hCXKX hCYKY,
          Real.mul_rpow hAcard hBcard]
        ring
      _ = (L * L) *
          (Q ^ (1 / 4 : ℝ) * N ^ (eta / 2)) := by
        dsimp [Q, N]
        congr 3
        ring
  rw [hprod]
  rw [Real.mul_rpow (mul_nonneg hL hL)
    (mul_nonneg (Real.rpow_nonneg hQ _)
      (Real.rpow_nonneg hN _))]
  rw [Real.mul_rpow (Real.rpow_nonneg hQ _)
    (Real.rpow_nonneg hN _)]
  rw [← Real.rpow_mul hQ, ← Real.rpow_mul hN]
  have hqexp : (1 / 4 : ℝ) * theta = theta / 4 := by ring
  have hnexp : eta / 2 * theta ≤ eps := by
    have heta0 : 0 ≤ eta := heta.le
    nlinarith
  rw [hqexp]
  calc
    (L * L) ^ theta * (Q ^ (theta / 4) *
        N ^ (eta / 2 * theta)) =
        ((L * L) ^ theta * Q ^ (theta / 4)) *
          N ^ (eta / 2 * theta) := by ring
    _ ≤ ((L * L) ^ theta * Q ^ (theta / 4)) * N ^ eps := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow_of_exponent_le hNone hnexp
      · exact mul_nonneg
          (Real.rpow_nonneg (mul_nonneg hL hL) _)
          (Real.rpow_nonneg hQ _)
    _ = (dyadicLorentzConstant eta * dyadicLorentzConstant eta) ^ theta *
        ((CX * CY) * (KX * KY)) ^ (theta / 4) *
          ((A.card : ℝ) * (B.card : ℝ)) ^ eps := by
      rfl

/-- The internally proved Proposition 5.1 endpoints satisfy the exact
paper-facing endpoint package.  The only remaining inputs are those explicitly
stored in `AnalysisInputs`: the standard Fourier realization and complex
bilinear interpolation theorem. -/
theorem theorem13EndpointInputs_internal (inputs : AnalysisInputs) :
    Theorem13EndpointInputs inputs := by
  intro p q eps hp hp2 hq hq2 hpq heps
  let eta : ℝ := min 1 eps
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min zero_lt_one heps
  have heta2 : eta < 2 :=
    (min_le_left (1 : ℝ) eps).trans_lt (by norm_num)
  have hetaeps : eta ≤ eps := min_le_right _ _
  let theta : ℝ := offDiagonalTheta (1 / p) (1 / q)
  have htheta0 : 0 ≤ theta := by
    dsimp [theta]
    exact offDiagonalTheta_nonneg _ _
  have htheta1 : theta ≤ 1 := by
    dsimp [theta]
    exact offDiagonalTheta_le_one_of_one_le_sum hpq
  let L : ℝ := dyadicLorentzConstant eta
  let Cout : ℝ := (L * L) ^ theta
  have hCout : 0 ≤ Cout := by
    dsimp [Cout]
    exact Real.rpow_nonneg
      (mul_nonneg (dyadicLorentzConstant_nonneg heta)
        (dyadicLorentzConstant_nonneg heta)) _
  refine ⟨eta, heta, Cout, hCout, ?_⟩
  intro H hH htf hdec X Y KX KY CX CY hX hY hXne hYne
  letI : AddCommGroup H := hH
  letI : IsAddTorsionFree H := htf
  letI : DecidableEq H := hdec
  let F : FourierFourthNormInput H := selectedFourierFourth inputs H
  let DX : ℝ := restrictedStrongConstant X KX CX eta
  let DY : ℝ := restrictedStrongConstant Y KY CY eta
  refine ⟨DX, DY, ?_, ?_, ?_, ?_⟩
  · exact fourierL2FourthBound_of_hereditary F X hX heta2
  · exact fourierL2FourthBound_of_hereditary F Y hY heta2
  · change (restrictedStrongConstant X KX CX eta *
        restrictedStrongConstant Y KY CY eta) ^ theta ≤
      (dyadicLorentzConstant eta * dyadicLorentzConstant eta) ^ theta *
        ((CX * CY) * (KX * KY)) ^ (theta / 4) *
          ((X.card : ℝ) * (Y.card : ℝ)) ^ eps
    exact restrictedStrongConstants_product_rpow_le X Y hX hY hXne hYne
      htheta0 htheta1 hetaeps
  · change 0 ≤ (dyadicLorentzConstant eta *
        dyadicLorentzConstant eta) ^ theta *
      ((CX * CY) * (KX * KY)) ^ (theta / 4) *
        ((X.card : ℝ) * (Y.card : ℝ)) ^ eps
    have hcomplexity : 0 ≤ (CX * CY) * (KX * KY) := by
      exact mul_nonneg
        (mul_nonneg (zero_le_one.trans hX.2.1)
          (zero_le_one.trans hY.2.1))
        (mul_nonneg (zero_le_one.trans hX.1)
          (zero_le_one.trans hY.1))
    exact mul_nonneg
      (mul_nonneg
        (Real.rpow_nonneg
          (mul_nonneg (dyadicLorentzConstant_nonneg heta)
            (dyadicLorentzConstant_nonneg heta)) _)
        (Real.rpow_nonneg hcomplexity _))
      (Real.rpow_nonneg (by positivity) _)

/-- Full internal derivation of the constant-explicit Theorem 1.3 from the
declared standard-analysis package. -/
theorem theorem13_of_analysisInputs (inputs : AnalysisInputs) :
    Theorem13Statement :=
  theorem13_of_endpointInputs inputs (theorem13EndpointInputs_internal inputs)

/-- Short paper-facing alias. -/
theorem theorem13_internal : AnalysisInputs → Theorem13Statement :=
  theorem13_of_analysisInputs

end

end ComplexitySensitiveEnergy
