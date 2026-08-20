import ComplexitySensitiveEnergy.Turning.Definitions
import ComplexitySensitiveEnergy.Turning.DyadicAssembly

/-!
# Non-circular verifier for the upper bound in Theorem 1.4

The external CDW/strip stage supplies dyadic classes, their masses, and one
nonnegative layer contribution per class.  Its conclusion stops at the
sixth-root comparison and the per-layer estimate.  The sixth power,
finite-class Hölder estimate, logarithmic loss absorption, and final theorem
are proved here.
-/

open scoped BigOperators Pointwise

namespace ComplexitySensitiveEnergy.Turning

noncomputable section

/-- A convenient real upper scale for the number of nonempty dyadic classes.
The factor two accommodates conversion from binary to natural logarithms. -/
def dyadicClassScale (N : ℕ) : ℝ :=
  2 * (1 + Real.log (N : ℝ))

theorem dyadicClassScale_pos {N : ℕ} (hN : 0 < N) :
    0 < dyadicClassScale N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  unfold dyadicClassScale
  positivity

theorem one_le_dyadicClassScale {N : ℕ} (hN : 0 < N) :
    1 ≤ dyadicClassScale N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  unfold dyadicClassScale
  linarith

/-- `log(N)^(3-η)` is absorbed by the spare power `N^(ε-η)`.
The displayed constant is explicit and depends only on the two exponents. -/
theorem dyadicClassScale_absorb
    {N : ℕ} {eta eps : ℝ}
    (hN : 0 < N) (heta0 : 0 ≤ eta)
    (hetaeps : eta < eps) :
    dyadicClassScale N ^ (3 - eta) * (N : ℝ) ^ (3 + eta) ≤
      (2 * (1 + 3 / (eps - eta))) ^ (3 : ℕ) *
        (N : ℝ) ^ (3 + eps) := by
  let delta : ℝ := (eps - eta) / 3
  let A : ℝ := 2 * (1 + 1 / delta)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    linarith
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpow1 : (1 : ℝ) ≤ (N : ℝ) ^ delta :=
    Real.one_le_rpow hN1 hdelta.le
  have hlog := Real.log_natCast_le_rpow_div N hdelta
  have hscale : dyadicClassScale N ≤ A * (N : ℝ) ^ delta := by
    dsimp only [dyadicClassScale, A]
    calc
      2 * (1 + Real.log (N : ℝ)) ≤
          2 * (1 + (N : ℝ) ^ delta / delta) := by
        gcongr
      _ ≤ 2 * ((1 + 1 / delta) * (N : ℝ) ^ delta) := by
        have hone : 1 + (N : ℝ) ^ delta / delta ≤
            (1 + 1 / delta) * (N : ℝ) ^ delta := by
          calc
            1 + (N : ℝ) ^ delta / delta ≤
                (N : ℝ) ^ delta + (N : ℝ) ^ delta / delta :=
              by
                simpa only [add_comm] using
                  add_le_add_right hNpow1 ((N : ℝ) ^ delta / delta)
            _ = (1 + 1 / delta) * (N : ℝ) ^ delta := by ring
        gcongr
      _ = 2 * (1 + 1 / delta) * (N : ℝ) ^ delta := by ring
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hscale0 : 0 ≤ dyadicClassScale N :=
    (dyadicClassScale_pos hN).le
  have hscalePow : dyadicClassScale N ^ (3 - eta) ≤
      dyadicClassScale N ^ (3 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (one_le_dyadicClassScale hN) (by linarith : 3 - eta ≤ (3 : ℝ))
    calc
      dyadicClassScale N ^ (3 - eta) ≤
          dyadicClassScale N ^ (3 : ℝ) := h
      _ = dyadicClassScale N ^ (3 : ℕ) := Real.rpow_natCast _ _
  have hcube : dyadicClassScale N ^ (3 : ℕ) ≤
      (A * (N : ℝ) ^ delta) ^ (3 : ℕ) :=
    pow_le_pow_left₀ hscale0 hscale 3
  have hdeltaThree : delta * 3 = eps - eta := by
    dsimp only [delta]
    ring
  have hcubeIdentity : (A * (N : ℝ) ^ delta) ^ (3 : ℕ) =
      A ^ (3 : ℕ) * (N : ℝ) ^ (eps - eta) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hNpos.le]
    congr 2
  have hclassPower : dyadicClassScale N ^ (3 - eta) ≤
      A ^ (3 : ℕ) * (N : ℝ) ^ (eps - eta) :=
    hscalePow.trans (hcube.trans_eq hcubeIdentity)
  calc
    dyadicClassScale N ^ (3 - eta) * (N : ℝ) ^ (3 + eta) ≤
        (A ^ (3 : ℕ) * (N : ℝ) ^ (eps - eta)) *
          (N : ℝ) ^ (3 + eta) :=
      mul_le_mul_of_nonneg_right hclassPower (Real.rpow_nonneg hNpos.le _)
    _ = A ^ (3 : ℕ) * (N : ℝ) ^ (3 + eps) := by
      rw [show A ^ (3 : ℕ) * (N : ℝ) ^ (eps - eta) *
          (N : ℝ) ^ (3 + eta) =
        A ^ (3 : ℕ) * ((N : ℝ) ^ (eps - eta) *
          (N : ℝ) ^ (3 + eta)) by ring]
      rw [← Real.rpow_add hNpos]
      congr 2
      ring
    _ = (2 * (1 + 3 / (eps - eta))) ^ (3 : ℕ) *
        (N : ℝ) ^ (3 + eps) := by
      congr 2
      dsimp only [A, delta]
      field_simp

/-- Non-circular output of the CDW decomposition and strip estimate for one
ordered configuration and one signed-convex partition.  The parameter `A`
is the uniform analytic constant supplied by those external estimates; it is
kept explicit rather than silently normalized to one. -/
structure TurningDyadicCertificate
    (P : OrderedConfiguration) (K : ℕ) (eta A : ℝ) where
  Index : Type
  classes : Finset Index
  mass : Index → ℕ
  layer : Index → ℝ
  layer_nonneg : ∀ i ∈ classes, 0 ≤ layer i
  sixth_root_control :
    (J3 (pointSet P) : ℝ) ^ (1 / 6 : ℝ) ≤
      A * ∑ i ∈ classes, layer i
  class_count :
    (classes.card : ℝ) ≤ dyadicClassScale (pointSet P).card
  total_mass :
    (∑ i ∈ classes, mass i) ≤ (pointSet P).card
  per_layer : ∀ i ∈ classes,
    layer i ≤ (K : ℝ) ^ (1 / 3 : ℝ) *
      (mass i : ℝ) ^ dyadicLayerExponent eta

/-- Exact external interface for CDW plus the strip estimate.  For each
admissible exponent it first supplies one nonnegative analytic constant,
uniform in `P` and `K`, and only then produces certificates for actual
signed-convex partitions.  It contains no final `J3` estimate. -/
def TurningDyadicInputs : Prop :=
  ∀ eta : ℝ, 0 < eta → eta ≤ 3 →
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (P : OrderedConfiguration) (K : ℕ),
        1 ≤ K → HasSignedConvexPartitionAtMost P K →
          (pointSet P).Nonempty →
            Nonempty (TurningDyadicCertificate P K eta A)

private theorem sixthRoot_pow_six (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (1 / 6 : ℝ)) ^ (6 : ℕ) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- The upper-bound clause of Theorem 1.4 follows from the precise dyadic
input.  The choice `eta=min(eps/2,3)` leaves a positive power which absorbs
the logarithmic class count. -/
theorem turningComplexityUpper_of_dyadicInputs
    (H : TurningDyadicInputs) : TurningComplexityUpperStatement := by
  intro eps heps
  let eta : ℝ := min (eps / 2) 3
  have hetaPos : 0 < eta := by
    dsimp only [eta]
    exact lt_min (by linarith) (by norm_num)
  have heta0 : 0 ≤ eta := hetaPos.le
  have heta3 : eta ≤ 3 := by
    dsimp only [eta]
    exact min_le_right _ _
  have hetaeps : eta < eps := by
    dsimp only [eta]
    by_cases hsmall : eps / 2 ≤ 3
    · rw [min_eq_left hsmall]
      linarith
    · rw [min_eq_right (le_of_not_ge hsmall)]
      linarith
  rcases H eta hetaPos heta3 with ⟨A, hA, hcert⟩
  let logConstant : ℝ :=
    (2 * (1 + 3 / (eps - eta))) ^ (3 : ℕ)
  let C : ℝ := A ^ (6 : ℕ) * logConstant
  have hC : 0 ≤ C := by
    dsimp only [C, logConstant]
    positivity
  refine ⟨C, hC, ?_⟩
  intro P K hK hpartition
  by_cases hP : (pointSet P).Nonempty
  · let D := Classical.choice (hcert P K hK hpartition hP)
    have hN : 0 < (pointSet P).card := hP.card_pos
    have hKpos : 0 < K := lt_of_lt_of_le (by omega) hK
    have hassembly := dyadic_assembly_sixth_power_natMass
      D.classes D.layer D.mass heta0 heta3 D.layer_nonneg hKpos
      (dyadicClassScale_pos hN) hN D.class_count D.total_mass D.per_layer
    have hrootPower : (J3 (pointSet P) : ℝ) ≤
        (A * ∑ i ∈ D.classes, D.layer i) ^ (6 : ℕ) := by
      calc
        (J3 (pointSet P) : ℝ) =
            ((J3 (pointSet P) : ℝ) ^ (1 / 6 : ℝ)) ^ (6 : ℕ) :=
          (sixthRoot_pow_six _ (by positivity)).symm
        _ ≤ (A * ∑ i ∈ D.classes, D.layer i) ^ (6 : ℕ) :=
          pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _)
            D.sixth_root_control 6
    have habsorb :
        dyadicClassScale (pointSet P).card ^ (3 - eta) *
            ((pointSet P).card : ℝ) ^ (3 + eta) ≤
          logConstant * ((pointSet P).card : ℝ) ^ (3 + eps) := by
      simpa only [logConstant] using
        (dyadicClassScale_absorb hN heta0 hetaeps)
    calc
      (J3 (pointSet P) : ℝ) ≤
          (A * ∑ i ∈ D.classes, D.layer i) ^ (6 : ℕ) := hrootPower
      _ = A ^ (6 : ℕ) *
          (∑ i ∈ D.classes, D.layer i) ^ (6 : ℕ) := by
        rw [mul_pow]
      _ ≤ A ^ (6 : ℕ) *
          ((K : ℝ) ^ (2 : ℕ) *
            dyadicClassScale (pointSet P).card ^ (3 - eta) *
            ((pointSet P).card : ℝ) ^ (3 + eta)) :=
        mul_le_mul_of_nonneg_left hassembly (pow_nonneg hA 6)
      _ = A ^ (6 : ℕ) * (K : ℝ) ^ (2 : ℕ) *
          (dyadicClassScale (pointSet P).card ^ (3 - eta) *
            ((pointSet P).card : ℝ) ^ (3 + eta)) := by ring
      _ ≤ A ^ (6 : ℕ) * (K : ℝ) ^ (2 : ℕ) *
          (logConstant * ((pointSet P).card : ℝ) ^ (3 + eps)) := by
        exact mul_le_mul_of_nonneg_left habsorb (by positivity)
      _ = C * (K : ℝ) ^ 2 *
          ((pointSet P).card : ℝ) ^ (3 + eps) := by
        dsimp only [C]
        ring
  · have hEmpty : pointSet P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    rw [hEmpty]
    have hexp : 0 < 3 + eps := by linarith
    simp [J3, j3Witnesses, tripleProduct, Real.zero_rpow hexp.ne']

end

end ComplexitySensitiveEnergy.Turning
