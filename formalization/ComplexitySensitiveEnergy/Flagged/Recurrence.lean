import ComplexitySensitiveEnergy.Flagged.LocalInterpolation

/-!
# Numerical closure of the two induction recurrences

These lemmas isolate the algebra which closes the dimension/cardinality
inductions in Theorems 1.1 and 1.2.  Geometry supplies the step estimate;
Lean checks the contraction and absorption arithmetic.
-/

namespace ComplexitySensitiveEnergy

/-- A normalized strong-induction recurrence with contraction factor
`rho < 1` is uniformly bounded by `base / (1-rho)`. -/
theorem close_contractive_strong_induction
    {u : ℕ → ℝ} {base rho : ℝ}
    (_hbase : 0 ≤ base) (_hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hstep : ∀ n : ℕ,
      (∀ m < n, u m ≤ base / (1 - rho)) →
        u n ≤ base + rho * (base / (1 - rho))) :
    ∀ n : ℕ, u n ≤ base / (1 - rho) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hn := hstep n ih
      have hden : 0 < 1 - rho := sub_pos.mpr hrho1
      have hident : (1 - rho) * (base / (1 - rho)) = base := by
        field_simp
      nlinarith

/-- Explicit form of the `M^eps` absorption step: once the missing power
dominates the fixed coefficient, a lower-order term enters the target. -/
theorem absorb_missing_power
    {coefficient fraction M a eps : ℝ}
    (hM : 0 < M) (hcoeff : coefficient ≤ fraction * M ^ eps)
    (_hfrac : 0 ≤ fraction) :
    coefficient * M ^ a ≤ fraction * M ^ (a + eps) := by
  have hpow : 0 ≤ M ^ a := Real.rpow_nonneg hM.le _
  calc
    coefficient * M ^ a ≤ (fraction * M ^ eps) * M ^ a := by
      exact mul_le_mul_of_nonneg_right hcoeff hpow
    _ = fraction * M ^ (a + eps) := by
      rw [Real.rpow_add hM]
      ring

/-- The worse-intrinsic-exponent wall estimate (3.18), stated with all side
conditions. -/
theorem worse_wall_energy_scale
    {B Lambda a : ℝ}
    (hB : 1 ≤ B) (hBLambda : B ≤ Lambda)
    (ha2 : 2 ≤ a) (ha3 : a ≤ 3) :
    B ^ (3 : ℕ) ≤ Lambda ^ (3 - a) * B ^ a := by
  simpa [pow_succ, mul_assoc] using
    (local_lambda_to_global
      (lambda := B) (Lambda := Lambda) (M := B) (a := a)
      hB le_rfl hBLambda ha2 ha3)

/-- The elementary fourth-power inequality behind the factor `8` when a set
is split into a cell part and a wall part. -/
theorem add_pow_four_le_eight (x y : ℝ) :
    (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have h1 : 0 ≤ (x - y) ^ 4 := by positivity
  have h2 : 0 ≤ 6 * (x ^ 2 - y ^ 2) ^ 2 := by positivity
  nlinarith [h1, h2]

end ComplexitySensitiveEnergy
