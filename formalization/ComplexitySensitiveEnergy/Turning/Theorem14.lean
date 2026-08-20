import ComplexitySensitiveEnergy.Turning.Main
import ComplexitySensitiveEnergy.Turning.PacketExample

/-!
# Certified assembly of Theorem 1.4

The upper half is the non-circular dyadic verifier from `Turning.Main`.
The lower half uses the fully internal reset-packet construction, its exact
minimal turning complexity, and its explicit third-energy bounds.
-/

namespace ComplexitySensitiveEnergy.Turning

/-- The complete paper-facing Theorem 1.4.  Only the CDW/strip dyadic input
for the upper bound remains external; the sharp packet examples are proved
internally. -/
theorem theorem14_of_dyadicInputs
    (H : TurningDyadicInputs) : Theorem14Statement := by
  constructor
  · exact turningComplexityUpper_of_dyadicInputs H
  · refine ⟨(1 / 3125 : ℝ), 6, by norm_num, by norm_num, ?_⟩
    intro K n hK hn
    let P := resetPacketConfiguration 4 K n
    have hdata := resetPacketConfiguration_sharpness_data
      (B := 4) (K := K) (n := n) (by norm_num) (by omega)
    rcases hdata with ⟨hcard, hkData, hlower, hupper⟩
    rcases hkData with ⟨k, hk, _hhalf, hKtwo, hkK⟩
    refine ⟨P, hcard, ⟨k, hk, ?_, ?_⟩, ?_, ?_⟩
    · have hKtwoR : (K : ℝ) ≤ 2 * (k : ℝ) := by
        exact_mod_cast hKtwo
      nlinarith
    · have hkKR : (k : ℝ) ≤ K := by exact_mod_cast hkK
      have hK0 : (0 : ℝ) ≤ K := by positivity
      nlinarith
    · have hlowerR :
          ((K ^ 2 * (K * n) ^ 3 : ℕ) : ℝ) ≤
            3125 * (J3 (pointSet P) : ℝ) := by
        exact_mod_cast hlower
      calc
        (1 / 3125 : ℝ) * (K : ℝ) ^ 2 *
            ((pointSet P).card : ℝ) ^ 3 =
            (1 / 3125 : ℝ) *
              ((K ^ 2 * (K * n) ^ 3 : ℕ) : ℝ) := by
          rw [hcard]
          norm_num [Nat.cast_mul, Nat.cast_pow]
          ring
        _ ≤ (1 / 3125 : ℝ) *
            (3125 * (J3 (pointSet P) : ℝ)) :=
          mul_le_mul_of_nonneg_left hlowerR (by norm_num)
        _ = (J3 (pointSet P) : ℝ) := by ring
    · have hupperR :
          (J3 (pointSet P) : ℝ) ≤
            6 * ((K ^ 2 * (K * n) ^ 3 : ℕ) : ℝ) := by
        exact_mod_cast hupper
      calc
        (J3 (pointSet P) : ℝ) ≤
            6 * ((K ^ 2 * (K * n) ^ 3 : ℕ) : ℝ) := hupperR
        _ = (6 : ℝ) * (K : ℝ) ^ 2 *
            ((pointSet P).card : ℝ) ^ 3 := by
          rw [hcard]
          norm_num [Nat.cast_mul, Nat.cast_pow]
          ring

end ComplexitySensitiveEnergy.Turning
