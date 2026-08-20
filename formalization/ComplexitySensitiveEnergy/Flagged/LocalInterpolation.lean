import Mathlib

/-!
# Correct local-to-global interpolation in Theorem 1.1

The manuscript's displayed inequality (3.6) is valid for the node-local
parameter `lambda ≤ M`, not for the global flag parameter, which can exceed
the node size.  This file proves the corrected two-stage inequality.
-/

namespace ComplexitySensitiveEnergy

/-- Equation (3.6), with the required local side condition `lambda ≤ M`. -/
theorem local_lambda_interpolation
    {lambda M a : ℝ}
    (hlambda : 1 ≤ lambda) (hlambdaM : lambda ≤ M)
    (ha2 : 2 ≤ a) (_ha3 : a ≤ 3) :
    lambda * M ^ (2 : ℕ) ≤ lambda ^ (3 - a) * M ^ a := by
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambda
  have hMPos : 0 < M := hlambdaPos.trans_le hlambdaM
  have hexp : 0 ≤ a - 2 := sub_nonneg.mpr ha2
  have hpow : lambda ^ (a - 2) ≤ M ^ (a - 2) :=
    Real.rpow_le_rpow hlambdaPos.le hlambdaM hexp
  have hleft : lambda ^ (3 - a) * lambda ^ (a - 2) = lambda := by
    rw [← Real.rpow_add hlambdaPos]
    norm_num
  have hright : M ^ (a - 2) * M ^ (2 : ℕ) = M ^ a := by
    rw [← Real.rpow_natCast M 2, ← Real.rpow_add hMPos]
    congr 1
    ring
  have hnonneg : 0 ≤ lambda ^ (3 - a) :=
    Real.rpow_nonneg hlambdaPos.le _
  calc
    lambda * M ^ (2 : ℕ) =
        (lambda ^ (3 - a) * lambda ^ (a - 2)) * M ^ (2 : ℕ) := by
          rw [hleft]
    _ ≤ (lambda ^ (3 - a) * M ^ (a - 2)) * M ^ (2 : ℕ) := by
          gcongr
    _ = lambda ^ (3 - a) * M ^ a := by
          rw [← hright]
          ring

/-- Correct passage from the node-local parameter to the global flag bound:
first use `lambda ≤ M`, then monotonicity `lambda ≤ Lambda` with the
nonnegative exponent `3-a`. -/
theorem local_lambda_to_global
    {lambda Lambda M a : ℝ}
    (hlambda : 1 ≤ lambda) (hlambdaM : lambda ≤ M)
    (hlambdaGlobal : lambda ≤ Lambda)
    (ha2 : 2 ≤ a) (ha3 : a ≤ 3) :
    lambda * M ^ (2 : ℕ) ≤ Lambda ^ (3 - a) * M ^ a := by
  have hlambdaNonneg : 0 ≤ lambda := (zero_lt_one.trans_le hlambda).le
  have hMNonneg : 0 ≤ M := hlambdaNonneg.trans hlambdaM
  have hexp : 0 ≤ 3 - a := sub_nonneg.mpr ha3
  calc
    lambda * M ^ (2 : ℕ) ≤ lambda ^ (3 - a) * M ^ a :=
      local_lambda_interpolation hlambda hlambdaM ha2 ha3
    _ ≤ Lambda ^ (3 - a) * M ^ a := by
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hlambdaNonneg hlambdaGlobal hexp)
        (Real.rpow_nonneg hMNonneg a)

/-- The cellular power of the partition degree is at most `-k*eps`, the
algebraic calculation in (3.16). -/
theorem cell_contraction_exponent
    {k sigma : ℕ} {a eps : ℝ}
    (hk : 0 < k)
    (ha : 1 + 2 * (sigma : ℝ) / (k : ℝ) ≤ a) :
    2 * (sigma : ℝ) - (k : ℝ) * (a + eps - 1) ≤
      -(k : ℝ) * eps := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hmul := (mul_le_mul_of_nonneg_left ha hkR.le)
  field_simp at hmul
  nlinarith

/-- The exponent calculation in the threefold recurrence (4.15). -/
theorem threefold_cell_exponent (eps : ℝ) :
    2 - 3 * (1 + eps) = -1 - 3 * eps := by
  ring

end ComplexitySensitiveEnergy
