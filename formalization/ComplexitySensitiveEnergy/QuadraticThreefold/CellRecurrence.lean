import ComplexitySensitiveEnergy.Flagged.Recurrence

/-!
# Cellular numerical recurrence for Theorem 1.2

Geometry supplies cell sizes and the two-crossing estimate.  This file proves
the power-sum step which turns `|X_i| <= M` and `∑|X_i| <= N` into the
contractive cellular contribution at exponent `2+eps`.
-/

namespace ComplexitySensitiveEnergy.QuadraticThreefold

open scoped BigOperators

noncomputable section

theorem rpow_two_add_eq_mul_rpow_one_add
    {x eps : ℝ} (hx : 0 ≤ x) (heps : 0 < eps) :
    x ^ (2 + eps) = x * x ^ (1 + eps) := by
  by_cases hx0 : x = 0
  · subst x
    simp [ne_of_gt (by linarith : 0 < 2 + eps),
      ne_of_gt (by linarith : 0 < 1 + eps)]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [show 2 + eps = 1 + (1 + eps) by ring,
      Real.rpow_add hxpos, Real.rpow_one]

/-- Finite power-sum estimate used in (4.15). -/
theorem sum_rpow_two_add_eps_le
    {ι : Type*} (cells : Finset ι) (mass : ι → ℝ)
    {M N eps : ℝ}
    (heps : 0 < eps)
    (hM : 0 ≤ M)
    (hmass : ∀ i ∈ cells, 0 ≤ mass i)
    (hcell : ∀ i ∈ cells, mass i ≤ M)
    (htotal : (∑ i ∈ cells, mass i) ≤ N) :
    (∑ i ∈ cells, mass i ^ (2 + eps)) ≤
      M ^ (1 + eps) * N := by
  calc
    (∑ i ∈ cells, mass i ^ (2 + eps)) =
        ∑ i ∈ cells, mass i * mass i ^ (1 + eps) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact rpow_two_add_eq_mul_rpow_one_add (hmass i hi) heps
    _ ≤ ∑ i ∈ cells, mass i * M ^ (1 + eps) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hmass i hi) (hcell i hi) (by linarith))
        (hmass i hi)
    _ = ∑ i ∈ cells, M ^ (1 + eps) * mass i := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = M ^ (1 + eps) * ∑ i ∈ cells, mass i := by
      rw [Finset.mul_sum]
    _ ≤ M ^ (1 + eps) * N :=
      mul_le_mul_of_nonneg_left htotal (Real.rpow_nonneg hM _)

/-- Insert inductive energy estimates into the cellular power sum. -/
theorem cellular_energy_sum_le
    {ι : Type*} (cells : Finset ι) (mass energyValue : ι → ℝ)
    {C M N eps : ℝ}
    (heps : 0 < eps) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hmass : ∀ i ∈ cells, 0 ≤ mass i)
    (hcell : ∀ i ∈ cells, mass i ≤ M)
    (htotal : (∑ i ∈ cells, mass i) ≤ N)
    (hinduction : ∀ i ∈ cells,
      energyValue i ≤ C * mass i ^ (2 + eps)) :
    (∑ i ∈ cells, energyValue i) ≤
      C * (M ^ (1 + eps) * N) := by
  calc
    (∑ i ∈ cells, energyValue i) ≤
        ∑ i ∈ cells, C * mass i ^ (2 + eps) :=
      Finset.sum_le_sum hinduction
    _ = C * ∑ i ∈ cells, mass i ^ (2 + eps) := by
      rw [Finset.mul_sum]
    _ ≤ C * (M ^ (1 + eps) * N) :=
      mul_le_mul_of_nonneg_left
        (sum_rpow_two_add_eps_le cells mass heps hM hmass hcell htotal) hC

/-- Exact exponent algebra behind the factor `D^(-1-3 eps)` in (4.15). -/
theorem threefold_cell_scale_identity
    {D N eps : ℝ} (hD : 0 < D) (hN : 0 < N) :
    D ^ (2 : ℝ) * (N / D ^ (3 : ℕ)) ^ (1 + eps) * N =
      D ^ (-1 - 3 * eps) * N ^ (2 + eps) := by
  have hD0 : 0 ≤ D := hD.le
  have hN0 : 0 ≤ N := hN.le
  have hD3 : 0 ≤ D ^ (3 : ℕ) := by positivity
  have hden : (D ^ (3 : ℕ)) ^ (1 + eps) =
      D ^ (3 * (1 + eps)) := by
    calc
      (D ^ (3 : ℕ)) ^ (1 + eps) =
          (D ^ (3 : ℝ)) ^ (1 + eps) := by
        congr 1
        exact (Real.rpow_natCast D 3).symm
      _ = D ^ (3 * (1 + eps)) :=
        (Real.rpow_mul hD0 3 (1 + eps)).symm
  have hNjoin : N ^ (1 + eps) * N = N ^ ((1 + eps) + 1) := by
    calc
      N ^ (1 + eps) * N = N ^ (1 + eps) * N ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = N ^ ((1 + eps) + 1) :=
        (Real.rpow_add hN (1 + eps) 1).symm
  rw [Real.div_rpow hN0 hD3, hden]
  calc
    D ^ (2 : ℝ) * (N ^ (1 + eps) / D ^ (3 * (1 + eps))) * N =
        (D ^ (2 : ℝ) / D ^ (3 * (1 + eps))) *
          (N ^ (1 + eps) * N) := by ring
    _ = D ^ ((2 : ℝ) - 3 * (1 + eps)) *
          N ^ ((1 + eps) + 1) := by
      rw [Real.rpow_sub hD, hNjoin]
    _ = D ^ (-1 - 3 * eps) * N ^ (2 + eps) := by
      congr 1 <;> ring_nf

end

end ComplexitySensitiveEnergy.QuadraticThreefold
