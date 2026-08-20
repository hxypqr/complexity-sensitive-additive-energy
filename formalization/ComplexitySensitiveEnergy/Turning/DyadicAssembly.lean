import Mathlib

/-!
# Numerical dyadic assembly for the turning-complexity theorem

This file contains the finite numerical step at the end of the proof of the
turning-complexity theorem.  The analytic and geometric inputs have already
produced one nonnegative quantity per nonempty dyadic class.  If

`layer r ≤ K^(1/3) * mass r^(1/2 + η/6)`,

the number of classes is at most `L`, and their total mass is at most `N`, then
the sixth power of their sum is at most

`K^2 * L^(3 - η) * N^(3 + η)`.

The proof includes the finite Hölder/Jensen step rather than taking it as an
additional hypothesis.
-/

namespace ComplexitySensitiveEnergy
namespace Turning

open scoped BigOperators

noncomputable section

/-- The exponent of the mass of one dyadic class. -/
def dyadicLayerExponent (η : ℝ) : ℝ :=
  1 / 2 + η / 6

@[simp]
theorem six_mul_dyadicLayerExponent (η : ℝ) :
    6 * dyadicLayerExponent η = 3 + η := by
  unfold dyadicLayerExponent
  ring

@[simp]
theorem six_mul_one_sub_dyadicLayerExponent (η : ℝ) :
    6 * (1 - dyadicLayerExponent η) = 3 - η := by
  unfold dyadicLayerExponent
  ring

/-- Finite concave-power estimate with an upper bound `L` for the number of
summands.  This is the Hölder step in the dyadic class index. -/
theorem sum_rpow_le_layerCount_mul_sum_rpow
    {ι : Type*} (classes : Finset ι) (mass : ι → ℝ) {a L : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hmass : ∀ i ∈ classes, 0 ≤ mass i)
    (hL : 0 < L) (hcard : (classes.card : ℝ) ≤ L) :
    (∑ i ∈ classes, mass i ^ a) ≤
      L ^ (1 - a) * (∑ i ∈ classes, mass i) ^ a := by
  have hL0 : L ≠ 0 := hL.ne'
  have hinvL : 0 ≤ L⁻¹ := inv_nonneg.mpr hL.le
  have hv : 0 ≤ 1 - (classes.card : ℝ) * L⁻¹ := by
    rw [sub_nonneg]
    calc
      (classes.card : ℝ) * L⁻¹ ≤ L * L⁻¹ :=
        mul_le_mul_of_nonneg_right hcard hinvL
      _ = 1 := mul_inv_cancel₀ hL0
  have hweights :
      1 - (classes.card : ℝ) * L⁻¹ +
          ∑ _i ∈ classes, L⁻¹ = 1 := by
    simp [nsmul_eq_mul]
  have hJensen :=
    (Real.concaveOn_rpow ha0.le ha1).map_add_sum_le
      (t := classes) (w := fun _ ↦ L⁻¹) (p := mass)
      (v := 1 - (classes.card : ℝ) * L⁻¹) (q := 0)
      (fun _ _ ↦ hinvL) hweights
      (fun i hi ↦ hmass i hi) hv (by simp)
  have hscaled :
      L⁻¹ * (∑ i ∈ classes, mass i ^ a) ≤
        (L⁻¹ * ∑ i ∈ classes, mass i) ^ a := by
    simpa [smul_eq_mul, Finset.mul_sum, ha0.ne'] using hJensen
  have hsum_nonneg : 0 ≤ ∑ i ∈ classes, mass i :=
    Finset.sum_nonneg hmass
  calc
    (∑ i ∈ classes, mass i ^ a)
        = L * (L⁻¹ * ∑ i ∈ classes, mass i ^ a) := by
            field_simp [hL0]
    _ ≤ L * (L⁻¹ * ∑ i ∈ classes, mass i) ^ a :=
          mul_le_mul_of_nonneg_left hscaled hL.le
    _ = L ^ (1 - a) * (∑ i ∈ classes, mass i) ^ a := by
          rw [Real.mul_rpow hinvL hsum_nonneg, Real.inv_rpow hL.le]
          rw [Real.rpow_sub hL 1 a]
          simp [div_eq_mul_inv]
          ring

/-- Sum the per-class estimates before taking the sixth power. -/
theorem dyadic_sum_le
    {ι : Type*} (classes : Finset ι) (layer mass : ι → ℝ)
    {a K L N : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hmass : ∀ i ∈ classes, 0 ≤ mass i)
    (hK : 0 < K) (hL : 0 < L)
    (hclass : (classes.card : ℝ) ≤ L)
    (htotal : (∑ i ∈ classes, mass i) ≤ N)
    (hperLayer : ∀ i ∈ classes, layer i ≤ K ^ (1 / 3 : ℝ) * mass i ^ a) :
    (∑ i ∈ classes, layer i) ≤
      K ^ (1 / 3 : ℝ) * L ^ (1 - a) * N ^ a := by
  have hclasses :=
    sum_rpow_le_layerCount_mul_sum_rpow classes mass ha0 ha1 hmass hL hclass
  calc
    (∑ i ∈ classes, layer i)
        ≤ ∑ i ∈ classes, K ^ (1 / 3 : ℝ) * mass i ^ a :=
          Finset.sum_le_sum hperLayer
    _ = K ^ (1 / 3 : ℝ) * (∑ i ∈ classes, mass i ^ a) := by
          rw [Finset.mul_sum]
    _ ≤ K ^ (1 / 3 : ℝ) *
          (L ^ (1 - a) * (∑ i ∈ classes, mass i) ^ a) :=
          mul_le_mul_of_nonneg_left hclasses (Real.rpow_nonneg hK.le _)
    _ ≤ K ^ (1 / 3 : ℝ) * (L ^ (1 - a) * N ^ a) := by
          have hmassPow :
              (∑ i ∈ classes, mass i) ^ a ≤ N ^ a :=
            Real.rpow_le_rpow (Finset.sum_nonneg hmass) htotal ha0.le
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmassPow (Real.rpow_nonneg hL.le _))
            (Real.rpow_nonneg hK.le _)
    _ = K ^ (1 / 3 : ℝ) * L ^ (1 - a) * N ^ a := by ring

/-- The generic sixth-power dyadic assembly inequality. -/
theorem dyadic_sixth_power_le
    {ι : Type*} (classes : Finset ι) (layer mass : ι → ℝ)
    {a K L N : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hlayer : ∀ i ∈ classes, 0 ≤ layer i)
    (hmass : ∀ i ∈ classes, 0 ≤ mass i)
    (hK : 0 < K) (hL : 0 < L) (hN : 0 < N)
    (hclass : (classes.card : ℝ) ≤ L)
    (htotal : (∑ i ∈ classes, mass i) ≤ N)
    (hperLayer : ∀ i ∈ classes, layer i ≤ K ^ (1 / 3 : ℝ) * mass i ^ a) :
    (∑ i ∈ classes, layer i) ^ 6 ≤
      K ^ 2 * L ^ ((1 - a) * 6) * N ^ (a * 6) := by
  have hsum := dyadic_sum_le classes layer mass ha0 ha1 hmass
    hK hL hclass htotal hperLayer
  have hpow :
      (∑ i ∈ classes, layer i) ^ 6 ≤
        (K ^ (1 / 3 : ℝ) * L ^ (1 - a) * N ^ a) ^ 6 :=
    pow_le_pow_left₀ (Finset.sum_nonneg hlayer) hsum 6
  calc
    (∑ i ∈ classes, layer i) ^ 6
        ≤ (K ^ (1 / 3 : ℝ) * L ^ (1 - a) * N ^ a) ^ 6 := hpow
    _ = K ^ 2 * L ^ ((1 - a) * 6) * N ^ (a * 6) := by
          rw [mul_pow, mul_pow]
          rw [← Real.rpow_mul_natCast hK.le, ← Real.rpow_mul_natCast hL.le,
            ← Real.rpow_mul_natCast hN.le]
          norm_num

/-- The exponent-specialized numerical conclusion used in Theorem 1.4. -/
theorem dyadic_assembly_sixth_power
    {ι : Type*} (classes : Finset ι) (layer mass : ι → ℝ)
    {η K L N : ℝ}
    (hη0 : 0 ≤ η) (hη3 : η ≤ 3)
    (hlayer : ∀ i ∈ classes, 0 ≤ layer i)
    (hmass : ∀ i ∈ classes, 0 ≤ mass i)
    (hK : 0 < K) (hL : 0 < L) (hN : 0 < N)
    (hclass : (classes.card : ℝ) ≤ L)
    (htotal : (∑ i ∈ classes, mass i) ≤ N)
    (hperLayer : ∀ i ∈ classes,
      layer i ≤ K ^ (1 / 3 : ℝ) * mass i ^ dyadicLayerExponent η) :
    (∑ i ∈ classes, layer i) ^ 6 ≤
      K ^ 2 * L ^ (3 - η) * N ^ (3 + η) := by
  have ha0 : 0 < dyadicLayerExponent η := by
    unfold dyadicLayerExponent
    linarith
  have ha1 : dyadicLayerExponent η ≤ 1 := by
    unfold dyadicLayerExponent
    linarith
  have h := dyadic_sixth_power_le classes layer mass ha0 ha1 hlayer hmass
    hK hL hN hclass htotal hperLayer
  have hcountExponent : (1 - dyadicLayerExponent η) * 6 = 3 - η := by
    unfold dyadicLayerExponent
    ring
  have hmassExponent : dyadicLayerExponent η * 6 = 3 + η := by
    unfold dyadicLayerExponent
    ring
  rw [hcountExponent, hmassExponent] at h
  exact h

/-- The same assembly statement with the dyadic masses, the total mass, and
the number of signed-convex blocks supplied as natural numbers. -/
theorem dyadic_assembly_sixth_power_natMass
    {ι : Type*} (classes : Finset ι) (layer : ι → ℝ) (mass : ι → ℕ)
    {η L : ℝ} {K N : ℕ}
    (hη0 : 0 ≤ η) (hη3 : η ≤ 3)
    (hlayer : ∀ i ∈ classes, 0 ≤ layer i)
    (hK : 0 < K) (hL : 0 < L) (hN : 0 < N)
    (hclass : (classes.card : ℝ) ≤ L)
    (htotal : (∑ i ∈ classes, mass i) ≤ N)
    (hperLayer : ∀ i ∈ classes,
      layer i ≤ (K : ℝ) ^ (1 / 3 : ℝ) *
        (mass i : ℝ) ^ dyadicLayerExponent η) :
    (∑ i ∈ classes, layer i) ^ 6 ≤
      (K : ℝ) ^ 2 * L ^ (3 - η) * (N : ℝ) ^ (3 + η) := by
  apply dyadic_assembly_sixth_power classes layer (fun i ↦ (mass i : ℝ))
      hη0 hη3 hlayer
  · intro i hi
    positivity
  · exact_mod_cast hK
  · exact hL
  · exact_mod_cast hN
  · exact hclass
  · exact_mod_cast htotal
  · exact hperLayer

end

end Turning
end ComplexitySensitiveEnergy
