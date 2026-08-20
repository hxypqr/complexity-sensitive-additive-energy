import Mathlib

/-!
# The interpolation exponent in the strip estimate

This file checks the numerical calculation in the proof of the `L⁶` strip
projection lemma.  The interpolation parameter is determined by

`1 / 6 = (1 - θ) / 2 + θ / r`, with `r > 6`.

Solving this equation and substituting into the power of the number of strips
gives

`6 * θ * (1 - 1 / r) = 4 + 4 / (r - 2)`.
-/

namespace ComplexitySensitiveEnergy
namespace Turning

/-- The interpolation parameter between the `L²` and `Lʳ` strip bounds. -/
noncomputable def stripTheta (r : ℝ) : ℝ :=
  2 * r / (3 * (r - 2))

/-- The explicit parameter satisfies the interpolation equation. -/
theorem stripTheta_interpolation {r : ℝ} (hr : 6 < r) :
    (1 : ℝ) / 6 = (1 - stripTheta r) / 2 + stripTheta r / r := by
  have hr0 : r ≠ 0 := by linarith
  have hr2 : r - 2 ≠ 0 := by linarith
  rw [stripTheta]
  field_simp [hr0, hr2]
  ring

/-- The interpolation equation uniquely determines `θ` when `r > 6`. -/
theorem theta_eq_stripTheta {r θ : ℝ} (hr : 6 < r)
    (hθ : (1 : ℝ) / 6 = (1 - θ) / 2 + θ / r) :
    θ = stripTheta r := by
  have hr0 : r ≠ 0 := by linarith
  have hr2 : r - 2 ≠ 0 := by linarith
  field_simp [hr0] at hθ
  rw [stripTheta]
  field_simp [hr2]
  nlinarith

/-- The explicit strip exponent calculation. -/
theorem stripTheta_exponent {r : ℝ} (hr : 6 < r) :
    6 * stripTheta r * (1 - 1 / r) = 4 + 4 / (r - 2) := by
  have hr0 : r ≠ 0 := by linarith
  have hr2 : r - 2 ≠ 0 := by linarith
  rw [stripTheta]
  field_simp [hr0, hr2]
  ring

/-- The form used directly after interpolation: no explicit formula for `θ`
is assumed, only its defining equation. -/
theorem strip_exponent_identity_of_interpolation {r θ : ℝ} (hr : 6 < r)
    (hθ : (1 : ℝ) / 6 = (1 - θ) / 2 + θ / r) :
    6 * θ * (1 - 1 / r) = 4 + 4 / (r - 2) := by
  rw [theta_eq_stripTheta hr hθ]
  exact stripTheta_exponent hr

/-- Once `r` makes the remainder smaller than `δ`, the sixth-power strip
exponent is strictly smaller than `4 + δ`. -/
theorem strip_exponent_lt_four_add {r θ δ : ℝ} (hr : 6 < r)
    (hθ : (1 : ℝ) / 6 = (1 - θ) / 2 + θ / r)
    (hremainder : 4 / (r - 2) < δ) :
    6 * θ * (1 - 1 / r) < 4 + δ := by
  rw [strip_exponent_identity_of_interpolation hr hθ]
  linarith

end Turning
end ComplexitySensitiveEnergy
