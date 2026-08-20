import ComplexitySensitiveEnergy.Additive.Diagonal
import ComplexitySensitiveEnergy.QuadraticThreefold.Definitions
import ComplexitySensitiveEnergy.QuadraticThreefold.Main

/-!
# The unconditional sharpness half of Theorem 1.2

The upper estimate in Theorem 1.2 uses the geometry of the quadratic
threefold and is intentionally not assumed here.  Its sharpness clause is the
universal two-diagonal contribution to additive energy, so it holds for every
finite subset of the ambient space `R5`, independently of whether the set lies
on a quadratic graph.
-/

namespace ComplexitySensitiveEnergy.QuadraticThreefold

/-- Sharpness half of Theorem 1.2, with no upper-bound hypothesis. -/
theorem theorem12_sharpness :
    ∀ X : Finset R5, 2 * X.card ^ 2 - X.card ≤ energy X := by
  intro X
  exact two_mul_card_sq_sub_card_le_energy X

/-- Once the geometric upper estimate has been supplied, the sharpness half
is discharged entirely by the internal diagonal count. -/
theorem theorem12_of_upper (hupper : QuadraticThreefoldEnergyStatement) :
    Theorem12Statement :=
  ⟨hupper, theorem12_sharpness⟩

/-- Paper-facing Theorem 1.2 from the explicit non-circular recurrence
certificate family. -/
theorem theorem12_of_recurrenceInputs (H : ThreefoldRecurrenceInputs) :
    Theorem12Statement :=
  theorem12_of_upper (quadraticThreefoldEnergy_of_recurrenceInputs H)

/-- Paper-facing Theorem 1.2 from the granular recurrence interface.  Along
this route the cellular estimate (Proposition 4.5) is reconstructed from the
two active-support bounds, the internal mixed rearrangement and two finite
Cauchy--Schwarz steps, and the rank-drop Gram certificate. -/
theorem theorem12_of_granularRecurrenceInputs
    (H : GranularThreefoldRecurrenceInputs) :
    Theorem12Statement :=
  theorem12_of_upper
    (quadraticThreefoldEnergy_of_granularRecurrenceInputs H)

end ComplexitySensitiveEnergy.QuadraticThreefold
