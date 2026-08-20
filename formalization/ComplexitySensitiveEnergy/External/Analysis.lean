import Mathlib
import ComplexitySensitiveEnergy.Weighted.Correlation

/-!
# Standard analytic inputs

The paper calls Plancherel/Fourier realization, bilinear complex
interpolation, interval-projection bounds from the Hilbert transform, and a
small Fourier thickening.  These are not new arguments of the paper.  This
file records the two interfaces used by the formal proof; it asserts no
global axiom.

The finite convolution interface below is literal, so the interpolation
statement cannot accidentally be read as a theorem about a different
operation or about normalized counting measure.
-/

open scoped BigOperators Pointwise

namespace ComplexitySensitiveEnergy.External

noncomputable section

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Unnormalized counting-measure `ℓᵖ` norm on a displayed finite support. -/
def finiteLpNorm (p : ℝ) (A : Finset G) (f : G → ℂ) : ℝ :=
  (∑ x ∈ A, ‖f x‖ ^ p) ^ (1 / p)

/-- Ordinary (not cyclic) convolution of two functions restricted to the
displayed finite supports. -/
def finiteConvolution (A B : Finset G) (f g : G → ℂ) (z : G) : ℂ :=
  ∑ x ∈ A, if z - x ∈ B then f x * g (z - x) else 0

/-- A support-restricted counting-measure convolution estimate. -/
def ConvolutionBound (A B : Finset G) (p q C : ℝ) : Prop :=
  1 ≤ p ∧ 1 ≤ q ∧ 0 ≤ C ∧
  ∀ f g : G → ℂ,
    finiteLpNorm 2 (A + B) (finiteConvolution A B f g) ≤
      C * finiteLpNorm p A f * finiteLpNorm q B g

/-- Paper-specific alpha-two form of bilinear complex interpolation.

The three vertices are the geometric `(2,2)` endpoint and the classical
Young endpoints `(1,2)` and `(2,1)`.  Constants interpolate geometrically.
This is the exact external step used in Theorem 1.3. -/
def AlphaTwoBilinearInterpolationStatement : Prop :=
  ∀ (G : Type) (_ : AddCommGroup G) (_ : DecidableEq G)
    (A B : Finset G) (C₀ C₁ C₂ : ℝ),
    ConvolutionBound A B 2 2 C₀ →
    ConvolutionBound A B 1 2 C₁ →
    ConvolutionBound A B 2 1 C₂ →
    ∀ theta₀ theta₁ theta₂ p q : ℝ,
      0 ≤ theta₀ → 0 ≤ theta₁ → 0 ≤ theta₂ →
      theta₀ + theta₁ + theta₂ = 1 →
      1 / p = theta₀ / 2 + theta₁ + theta₂ / 2 →
      1 / q = theta₀ / 2 + theta₁ / 2 + theta₂ →
      ConvolutionBound A B p q
        (C₀ ^ theta₀ * C₁ ^ theta₁ * C₂ ^ theta₂)

/-- Abstract Fourier realization needed after the internal phase majorant.
It says precisely that the fourth power of the Fourier `L⁴` norm is the
finite squared-correlation sum and that this fourth-root functional obeys
the triangle inequality.  Separating these fields prevents the manuscript's
indicator-to-complex gap from being hidden here: phase control is proved in
`Weighted.Correlation`. -/
structure FourierFourthNormInput (G : Type*) [AddCommGroup G]
    [DecidableEq G] where
  fourthNorm : Finset G → (G → ℂ) → ℝ
  nonnegative : ∀ A f, 0 ≤ fourthNorm A f
  correlation_identity : ∀ A f,
    fourthNorm A f ^ 4 = weightedCorrelationSquareSum A f
  triangle : ∀ A (f g : G → ℂ),
    fourthNorm A (f + g) ≤ fourthNorm A f + fourthNorm A g
  supported_ext : ∀ A (f g : G → ℂ),
    (∀ x ∈ A, f x = g x) → fourthNorm A f = fourthNorm A g

/-- Semantic data of a finite `L⁶` family with pairwise disjoint
one-coordinate Fourier strips.  The actual Fourier-support predicate is kept
as a field because the repository deliberately does not rebuild the full
Euclidean Fourier-transform support API. -/
structure L6StripFamily where
  numberOfStrips : ℕ
  individualSixthPower : Fin numberOfStrips → ℝ
  sumSixthPower : ℝ
  individual_nonnegative : ∀ j, 0 ≤ individualSixthPower j
  sum_nonnegative : 0 ≤ sumSixthPower
  pairwiseDisjointIntervalFourierSupports : Prop

/-- Exact numerical conclusion of the strip projection lemma.  Its analytic
input is orthogonality at `L²`, bounded interval projections at `Lʳ` from the
Hilbert transform, and vector-valued complex interpolation.  The new exponent
calculation is *not* hidden here; it is proved in `Turning.StripExponent`. -/
def L6StripProjectionStatement : Prop :=
  ∀ delta : ℝ, 0 < delta → ∃ Cdelta : ℝ, 0 ≤ Cdelta ∧
    ∀ F : L6StripFamily,
      F.pairwiseDisjointIntervalFourierSupports →
      F.sumSixthPower ≤ Cdelta * (F.numberOfStrips : ℝ) ^ (4 + delta) *
        ∑ j, F.individualSixthPower j

/-- All standard analysis inputs used later. -/
structure AnalysisInputs : Prop where
  fourierFourth : ∀ (G : Type) (_ : AddCommGroup G)
    (_ : IsAddTorsionFree G) (_ : DecidableEq G),
      Nonempty (FourierFourthNormInput G)
  bilinearInterpolation : AlphaTwoBilinearInterpolationStatement
  stripProjection : L6StripProjectionStatement

end

end ComplexitySensitiveEnergy.External
