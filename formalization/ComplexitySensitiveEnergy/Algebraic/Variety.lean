import Mathlib

/-!
# Paper-facing algebraic-variety interface

Mathlib does not yet provide the combined real/complex degree, dimension,
real-locus, and semialgebraic-component API used by the paper.  This file
therefore records those data in one explicit semantic interface.  No theorem
about algebraic varieties is postulated here: the external files state the
precise results which may be supplied for this interface.

The additive-combinatorial definitions (`stabilizer`, translate fibers, and
finite occupancies) are literal definitions on the displayed carriers.
-/

open scoped Pointwise

namespace ComplexitySensitiveEnergy

/-- Real affine `n`-space, with coordinatewise addition. -/
abbrev RVec (n : ℕ) := Fin n → ℝ

/-- Complex affine `n`-space. -/
abbrev CVec (n : ℕ) := Fin n → ℂ

/-- Coordinatewise inclusion of real affine space into complex affine space. -/
def complexifyPoint {n : ℕ} (x : RVec n) : CVec n := fun i => (x i : ℂ)

/-- Translate a set in an additive group.  Thus `x ∈ translateSet S t` means
`x = y + t` for some `y ∈ S`. -/
def translateSet {G : Type*} [AddGroup G] (S : Set G) (t : G) : Set G :=
  {x | x - t ∈ S}

theorem mem_translateSet_iff {G : Type*} [AddGroup G]
    {S : Set G} {t x : G} :
    x ∈ translateSet S t ↔ x - t ∈ S := Iff.rfl

/-- The paper's admissible irreducible variety data.

`complexDim`, `degree`, `differenceDim`, and `translateFiberDim` are the
corresponding *complex algebraic* invariants.  Supplying data with these
meanings is part of the external algebraic-geometry trust boundary; they must
not be confused with Euclidean topological dimension or topological
irreducibility. -/
structure PaperVariety (n : ℕ) where
  realPoints : Set (RVec n)
  complexPoints : Set (CVec n)
  complexDim : ℕ
  degree : ℕ
  differenceDim : ℕ
  /-- Complex dimension of `W_C ∩ (W_C + t)` for a real translation `t`.
  The value on an empty fiber is harmless in this development because only
  the comparison with the generic fiber dimension is used. -/
  translateFiberDim : RVec n → ℕ
  /-- Marker for: complex affine variety irreducible and defined over `ℝ`,
  with the displayed real locus Zariski dense in it. -/
  admissibleIrreducible : Prop
  real_is_realLocus :
    realPoints = {x | complexifyPoint x ∈ complexPoints}
  differenceDim_le : differenceDim ≤ 2 * complexDim

namespace PaperVariety

variable {n : ℕ}

/-- Generic complex dimension of a difference fiber, equation (2.7). -/
def sigma (W : PaperVariety n) : ℕ := 2 * W.complexDim - W.differenceDim

/-- Intrinsic energy exponent, equation (2.8).  Paper-facing theorems always
assume `0 < W.complexDim`. -/
noncomputable def alpha (W : PaperVariety n) : ℝ :=
  max 2 (1 + 2 * (W.sigma : ℝ) / (W.complexDim : ℝ))

/-- Literal real translation stabilizer, equation (2.9). -/
def stabilizer (W : PaperVariety n) : Set (RVec n) :=
  {t | translateSet W.realPoints t = W.realPoints}

/-- Literal real translate fiber `W ∩ (W+t)`. -/
def realTranslateFiber (W : PaperVariety n) (t : RVec n) : Set (RVec n) :=
  W.realPoints ∩ translateSet W.realPoints t

/-- Exceptional non-stabilizer translations, equation (2.10). -/
def badTranslations (W : PaperVariety n) : Set (RVec n) :=
  {t | t ∉ W.stabilizer ∧ W.sigma < W.translateFiberDim t}

/-- A paper subvariety is required to be an admissible irreducible positive-
dimensional subvariety on both its real and complex carriers. -/
def IsPositiveDimensionalSubvariety (W V : PaperVariety n) : Prop :=
  W.admissibleIrreducible ∧ 0 < W.complexDim ∧
    W.realPoints ⊆ V.realPoints ∧ W.complexPoints ⊆ V.complexPoints

/-- Points of a finite set lying on a variety. -/
noncomputable def restrict (A : Finset (RVec n)) (W : PaperVariety n) :
    Finset (RVec n) := by
  classical
  exact A.filter (· ∈ W.realPoints)

@[simp] theorem mem_restrict {A : Finset (RVec n)} {W : PaperVariety n}
    {x : RVec n} :
    x ∈ W.restrict A ↔ x ∈ A ∧ x ∈ W.realPoints := by
  classical
  simp [restrict]

/-- Occupancy of the stabilizer coset through `z`. -/
noncomputable def stabilizerCosetOccupancy
    (W : PaperVariety n) (A : Finset (RVec n)) (z : RVec n) : ℕ := by
  classical
  exact (A.filter fun x => x - z ∈ W.stabilizer).card

/-- Occupancy of one translate fiber by the selected finite set. -/
noncomputable def translateFiberOccupancy
    (W : PaperVariety n) (A : Finset (RVec n)) (t : RVec n) : ℕ := by
  classical
  exact (A.filter fun x => x ∈ W.realTranslateFiber t).card

/-- Upper-bound formulation of the local concentration parameter (2.11).
This is equivalent to saying `lambda_W(A) ≤ L`, while avoiding an infinite
supremum of natural numbers in downstream statements. -/
def LocalConcentrationBound
    (W : PaperVariety n) (A : Finset (RVec n)) (L : ℕ) : Prop :=
  1 ≤ L ∧
  (∀ z : RVec n, W.stabilizerCosetOccupancy A z ≤ L) ∧
  (∀ t ∈ W.badTranslations, W.translateFiberOccupancy A t ≤ L)

/-- Upper-bound formulation of the flag parameter (3.1).  It retains the
degree cutoff, the split at the target exponent, and every positive-
dimensional admissible irreducible subvariety. -/
def FlagBound (a : ℝ) (R : ℕ) (X : Finset (RVec n))
    (V : PaperVariety n) (Lambda : ℕ) : Prop :=
  1 ≤ Lambda ∧
  ∀ W : PaperVariety n,
    W.IsPositiveDimensionalSubvariety V → W.degree ≤ R →
      if W.alpha ≤ a then
        W.LocalConcentrationBound (W.restrict X) Lambda
      else
        (W.restrict X).card ≤ Lambda

end PaperVariety

end ComplexitySensitiveEnergy
