import ComplexitySensitiveEnergy.QuadraticThreefold.CellRecurrence
import ComplexitySensitiveEnergy.QuadraticThreefold.TwoCrossing
import ComplexitySensitiveEnergy.QuadraticThreefold.Definitions
import ComplexitySensitiveEnergy.Additive.UnionEnergy

/-!
# Certified recurrence closure for Theorem 1.2

This file formalizes the cardinality-induction core of the quadratic
threefold theorem.  A node certificate records the genuine set partition,
strictly smaller cells, the `D N² + D² ∑ E(X_i)` cellular estimate, and
the lower-exponent wall estimate.  It never contains the desired
`N^(2+eps)` conclusion.

The Gram-matrix rank-drop bound, cellular power sum, exact
`D^(-1-3 eps)` algebra, lower-order absorption, two-set union inequality,
and contractive strong induction are all checked in Lean.
-/

open scoped BigOperators Pointwise

namespace ComplexitySensitiveEnergy.QuadraticThreefold

noncomputable section

abbrev threefoldRealEnergy (X : Finset R5) : ℝ := (energy X : ℝ)

/-- A raw geometric cell estimate whose exceptional term is expressed by
the four rank-drop contributions can be converted to the normalized
`D N² + D² ∑ E` form by the internal Gram calculation. -/
theorem cell_estimate_of_rankDrop
    {I R1 Z1 R2 Z2 R3 Z3 : Type*}
    [Fintype R1] [Fintype Z1] [DecidableEq R1]
    [Fintype R2] [Fintype Z2] [DecidableEq R2]
    [Fintype R3] [Fintype Z3] [DecidableEq R3]
    (Y : Finset R5) (cells : Finset I) (cellEnergy : I → ℕ)
    (N D zeroContribution direction1 direction2 direction3 : ℕ)
    (M1 : R1 → Z1 → ℕ) (M2 : R2 → Z2 → ℕ)
    (M3 : R3 → Z3 → ℕ)
    (hzero : zeroContribution ≤ N ^ 2)
    (hdir1 : direction1 ≤ offDiagonalGramSquareSum M1)
    (hdir2 : direction2 ≤ offDiagonalGramSquareSum M2)
    (hdir3 : direction3 ≤ offDiagonalGramSquareSum M3)
    (htrace1 : gramTrace M1 ≤ N) (htrace2 : gramTrace M2 ≤ N)
    (htrace3 : gramTrace M3 ≤ N)
    (hraw : energy Y ≤
      D * (zeroContribution + direction1 + direction2 + direction3) +
        D ^ 2 * ∑ i ∈ cells, cellEnergy i) :
    energy Y ≤ 7 *
      (D * N ^ 2 + D ^ 2 * ∑ i ∈ cells, cellEnergy i) := by
  have hrank := rankDrop_contributions_le_seven N zeroContribution
    direction1 direction2 direction3 M1 M2 M3 hzero hdir1 hdir2 hdir3
    htrace1 htrace2 htrace3
  calc
    energy Y ≤
        D * (zeroContribution + direction1 + direction2 + direction3) +
          D ^ 2 * ∑ i ∈ cells, cellEnergy i := hraw
    _ ≤ D * (7 * N ^ 2) + D ^ 2 * ∑ i ∈ cells, cellEnergy i := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left D hrank) _
    _ ≤ 7 * (D * N ^ 2 + D ^ 2 * ∑ i ∈ cells, cellEnergy i) := by
      have hseven : D ^ 2 * (∑ i ∈ cells, cellEnergy i) ≤
          7 * (D ^ 2 * ∑ i ∈ cells, cellEnergy i) := by omega
      calc
        D * (7 * N ^ 2) + D ^ 2 * ∑ i ∈ cells, cellEnergy i =
            7 * (D * N ^ 2) + D ^ 2 *
              ∑ i ∈ cells, cellEnergy i := by ring
        _ ≤ 7 * (D * N ^ 2) +
            7 * (D ^ 2 * ∑ i ∈ cells, cellEnergy i) :=
          Nat.add_le_add_left hseven _
        _ = 7 * (D * N ^ 2 + D ^ 2 *
            ∑ i ∈ cells, cellEnergy i) := by ring

/-- Non-circular data produced by one degree-`D` partition of a finite
subset of a fixed simple-spectrum graph. -/
structure ThreefoldNodeCertificate
    (Q : SimplePencil) (Eligible : Finset R5 → Prop)
    (X : Finset R5) (D : ℕ)
    (eps cellCoefficient wallCoefficient rho : ℝ) where
  retained : Finset R5
  wall : Finset R5
  decomposition : X = retained ∪ wall
  retained_wall_disjoint : Disjoint retained wall
  points_on_graph : ↑X ⊆ graphCarrier Q
  cells : Finset (Finset R5)
  cell_subset : ∀ B ∈ cells, B ⊆ X
  cell_eligible : ∀ B ∈ cells, Eligible B
  cell_strict : ∀ B ∈ cells, B.card < X.card
  /-- Normalized form of `|X_i| ≪ N/D³`; fixed geometric constants may be
  incorporated into the chosen effective partition parameter. -/
  cell_size : ∀ B ∈ cells,
    (B.card : ℝ) ≤ (X.card : ℝ) / (D : ℝ) ^ (3 : ℕ)
  cell_card_sum :
    (∑ B ∈ cells, (B.card : ℝ)) ≤ (X.card : ℝ)
  /-- Proposition 4.5 (`prop:threefold-cell`) after the internal rank-drop
  estimate has been inserted. -/
  cell_estimate :
    threefoldRealEnergy retained ≤ cellCoefficient *
      ((D : ℝ) * (X.card : ℝ) ^ (2 : ℕ) +
        (D : ℝ) ^ (2 : ℕ) *
          ∑ B ∈ cells, threefoldRealEnergy B)
  /-- Exact output of the wall/Jing--Wu/generic-projection stage.  Its
  exponent `2+eps/2` is strictly below the induction target. -/
  wall_estimate :
    threefoldRealEnergy wall ≤ wallCoefficient *
      (X.card : ℝ) ^ (2 + eps / 2)
  /-- Checked numerical output of choosing `D` sufficiently large. -/
  contraction :
    8 * cellCoefficient * (D : ℝ) ^ (-1 - 3 * eps) ≤ rho

/-- A non-circular refinement of `ThreefoldNodeCertificate` in which the
cellular estimate is not supplied as a field.  Instead, the geometric input
is the granular crossing certificate and the literal rank-drop Gram
certificate from `QuadraticThreefold.TwoCrossing`.

The remaining fields are exactly the partition, wall, and numerical data
needed by the cardinality recurrence. -/
structure GranularThreefoldNodeCertificate
    (Q : SimplePencil) (Eligible : Finset R5 → Prop)
    (X : Finset R5) (D : ℕ)
    (eps cellCoefficient wallCoefficient rho : ℝ) where
  retained : Finset R5
  wall : Finset R5
  decomposition : X = retained ∪ wall
  retained_wall_disjoint : Disjoint retained wall
  points_on_graph : ↑X ⊆ graphCarrier Q
  crossing : ThreefoldCrossingCertificate X retained D
  rankDrop : RankDropGramCertificate X crossing.rankDropSet
  cell_eligible : ∀ B ∈ crossing.cells, Eligible B
  cell_strict : ∀ B ∈ crossing.cells, B.card < X.card
  cell_size : ∀ B ∈ crossing.cells,
    (B.card : ℝ) ≤ (X.card : ℝ) / (D : ℝ) ^ (3 : ℕ)
  cell_card_sum :
    (∑ B ∈ crossing.cells, (B.card : ℝ)) ≤ (X.card : ℝ)
  /-- The explicit absolute constant produced by the two crossings and the
  paper's deliberately loose rank-drop coefficient `7`. -/
  fourteen_le_cellCoefficient : (14 : ℝ) ≤ cellCoefficient
  wall_estimate :
    threefoldRealEnergy wall ≤ wallCoefficient *
      (X.card : ℝ) ^ (2 + eps / 2)
  contraction :
    8 * cellCoefficient * (D : ℝ) ^ (-1 - 3 * eps) ≤ rho

namespace GranularThreefoldNodeCertificate

variable {Q : SimplePencil} {Eligible : Finset R5 → Prop}
  {X : Finset R5} {D : ℕ}
  {eps cellCoefficient wallCoefficient rho : ℝ}

/-- Convert the granular, genuinely geometric certificate into the legacy
node interface.  The formerly assumed `cell_estimate` is proved here by the
two internal Cauchy--Schwarz steps, mixed rearrangement, and Gram estimate. -/
noncomputable def toNode
    (N : GranularThreefoldNodeCertificate Q Eligible X D
      eps cellCoefficient wallCoefficient rho)
    (hD : 1 ≤ D) :
    ThreefoldNodeCertificate Q Eligible X D
      eps cellCoefficient wallCoefficient rho where
  retained := N.retained
  wall := N.wall
  decomposition := N.decomposition
  retained_wall_disjoint := N.retained_wall_disjoint
  points_on_graph := N.points_on_graph
  cells := N.crossing.cells
  cell_subset := N.crossing.cell_subset
  cell_eligible := N.cell_eligible
  cell_strict := N.cell_strict
  cell_size := N.cell_size
  cell_card_sum := N.cell_card_sum
  cell_estimate := N.crossing.cell_estimate_real N.rankDrop hD
    cellCoefficient N.fourteen_le_cellCoefficient
  wall_estimate := N.wall_estimate
  contraction := N.contraction

end GranularThreefoldNodeCertificate

namespace ThreefoldNodeCertificate

variable {Q : SimplePencil} {Eligible : Finset R5 → Prop}
  {X : Finset R5} {D : ℕ}
  {eps cellCoefficient wallCoefficient rho C : ℝ}

/-- Single-node verifier for the recurrence in equation (4.15). -/
theorem recurrence_step
    (N : ThreefoldNodeCertificate Q Eligible X D
      eps cellCoefficient wallCoefficient rho)
    (hX : X.Nonempty) (hD : 2 ≤ D) (heps : 0 < eps)
    (hcellCoefficient : 0 ≤ cellCoefficient)
    (hwallCoefficient : 0 ≤ wallCoefficient)
    (hC : 0 ≤ C)
    (hCells : ∀ B ∈ N.cells,
      threefoldRealEnergy B ≤ C * (B.card : ℝ) ^ (2 + eps)) :
    threefoldRealEnergy X ≤
      ((8 * cellCoefficient * (D : ℝ) + 8 * wallCoefficient) +
        rho * C) * (X.card : ℝ) ^ (2 + eps) := by
  classical
  let cardX : ℝ := (X.card : ℝ)
  let target : ℝ := cardX ^ (2 + eps)
  let cellSum : ℝ := ∑ B ∈ N.cells, threefoldRealEnergy B
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hD)
  have hXpos : 0 < cardX := by
    dsimp only [cardX]
    exact_mod_cast hX.card_pos
  have hXone : (1 : ℝ) ≤ cardX := by
    dsimp only [cardX]
    exact_mod_cast hX.card_pos
  have hscale0 : 0 ≤ cardX / (D : ℝ) ^ (3 : ℕ) := by positivity
  have hsumCells : cellSum ≤
      C * ((cardX / (D : ℝ) ^ (3 : ℕ)) ^ (1 + eps) * cardX) := by
    dsimp only [cellSum, cardX]
    exact cellular_energy_sum_le N.cells
      (fun B => (B.card : ℝ)) (fun B => threefoldRealEnergy B)
      heps hC hscale0 (fun B hB => by positivity) N.cell_size
      N.cell_card_sum hCells
  have hscaleIdentity :
      (D : ℝ) ^ (2 : ℝ) *
          (cardX / (D : ℝ) ^ (3 : ℕ)) ^ (1 + eps) * cardX =
        (D : ℝ) ^ (-1 - 3 * eps) * target := by
    simpa only [cardX, target] using
      (threefold_cell_scale_identity (D := (D : ℝ))
        (N := (X.card : ℝ)) (eps := eps) hDpos hXpos)
  have hscaleIdentityNat :
      (D : ℝ) ^ (2 : ℕ) *
          (cardX / (D : ℝ) ^ (3 : ℕ)) ^ (1 + eps) * cardX =
        (D : ℝ) ^ (-1 - 3 * eps) * target := by
    simpa only [Real.rpow_two] using hscaleIdentity
  have hrecursive :
      8 * cellCoefficient * (D : ℝ) ^ (2 : ℕ) * cellSum ≤
        rho * C * target := by
    calc
      8 * cellCoefficient * (D : ℝ) ^ (2 : ℕ) * cellSum ≤
          8 * cellCoefficient * (D : ℝ) ^ (2 : ℕ) *
            (C * ((cardX / (D : ℝ) ^ (3 : ℕ)) ^ (1 + eps) *
              cardX)) := by
        exact mul_le_mul_of_nonneg_left hsumCells (by positivity)
      _ = C * (8 * cellCoefficient *
          ((D : ℝ) ^ (2 : ℕ) *
            (cardX / (D : ℝ) ^ (3 : ℕ)) ^ (1 + eps) * cardX)) := by
        ring
      _ = (8 * cellCoefficient * (D : ℝ) ^ (-1 - 3 * eps)) *
          (C * target) := by
        rw [hscaleIdentityNat]
        ring
      _ ≤ rho * (C * target) := by
        exact mul_le_mul_of_nonneg_right N.contraction (by positivity)
      _ = rho * C * target := by ring
  have hEpsPow : (1 : ℝ) ≤ cardX ^ eps :=
    Real.one_le_rpow hXone heps.le
  have hcellCoeff :
      8 * cellCoefficient * (D : ℝ) ≤
        (8 * cellCoefficient * (D : ℝ)) * cardX ^ eps :=
    le_mul_of_one_le_right (by positivity) hEpsPow
  have hcellBase :
      8 * cellCoefficient * ((D : ℝ) * cardX ^ (2 : ℕ)) ≤
        (8 * cellCoefficient * (D : ℝ)) * target := by
    dsimp only [target]
    have habsorb := absorb_missing_power
      (coefficient := 8 * cellCoefficient * (D : ℝ))
      (fraction := 8 * cellCoefficient * (D : ℝ))
      (M := cardX) (a := 2) (eps := eps)
      hXpos hcellCoeff (by positivity)
    simpa [Real.rpow_natCast, mul_assoc] using habsorb
  have hHalfEpsPow : (1 : ℝ) ≤ cardX ^ (eps / 2) :=
    Real.one_le_rpow hXone (by positivity)
  have hwallCoeff : 8 * wallCoefficient ≤
      (8 * wallCoefficient) * cardX ^ (eps / 2) :=
    le_mul_of_one_le_right (by positivity) hHalfEpsPow
  have hwallBase :
      8 * (wallCoefficient * cardX ^ (2 + eps / 2)) ≤
        (8 * wallCoefficient) * target := by
    dsimp only [target]
    have habsorb := absorb_missing_power
      (coefficient := 8 * wallCoefficient)
      (fraction := 8 * wallCoefficient)
      (M := cardX) (a := 2 + eps / 2) (eps := eps / 2)
      hXpos hwallCoeff (by positivity)
    convert habsorb using 1 <;> ring_nf
  have houter : threefoldRealEnergy X ≤
      8 * (threefoldRealEnergy N.retained + threefoldRealEnergy N.wall) := by
    calc
      threefoldRealEnergy X =
          threefoldRealEnergy (N.retained ∪ N.wall) :=
        congrArg (fun S : Finset R5 => threefoldRealEnergy S) N.decomposition
      _ ≤ 8 * (threefoldRealEnergy N.retained +
          threefoldRealEnergy N.wall) :=
        energy_union_le_eight_unconditional _ _ N.retained_wall_disjoint
  calc
    threefoldRealEnergy X ≤
        8 * (threefoldRealEnergy N.retained + threefoldRealEnergy N.wall) :=
      houter
    _ ≤ 8 * (cellCoefficient *
          ((D : ℝ) * cardX ^ (2 : ℕ) +
            (D : ℝ) ^ (2 : ℕ) * cellSum) +
        wallCoefficient * cardX ^ (2 + eps / 2)) := by
      dsimp only [cardX, cellSum]
      gcongr
      · exact N.cell_estimate
      · exact N.wall_estimate
    _ = 8 * cellCoefficient * ((D : ℝ) * cardX ^ (2 : ℕ)) +
        8 * cellCoefficient * (D : ℝ) ^ (2 : ℕ) * cellSum +
        8 * (wallCoefficient * cardX ^ (2 + eps / 2)) := by ring
    _ ≤ (8 * cellCoefficient * (D : ℝ)) * target +
        rho * C * target + (8 * wallCoefficient) * target :=
      add_le_add (add_le_add hcellBase hrecursive) hwallBase
    _ = ((8 * cellCoefficient * (D : ℝ) + 8 * wallCoefficient) +
          rho * C) * (X.card : ℝ) ^ (2 + eps) := by
      dsimp only [target, cardX]
      ring

end ThreefoldNodeCertificate

/-- Uniform nonrecursive coefficient of the normalized threefold node. -/
noncomputable def threefoldBaseCoefficient
    (D : ℕ) (cellCoefficient wallCoefficient : ℝ) : ℝ :=
  8 * cellCoefficient * (D : ℝ) + 8 * wallCoefficient

/-- Fixed point of the contractive cardinality recurrence. -/
noncomputable def threefoldInductionConstant
    (D : ℕ) (cellCoefficient wallCoefficient rho : ℝ) : ℝ :=
  threefoldBaseCoefficient D cellCoefficient wallCoefficient / (1 - rho)

/-- Strong-induction closure on the actual finite-set energy. -/
theorem energy_cardinality_strong_induction
    {Q : SimplePencil} {Eligible : Finset R5 → Prop}
    {D : ℕ} {eps cellCoefficient wallCoefficient rho : ℝ}
    (hD : 2 ≤ D) (heps : 0 < eps)
    (hcellCoefficient : 0 ≤ cellCoefficient)
    (hwallCoefficient : 0 ≤ wallCoefficient)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (certify : ∀ X, Eligible X → X.Nonempty →
      ThreefoldNodeCertificate Q Eligible X D eps
        cellCoefficient wallCoefficient rho) :
    ∀ X, Eligible X →
      threefoldRealEnergy X ≤
        threefoldInductionConstant D cellCoefficient wallCoefficient rho *
          (X.card : ℝ) ^ (2 + eps) := by
  classical
  let base := threefoldBaseCoefficient D cellCoefficient wallCoefficient
  let Cstar := threefoldInductionConstant D cellCoefficient wallCoefficient rho
  have hbase0 : 0 ≤ base := by
    dsimp only [base, threefoldBaseCoefficient]
    positivity
  have hCstar0 : 0 ≤ Cstar := by
    exact div_nonneg hbase0 (sub_nonneg.mpr hrho1.le)
  have hclose : base + rho * Cstar ≤ Cstar := by
    have hclosed := close_contractive_strong_induction
      (u := fun _ : ℕ => base + rho * Cstar)
      hbase0 hrho0 hrho1
      (by
        intro m ih
        change base + rho * Cstar ≤ base + rho * Cstar
        exact le_rfl)
    simpa only [Cstar, threefoldInductionConstant, base] using hclosed 0
  have hall : ∀ m : ℕ, ∀ X : Finset R5,
      X.card = m → Eligible X →
        threefoldRealEnergy X ≤ Cstar * (X.card : ℝ) ^ (2 + eps) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro X hcard hEligible
        by_cases hX : X.Nonempty
        · let N := certify X hEligible hX
          have hCells : ∀ B ∈ N.cells,
              threefoldRealEnergy B ≤
                Cstar * (B.card : ℝ) ^ (2 + eps) := by
            intro B hB
            have hlt : B.card < m := (N.cell_strict B hB).trans_le hcard.le
            exact ih B.card hlt B rfl (N.cell_eligible B hB)
          have hstep := N.recurrence_step hX hD heps
            hcellCoefficient hwallCoefficient hCstar0 hCells
          exact hstep.trans <| by
            exact mul_le_mul_of_nonneg_right hclose (by positivity)
        · have hEmpty : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
          subst X
          have hp : 0 < 2 + eps := by linarith
          simp [Real.zero_rpow hp.ne']
  intro X hEligible
  simpa only [Cstar] using hall X.card X rfl hEligible

/-- Exact interface to the geometric part of Theorem 1.2.  The external
partitioning, wall, Jing--Wu, and generic-projection arguments only have to
produce a node certificate with constants uniform in the simple pencil.
Neither this structure nor any of its fields assumes the target energy bound. -/
structure ThreefoldRecurrenceInputs : Prop where
  certify : ∀ eps : ℝ, 0 < eps →
    ∃ (D : ℕ) (cellCoefficient wallCoefficient rho : ℝ),
      2 ≤ D ∧
      0 ≤ cellCoefficient ∧
      0 ≤ wallCoefficient ∧
      0 ≤ rho ∧ rho < 1 ∧
      ∀ (Q : SimplePencil) (X : Finset R5),
        (↑X : Set R5) ⊆ graphCarrier Q → X.Nonempty →
          Nonempty (ThreefoldNodeCertificate Q
            (fun B : Finset R5 => (↑B : Set R5) ⊆ graphCarrier Q)
            X D eps cellCoefficient wallCoefficient rho)

/-- Stronger paper-facing geometric interface in which Proposition 4.5 is
not an input theorem.  Geometry supplies only the two active-support
certificates and the three directional incidence decompositions; the
cellular energy estimate is then reconstructed by `toNode`. -/
structure GranularThreefoldRecurrenceInputs : Prop where
  certify : ∀ eps : ℝ, 0 < eps →
    ∃ (D : ℕ) (cellCoefficient wallCoefficient rho : ℝ),
      2 ≤ D ∧
      0 ≤ cellCoefficient ∧
      0 ≤ wallCoefficient ∧
      0 ≤ rho ∧ rho < 1 ∧
      ∀ (Q : SimplePencil) (X : Finset R5),
        (↑X : Set R5) ⊆ graphCarrier Q → X.Nonempty →
          Nonempty (GranularThreefoldNodeCertificate Q
            (fun B : Finset R5 => (↑B : Set R5) ⊆ graphCarrier Q)
            X D eps cellCoefficient wallCoefficient rho)

/-- The exact upper-bound clause of Theorem 1.2 follows from the geometric
node interface.  All recurrence algebra and the cardinality induction are
performed internally above. -/
theorem quadraticThreefoldEnergy_of_recurrenceInputs
    (H : ThreefoldRecurrenceInputs) :
    QuadraticThreefoldEnergyStatement := by
  intro eps heps
  obtain ⟨D, cellCoefficient, wallCoefficient, rho, hD,
    hcellCoefficient, hwallCoefficient, hrho0, hrho1, hcertify⟩ :=
    H.certify eps heps
  let C := threefoldInductionConstant D cellCoefficient wallCoefficient rho
  have hC : 0 ≤ C := by
    dsimp only [C, threefoldInductionConstant, threefoldBaseCoefficient]
    exact div_nonneg (by positivity) (sub_nonneg.mpr hrho1.le)
  refine ⟨C, hC, ?_⟩
  intro Q X hgraph
  exact energy_cardinality_strong_induction
    (Q := Q)
    (Eligible := fun B : Finset R5 => (↑B : Set R5) ⊆ graphCarrier Q)
    (D := D) (eps := eps) (cellCoefficient := cellCoefficient)
    (wallCoefficient := wallCoefficient) (rho := rho)
    hD heps hcellCoefficient hwallCoefficient hrho0 hrho1
    (fun Y hY hnonempty => Classical.choice (hcertify Q Y hY hnonempty))
    X hgraph

/-- The upper-bound clause of Theorem 1.2 from the granular geometric
interface.  In particular, Proposition 4.5 is proved on the conversion path
and is not hidden in an external recurrence certificate. -/
theorem quadraticThreefoldEnergy_of_granularRecurrenceInputs
    (H : GranularThreefoldRecurrenceInputs) :
    QuadraticThreefoldEnergyStatement := by
  apply quadraticThreefoldEnergy_of_recurrenceInputs
  refine ⟨?_⟩
  intro eps heps
  obtain ⟨D, cellCoefficient, wallCoefficient, rho, hD,
    hcellCoefficient, hwallCoefficient, hrho0, hrho1, hcertify⟩ :=
    H.certify eps heps
  refine ⟨D, cellCoefficient, wallCoefficient, rho, hD,
    hcellCoefficient, hwallCoefficient, hrho0, hrho1, ?_⟩
  intro Q X hgraph hX
  let N := Classical.choice (hcertify Q X hgraph hX)
  exact ⟨N.toNode (by omega)⟩

end

end ComplexitySensitiveEnergy.QuadraticThreefold
