import ComplexitySensitiveEnergy.Flagged.Main
import ComplexitySensitiveEnergy.Flagged.Definitions

/-!
# Dimension--cardinality closure for Theorem 1.1

This file closes the lower-dimensional wall recursion which is deliberately
left as a parameter in `Flagged.Main`.  The geometric input supplies only
eligible supports, zero-dimensional cardinality, and non-circular node
certificates.  The energy estimate is then proved by the paper's
lexicographic induction on dimension and cardinality.
-/

open scoped BigOperators Pointwise

namespace ComplexitySensitiveEnergy.PaperVariety

noncomputable section

variable {n : ℕ}

/-- Geometric certificate family at all dimension and cardinality nodes.

`Eligible W A` is intended to mean that `A` is the portion of the original
finite set assigned to the admissible component `W`.  In particular,
`wall_eligible` records only the support bookkeeping needed to pass to a
strictly lower-dimensional component.  No field is an energy bound at the
target exponent. -/
structure FlaggedGeometryPackage
    (Lambda R : ℕ) (a eps : ℝ) where
  Eligible : PaperVariety n → Finset (RVec n) → Prop
  L : ℕ → ℕ
  J : ℕ → ℕ
  cellRatio : ℕ → ℝ
  rho : ℕ → ℝ
  zeroDimCardBound : ℕ
  cellRatio_nonneg : ∀ k, 0 ≤ cellRatio k
  rho_nonneg : ∀ k, 0 ≤ rho k
  rho_lt_one : ∀ k, rho k < 1
  eligible_dimension : ∀ W A, Eligible W A → W.complexDim ≤ n
  zero_dim_card : ∀ W A, Eligible W A → W.complexDim = 0 →
    A.card ≤ zeroDimCardBound
  certify : ∀ W A, Eligible W A → A.Nonempty →
    0 < W.complexDim →
      Nonempty (NodeCertificate W (Eligible W) A Lambda R
        (L W.complexDim) (J W.complexDim) a eps
        (cellRatio W.complexDim) (rho W.complexDim))
  wall_eligible : ∀ W A, Eligible W A →
    ∀ {L₀ J₀ : ℕ} {cellRatio₀ rho₀ : ℝ}
      (N : NodeCertificate W (Eligible W) A Lambda R
        L₀ J₀ a eps cellRatio₀ rho₀),
    ∀ i ∈ N.wallData.indices,
      (N.wallData.variety i).alpha ≤ a ∧
        (N.wallData.variety i).complexDim < W.complexDim ∧
        (N.wallData.variety i).degree ≤ R →
      Eligible (N.wallData.variety i) (N.wallData.piece i)

/-- Dimension-layer constants.  The `max` retains every preceding layer;
the second entry is the fixed point of the same-dimensional cardinality
recurrence at the new layer. -/
noncomputable def certifiedDimensionConstant
    (zeroDimCardBound : ℕ) (L J : ℕ → ℕ) (rho : ℕ → ℝ) :
    ℕ → ℝ
  | 0 => max 1 ((zeroDimCardBound : ℝ) ^ (3 : ℕ))
  | k + 1 =>
      max (certifiedDimensionConstant zeroDimCardBound L J rho k)
        (flaggedInductionConstant (L (k + 1)) (J (k + 1))
          (certifiedDimensionConstant zeroDimCardBound L J rho k)
          (rho (k + 1)))

theorem certifiedDimensionConstant_one_le
    (zeroDimCardBound : ℕ) (L J : ℕ → ℕ) (rho : ℕ → ℝ) :
    ∀ k, 1 ≤ certifiedDimensionConstant zeroDimCardBound L J rho k := by
  intro k
  induction k with
  | zero =>
      simpa only [certifiedDimensionConstant] using
        (le_max_left (1 : ℝ) ((zeroDimCardBound : ℝ) ^ (3 : ℕ)))
  | succ k ih =>
      exact ih.trans (by
        simp only [certifiedDimensionConstant]
        exact le_max_left _ _)

theorem certifiedDimensionConstant_nonneg
    (zeroDimCardBound : ℕ) (L J : ℕ → ℕ) (rho : ℕ → ℝ) :
    ∀ k, 0 ≤ certifiedDimensionConstant zeroDimCardBound L J rho k := by
  intro k
  exact (by norm_num : (0 : ℝ) ≤ 1).trans
    (certifiedDimensionConstant_one_le zeroDimCardBound L J rho k)

theorem certifiedDimensionConstant_step_mono
    (zeroDimCardBound : ℕ) (L J : ℕ → ℕ) (rho : ℕ → ℝ)
    (k : ℕ) :
    certifiedDimensionConstant zeroDimCardBound L J rho k ≤
      certifiedDimensionConstant zeroDimCardBound L J rho (k + 1) := by
  simp only [certifiedDimensionConstant]
  exact le_max_left _ _

theorem certifiedDimensionConstant_mono
    (zeroDimCardBound : ℕ) (L J : ℕ → ℕ) (rho : ℕ → ℝ)
    {j k : ℕ} (hjk : j ≤ k) :
    certifiedDimensionConstant zeroDimCardBound L J rho j ≤
      certifiedDimensionConstant zeroDimCardBound L J rho k := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hjk ih =>
      exact ih.trans
        (certifiedDimensionConstant_step_mono zeroDimCardBound L J rho k)

private theorem flaggedTargetScale_one_le
    {Lambda : ℕ} {a eps : ℝ} {A : Finset (RVec n)}
    (hLambda : 1 ≤ Lambda) (hA : A.Nonempty)
    (ha3 : a < 3) (ha0 : 0 < a + eps) :
    1 ≤ flaggedTargetScale Lambda a eps A := by
  have hLambdaR : (1 : ℝ) ≤ Lambda := by exact_mod_cast hLambda
  have hCardR : (1 : ℝ) ≤ A.card := by exact_mod_cast hA.card_pos
  unfold flaggedTargetScale
  have hleft : (1 : ℝ) ≤ (Lambda : ℝ) ^ (3 - a) :=
    Real.one_le_rpow hLambdaR (by linarith)
  have hright : (1 : ℝ) ≤ (A.card : ℝ) ^ (a + eps) :=
    Real.one_le_rpow hCardR ha0.le
  nlinarith [mul_le_mul hleft hright (by norm_num : (0 : ℝ) ≤ 1)
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Lambda) _)]

private theorem node_coefficient_le_dimensionConstant
    (zeroDimCardBound : ℕ) (L J : ℕ → ℕ) (rho : ℕ → ℝ)
    (k : ℕ) (_hrho0 : 0 ≤ rho (k + 1)) (hrho1 : rho (k + 1) < 1) :
    nodeBaseCoefficient (L (k + 1)) (J (k + 1))
        (certifiedDimensionConstant zeroDimCardBound L J rho k) +
      rho (k + 1) *
        certifiedDimensionConstant zeroDimCardBound L J rho (k + 1) ≤
      certifiedDimensionConstant zeroDimCardBound L J rho (k + 1) := by
  let lower := certifiedDimensionConstant zeroDimCardBound L J rho k
  let base := nodeBaseCoefficient (L (k + 1)) (J (k + 1)) lower
  let fixed := flaggedInductionConstant (L (k + 1)) (J (k + 1))
    lower (rho (k + 1))
  let current := certifiedDimensionConstant zeroDimCardBound L J rho (k + 1)
  have hden : 0 < 1 - rho (k + 1) := sub_pos.mpr hrho1
  have hfixed : fixed ≤ current := by
    dsimp only [fixed, current]
    simp only [certifiedDimensionConstant]
    exact le_max_right _ _
  have hbaseEq : base = (1 - rho (k + 1)) * fixed := by
    dsimp only [base, fixed, flaggedInductionConstant]
    field_simp
  have hmul : (1 - rho (k + 1)) * fixed ≤
      (1 - rho (k + 1)) * current :=
    mul_le_mul_of_nonneg_left hfixed hden.le
  change base + rho (k + 1) * current ≤ current
  rw [hbaseEq]
  calc
    (1 - rho (k + 1)) * fixed + rho (k + 1) * current ≤
        (1 - rho (k + 1)) * current + rho (k + 1) * current :=
      by
        simpa only [add_comm] using
          add_le_add_right hmul (rho (k + 1) * current)
    _ = current := by ring

/-- Full lexicographic closure.  Unlike
`flagged_energy_cardinality_strong_induction`, this theorem has no
lower-dimensional energy hypothesis: wall pieces are discharged by the
dimension induction generated from `wall_eligible`. -/
theorem certified_flagged_energy_bound
    {Lambda R : ℕ} {a eps : ℝ}
    (H : FlaggedGeometryPackage (n := n) Lambda R a eps)
    (hLambda : 1 ≤ Lambda)
    (ha2 : 2 ≤ a) (ha3 : a < 3) (heps : 0 < eps) :
    ∀ (W : PaperVariety n) (A : Finset (RVec n)), H.Eligible W A →
      realEnergy A ≤
        certifiedDimensionConstant H.zeroDimCardBound H.L H.J H.rho
          W.complexDim * flaggedTargetScale Lambda a eps A := by
  classical
  let Cdim := certifiedDimensionConstant H.zeroDimCardBound H.L H.J H.rho
  let P : ℕ → ℕ → Prop := fun k m =>
    ∀ (W : PaperVariety n) (A : Finset (RVec n)),
      W.complexDim = k → A.card = m → H.Eligible W A →
        realEnergy A ≤ Cdim k * flaggedTargetScale Lambda a eps A
  have hP : ∀ k m, P k m := by
    apply dimension_cardinality_strong_induction
    intro k m ihDimension ihCardinality W A hdim hcard hEligible
    by_cases hA : A.Nonempty
    · rcases k with _ | k
      · have hzeroDim : W.complexDim = 0 := hdim
        have hcardBound : A.card ≤ H.zeroDimCardBound :=
          H.zero_dim_card W A hEligible hzeroDim
        have henergy : realEnergy A ≤ (A.card : ℝ) ^ (3 : ℕ) := by
          exact_mod_cast energy_le_card_cubed A
        have hcardBoundR : (A.card : ℝ) ≤ H.zeroDimCardBound := by
          exact_mod_cast hcardBound
        have hpow : (A.card : ℝ) ^ (3 : ℕ) ≤
            (H.zeroDimCardBound : ℝ) ^ (3 : ℕ) :=
          pow_le_pow_left₀ (by positivity) hcardBoundR 3
        have htarget : 1 ≤ flaggedTargetScale Lambda a eps A :=
          flaggedTargetScale_one_le hLambda hA ha3 (by linarith)
        have hC0 : 0 ≤ Cdim 0 := by
          dsimp only [Cdim]
          exact certifiedDimensionConstant_nonneg _ _ _ _ _
        calc
          realEnergy A ≤ (A.card : ℝ) ^ (3 : ℕ) := henergy
          _ ≤ (H.zeroDimCardBound : ℝ) ^ (3 : ℕ) := hpow
          _ ≤ Cdim 0 := by
            dsimp only [Cdim]
            simp only [certifiedDimensionConstant]
            exact le_max_right (1 : ℝ)
              ((H.zeroDimCardBound : ℝ) ^ (3 : ℕ))
          _ ≤ Cdim 0 * flaggedTargetScale Lambda a eps A :=
            le_mul_of_one_le_right hC0 htarget
      · have hpositive : 0 < W.complexDim := by omega
        let N0 := Classical.choice (H.certify W A hEligible hA hpositive)
        let N : NodeCertificate W (H.Eligible W) A Lambda R
            (H.L (k + 1)) (H.J (k + 1)) a eps
            (H.cellRatio (k + 1)) (H.rho (k + 1)) := by
          simpa only [hdim] using N0
        have hCcurrent0 : 0 ≤ Cdim (k + 1) := by
          dsimp only [Cdim]
          exact certifiedDimensionConstant_nonneg _ _ _ _ _
        have hClower0 : 0 ≤ Cdim k := by
          dsimp only [Cdim]
          exact certifiedDimensionConstant_nonneg _ _ _ _ _
        have hCells : ∀ B ∈ N.crossing.cells,
            realEnergy B ≤ Cdim (k + 1) *
              flaggedTargetScale Lambda a eps B := by
          intro B hB
          have hlt : B.card < m :=
            (N.cell_strict B hB).trans_le hcard.le
          exact ihCardinality B.card hlt W B hdim rfl
            (N.cell_eligible B hB)
        have hLower : ∀ i ∈ N.wallData.indices,
            (N.wallData.variety i).alpha ≤ a →
              realEnergy (N.wallData.piece i) ≤
                Cdim k * flaggedTargetScale Lambda a eps
                  (N.wallData.piece i) := by
          intro i hi halpha
          rcases N.wallData.regime i hi with hgood | hsmall
          · have hEligibleWall : H.Eligible (N.wallData.variety i)
                (N.wallData.piece i) := by
              apply H.wall_eligible W A hEligible N i hi
              exact ⟨halpha, hgood.2⟩
            have hdimlt : (N.wallData.variety i).complexDim < k + 1 := by
              simpa only [hdim] using hgood.2.1
            have hwallInduction := ihDimension
              (N.wallData.variety i).complexDim hdimlt
              (N.wallData.piece i).card
              (N.wallData.variety i) (N.wallData.piece i) rfl rfl
              hEligibleWall
            have hdimle : (N.wallData.variety i).complexDim ≤ k := by omega
            have hconstantMono :
                Cdim (N.wallData.variety i).complexDim ≤ Cdim k := by
              dsimp only [Cdim]
              exact certifiedDimensionConstant_mono _ _ _ _ hdimle
            exact hwallInduction.trans <|
              mul_le_mul_of_nonneg_right hconstantMono
                (flaggedTargetScale_nonneg _ _ _ _)
          · have hsmallEnergy :=
              realEnergy_le_flaggedTargetScale_of_card_le
                hLambda hsmall ha2 ha3.le heps
            have hLowerOne : (1 : ℝ) ≤ Cdim k := by
              dsimp only [Cdim]
              exact certifiedDimensionConstant_one_le _ _ _ _ _
            exact hsmallEnergy.trans <| by
              simpa only [one_mul] using
                mul_le_mul_of_nonneg_right hLowerOne
                  (flaggedTargetScale_nonneg Lambda a eps
                    (N.wallData.piece i))
        have hnode := N.recurrence_step hA hLambda ha2 ha3.le heps
          (H.cellRatio_nonneg (k + 1)) hCcurrent0 hClower0 hCells hLower
        have hclose :
            nodeBaseCoefficient (H.L (k + 1)) (H.J (k + 1)) (Cdim k) +
                H.rho (k + 1) * Cdim (k + 1) ≤ Cdim (k + 1) := by
          dsimp only [Cdim]
          exact node_coefficient_le_dimensionConstant _ _ _ _ k
            (H.rho_nonneg (k + 1)) (H.rho_lt_one (k + 1))
        exact hnode.trans <|
          mul_le_mul_of_nonneg_right hclose
            (flaggedTargetScale_nonneg Lambda a eps A)
    · have hEmpty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      subst A
      have hp : 0 < a + eps := by linarith
      simp [flaggedTargetScale, Real.zero_rpow hp.ne']
  intro W A hEligible
  simpa only [P, Cdim] using
    (hP W.complexDim A.card W A rfl rfl hEligible)

/-- Uniform ambient-dimensional form: the coefficient at layer `n`
dominates the coefficient of every eligible variety. -/
theorem certified_flagged_energy_bound_uniform
    {Lambda R : ℕ} {a eps : ℝ}
    (H : FlaggedGeometryPackage (n := n) Lambda R a eps)
    (hLambda : 1 ≤ Lambda)
    (ha2 : 2 ≤ a) (ha3 : a < 3) (heps : 0 < eps)
    (W : PaperVariety n) (A : Finset (RVec n)) (hEligible : H.Eligible W A) :
    realEnergy A ≤
      certifiedDimensionConstant H.zeroDimCardBound H.L H.J H.rho n *
        flaggedTargetScale Lambda a eps A := by
  have hbound := certified_flagged_energy_bound H hLambda ha2 ha3 heps
    W A hEligible
  have hmono := certifiedDimensionConstant_mono H.zeroDimCardBound H.L H.J H.rho
    (H.eligible_dimension W A hEligible)
  exact hbound.trans <|
    mul_le_mul_of_nonneg_right hmono
      (flaggedTargetScale_nonneg Lambda a eps A)

/-- Paper-facing interface for the geometric inputs to Theorem 1.1.

For each paper parameter tuple it supplies a degree cutoff and a uniform
numerical majorant for the recursively defined dimension constants.  For a
particular `V`, `X`, and flag bound it then supplies a geometry package and
the root eligibility fact.  This proposition never assumes an energy bound. -/
def FlaggedRecurrenceInputs : Prop :=
  ∀ (n Delta : ℕ) (a eps : ℝ),
    1 ≤ n → 1 ≤ Delta → 2 ≤ a → a < 3 → 0 < eps →
    ∃ R : ℕ, Delta ≤ R ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (V : PaperVariety n), V.admissibleIrreducible →
        0 < V.complexDim → V.degree ≤ Delta → V.alpha ≤ a →
        ∀ (X : Finset (RVec n)), (↑X : Set (RVec n)) ⊆ V.realPoints →
          ∀ Lambda : ℕ, V.FlagBound a R X Lambda →
            ∃ H : FlaggedGeometryPackage (n := n) Lambda R a eps,
              H.Eligible V X ∧
              certifiedDimensionConstant
                H.zeroDimCardBound H.L H.J H.rho n ≤ C

/-- The exact statement of Theorem 1.1 follows from the non-circular
recurrence-input interface. -/
theorem theorem11_of_recurrenceInputs
    (Hinput : FlaggedRecurrenceInputs) : Theorem11Statement := by
  intro n Delta a eps hn hDelta ha2 ha3 heps
  obtain ⟨R, hR, C, hC, hprovide⟩ :=
    Hinput n Delta a eps hn hDelta ha2 ha3 heps
  refine ⟨R, hR, C, hC, ?_⟩
  intro V hVadmissible hVdim hVdegree hValpha X hX Lambda hFlag
  obtain ⟨H, hEligible, hconstant⟩ :=
    hprovide V hVadmissible hVdim hVdegree hValpha X hX Lambda hFlag
  have hbound := certified_flagged_energy_bound_uniform H hFlag.1
    ha2 ha3 heps V X hEligible
  calc
    (energy X : ℝ) ≤
        certifiedDimensionConstant H.zeroDimCardBound H.L H.J H.rho n *
          flaggedTargetScale Lambda a eps X := hbound
    _ ≤ C * flaggedTargetScale Lambda a eps X :=
      mul_le_mul_of_nonneg_right hconstant
        (flaggedTargetScale_nonneg Lambda a eps X)
    _ = C * (Lambda : ℝ) ^ (3 - a) *
        (X.card : ℝ) ^ (a + eps) := by
      simp only [flaggedTargetScale]
      ring

end

end ComplexitySensitiveEnergy.PaperVariety
