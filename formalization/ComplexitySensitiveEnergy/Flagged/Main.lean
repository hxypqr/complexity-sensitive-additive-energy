import ComplexitySensitiveEnergy.Flagged.TwoCrossing
import ComplexitySensitiveEnergy.Flagged.Recurrence
import ComplexitySensitiveEnergy.Additive.UnionEnergy

/-!
# Verified closure of the flagged-energy recurrence

This file contains the finite/numerical core of Theorem 1.1.  Geometry is
supplied by explicit node and wall certificates.  These certificates contain
partitions, support bounds, cardinality bounds, dimension drops, and the
contractive coefficient, but never the energy estimate which is being
proved.

The disjoint-union energy estimate, both crossings, the wall alternatives,
the local-to-global interpolation, power-sum estimates, and strong-induction
closure are all proved in Lean.
-/

open scoped BigOperators Pointwise

namespace ComplexitySensitiveEnergy

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Real-valued version of the finite additive energy. -/
abbrev realEnergy (A : Finset G) : ℝ := (energy A : ℝ)

/-- The target scale in Theorem 1.1, before its uniform constant. -/
noncomputable def flaggedTargetScale
    (Lambda : ℕ) (a eps : ℝ) (A : Finset G) : ℝ :=
  (Lambda : ℝ) ^ (3 - a) * (A.card : ℝ) ^ (a + eps)

/-- Power-sum estimate behind the cellular contraction.  It is derived from
the displayed cell-size and total-cell-mass bounds, rather than assumed as a
certificate field. -/
theorem sum_rpow_le_of_le_mul_and_sum_le
    {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {q M p : ℝ}
    (hx0 : ∀ i ∈ s, 0 ≤ x i)
    (hx : ∀ i ∈ s, x i ≤ q * M)
    (hsum : (∑ i ∈ s, x i) ≤ M)
    (hq : 0 ≤ q) (hM : 0 < M) (hp : 1 ≤ p) :
    (∑ i ∈ s, x i ^ p) ≤ q ^ (p - 1) * M ^ p := by
  classical
  have hexp : 0 ≤ p - 1 := sub_nonneg.mpr hp
  have hterm : ∀ i ∈ s,
      x i ^ p ≤ (q * M) ^ (p - 1) * x i := by
    intro i hi
    by_cases hxi : x i = 0
    · have hp0 : 0 < p := zero_lt_one.trans_le hp
      simp [hxi, Real.zero_rpow hp0.ne']
    · have hxpos : 0 < x i := lt_of_le_of_ne (hx0 i hi) (Ne.symm hxi)
      calc
        x i ^ p = x i ^ ((p - 1) + 1) := by
          congr 1
          ring
        _ = x i ^ (p - 1) * x i := Real.rpow_add_one hxi (p - 1)
        _ ≤ (q * M) ^ (p - 1) * x i := by
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (hx0 i hi) (hx i hi) hexp) (hx0 i hi)
  calc
    (∑ i ∈ s, x i ^ p) ≤
        ∑ i ∈ s, (q * M) ^ (p - 1) * x i := by
      exact Finset.sum_le_sum fun i hi => hterm i hi
    _ = (q * M) ^ (p - 1) * ∑ i ∈ s, x i := by
      rw [Finset.mul_sum]
    _ ≤ (q * M) ^ (p - 1) * M := by
      exact mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (by positivity) _)
    _ = q ^ (p - 1) * M ^ p := by
      rw [Real.mul_rpow hq hM.le]
      rw [show p = (p - 1) + 1 by ring, Real.rpow_add hM]
      simp [mul_assoc]

end ComplexitySensitiveEnergy

namespace ComplexitySensitiveEnergy.PaperVariety

variable {n : ℕ}

/-- Correct absorption of the local exceptional term.  The proof visibly
performs the two required stages in order: first `lambda_W(A) ≤ |A|`, then
`lambda_W(A) ≤ Lambda`. -/
theorem localLambda_mul_card_sq_le_flaggedTargetScale
    (W : PaperVariety n) {A : Finset (RVec n)} {Lambda : ℕ}
    {a eps : ℝ} (hA : A.Nonempty)
    (hLocal : W.LocalConcentrationBound A Lambda)
    (ha2 : 2 ≤ a) (ha3 : a ≤ 3) (heps : 0 < eps) :
    (W.energyLocalLambda A : ℝ) * (A.card : ℝ) ^ (2 : ℕ) ≤
      flaggedTargetScale Lambda a eps A := by
  have hlambda1 : (1 : ℝ) ≤ W.energyLocalLambda A := by
    exact_mod_cast W.one_le_energyLocalLambda A
  have hlambdaM : (W.energyLocalLambda A : ℝ) ≤ A.card := by
    exact_mod_cast W.energyLocalLambda_le_card hA
  have hlambdaGlobalNat : W.energyLocalLambda A ≤ Lambda :=
    W.energyLocalLambda_le_of_localConcentrationBound A hLocal
  have hlambdaGlobal : (W.energyLocalLambda A : ℝ) ≤ Lambda := by
    exact_mod_cast hlambdaGlobalNat
  have hM1 : (1 : ℝ) ≤ A.card := by exact_mod_cast hA.card_pos
  have hM0 : 0 ≤ (A.card : ℝ) := by positivity
  have hlambda0 : 0 ≤ (W.energyLocalLambda A : ℝ) := by positivity
  have hexp : 0 ≤ 3 - a := sub_nonneg.mpr ha3
  calc
    (W.energyLocalLambda A : ℝ) * (A.card : ℝ) ^ (2 : ℕ) ≤
        (W.energyLocalLambda A : ℝ) ^ (3 - a) *
          (A.card : ℝ) ^ a :=
      local_lambda_interpolation hlambda1 hlambdaM ha2 ha3
    _ ≤ (Lambda : ℝ) ^ (3 - a) * (A.card : ℝ) ^ a := by
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hlambda0 hlambdaGlobal hexp)
        (Real.rpow_nonneg hM0 _)
    _ ≤ (Lambda : ℝ) ^ (3 - a) *
        (A.card : ℝ) ^ (a + eps) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hM1 (by linarith))
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Lambda) _)
    _ = flaggedTargetScale Lambda a eps A := rfl

theorem flaggedTargetScale_nonneg
    (Lambda : ℕ) (a eps : ℝ) (A : Finset (RVec n)) :
    0 ≤ flaggedTargetScale Lambda a eps A := by
  unfold flaggedTargetScale
  positivity

/-- The high-intrinsic-exponent wall alternative.  Its only geometric input
is the cardinality conclusion of the flag definition; the universal energy
bound and both exponent comparisons are internal. -/
theorem realEnergy_le_flaggedTargetScale_of_card_le
    {B : Finset (RVec n)} {Lambda : ℕ} {a eps : ℝ}
    (hLambda : 1 ≤ Lambda) (hBLambda : B.card ≤ Lambda)
    (ha2 : 2 ≤ a) (ha3 : a ≤ 3) (heps : 0 < eps) :
    realEnergy B ≤ flaggedTargetScale Lambda a eps B := by
  by_cases hB : B.Nonempty
  · have hB1 : (1 : ℝ) ≤ B.card := by exact_mod_cast hB.card_pos
    have hBLambdaR : (B.card : ℝ) ≤ Lambda := by exact_mod_cast hBLambda
    have henergy : realEnergy B ≤ (B.card : ℝ) ^ (3 : ℕ) := by
      exact_mod_cast energy_le_card_cubed B
    calc
      realEnergy B ≤ (B.card : ℝ) ^ (3 : ℕ) := henergy
      _ ≤ (Lambda : ℝ) ^ (3 - a) * (B.card : ℝ) ^ a :=
        worse_wall_energy_scale hB1 hBLambdaR ha2 ha3
      _ ≤ (Lambda : ℝ) ^ (3 - a) *
          (B.card : ℝ) ^ (a + eps) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith))
          (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Lambda) _)
      _ = flaggedTargetScale Lambda a eps B := rfl
  · have hEmpty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    subst B
    have hp : 0 < a + eps := by linarith
    simp [flaggedTargetScale, Real.zero_rpow hp.ne']

/-- Exact wall decomposition data at one node.  The left branch of `regime`
is handled by the already-closed lower-dimensional induction; the right
branch is the flag-small (or singleton zero-dimensional) alternative. -/
structure WallCertificate
    (W : PaperVariety n) (A wall : Finset (RVec n))
    (Lambda R : ℕ) (a : ℝ) where
  Index : Type
  indices : Finset Index
  piece : Index → Finset (RVec n)
  variety : Index → PaperVariety n
  pairwise_disjoint :
    ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j → Disjoint (piece i) (piece j)
  wall_eq : wall = indices.biUnion piece
  piece_subset : ∀ i ∈ indices, piece i ⊆ A
  piece_on_variety :
    ∀ i ∈ indices, ∀ x ∈ piece i, x ∈ (variety i).realPoints
  regime : ∀ i ∈ indices,
    ((variety i).alpha ≤ a ∧
      (variety i).complexDim < W.complexDim ∧
      (variety i).degree ≤ R) ∨
    (piece i).card ≤ Lambda
  card_sum_le :
    (∑ i ∈ indices, ((piece i).card : ℝ)) ≤ (A.card : ℝ)

namespace WallCertificate

variable {W : PaperVariety n} {A wall : Finset (RVec n)}
  {Lambda R : ℕ} {a eps lowerCoefficient : ℝ}

/-- Wall energy assembled from lower-dimensional and flag-small pieces. -/
theorem energy_le
    (D : WallCertificate W A wall Lambda R a)
    {J : ℕ} (hJ : D.indices.card ≤ J)
    (hA : A.Nonempty) (hLambda : 1 ≤ Lambda)
    (ha2 : 2 ≤ a) (ha3 : a ≤ 3) (heps : 0 < eps)
    (hlower0 : 0 ≤ lowerCoefficient)
    (hLower : ∀ i ∈ D.indices,
      (D.variety i).alpha ≤ a →
        realEnergy (D.piece i) ≤
          lowerCoefficient *
            flaggedTargetScale Lambda a eps (D.piece i)) :
    realEnergy wall ≤
      (J : ℝ) ^ (3 : ℕ) * max lowerCoefficient 1 *
        flaggedTargetScale Lambda a eps A := by
  classical
  let K : ℝ := max lowerCoefficient 1
  have hK0 : 0 ≤ K := by
    exact hlower0.trans (le_max_left _ _)
  have hLambdaPow : 0 ≤ (Lambda : ℝ) ^ (3 - a) := by positivity
  have hp : 1 ≤ a + eps := by linarith
  have hM : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hpiece : ∀ i ∈ D.indices,
      realEnergy (D.piece i) ≤
        K * flaggedTargetScale Lambda a eps (D.piece i) := by
    intro i hi
    rcases D.regime i hi with hgood | hsmall
    · exact (hLower i hi hgood.1).trans <|
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (flaggedTargetScale_nonneg _ _ _ _)
    · exact
        (realEnergy_le_flaggedTargetScale_of_card_le
          hLambda hsmall ha2 ha3 heps).trans <|
          (by
            have hK1 : (1 : ℝ) ≤ K := le_max_right _ _
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hK1
                (flaggedTargetScale_nonneg Lambda a eps (D.piece i)))
  have hpower :
      (∑ i ∈ D.indices, ((D.piece i).card : ℝ) ^ (a + eps)) ≤
        (A.card : ℝ) ^ (a + eps) := by
    simpa using
      (sum_rpow_le_of_le_mul_and_sum_le D.indices
        (fun i => ((D.piece i).card : ℝ))
        (q := 1) (M := (A.card : ℝ)) (p := a + eps)
        (fun i hi => by positivity)
        (fun i hi => by
          have hcard : (D.piece i).card ≤ A.card :=
            Finset.card_le_card (D.piece_subset i hi)
          have hcardR : ((D.piece i).card : ℝ) ≤ (A.card : ℝ) := by
            exact_mod_cast hcard
          simpa using hcardR)
        D.card_sum_le (by norm_num) hM hp)
  have hsumEnergy :
      (∑ i ∈ D.indices, realEnergy (D.piece i)) ≤
        K * flaggedTargetScale Lambda a eps A := by
    calc
      (∑ i ∈ D.indices, realEnergy (D.piece i)) ≤
          ∑ i ∈ D.indices,
            K * flaggedTargetScale Lambda a eps (D.piece i) := by
        exact Finset.sum_le_sum fun i hi => hpiece i hi
      _ = K * (Lambda : ℝ) ^ (3 - a) *
          ∑ i ∈ D.indices,
            ((D.piece i).card : ℝ) ^ (a + eps) := by
        simp only [flaggedTargetScale]
        simp_rw [← mul_assoc]
        rw [Finset.mul_sum]
      _ ≤ K * (Lambda : ℝ) ^ (3 - a) *
          (A.card : ℝ) ^ (a + eps) := by
        exact mul_le_mul_of_nonneg_left hpower (mul_nonneg hK0 hLambdaPow)
      _ = K * flaggedTargetScale Lambda a eps A := by
        simp [flaggedTargetScale, mul_assoc]
  have hJreal : (D.indices.card : ℝ) ≤ J := by exact_mod_cast hJ
  calc
    realEnergy wall = realEnergy (D.indices.biUnion D.piece) := by
      exact congrArg (fun S : Finset (RVec n) => realEnergy S) D.wall_eq
    _ ≤ (D.indices.card : ℝ) ^ (3 : ℕ) *
        ∑ i ∈ D.indices, realEnergy (D.piece i) :=
      energy_biUnion_le_card_cube_mul_sum_unconditional D.indices D.piece
        D.pairwise_disjoint
    _ ≤ (J : ℝ) ^ (3 : ℕ) *
        ∑ i ∈ D.indices, realEnergy (D.piece i) := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hJreal 3) (by positivity)
    _ ≤ (J : ℝ) ^ (3 : ℕ) *
        (K * flaggedTargetScale Lambda a eps A) := by
      exact mul_le_mul_of_nonneg_left hsumEnergy (by positivity)
    _ = (J : ℝ) ^ (3 : ℕ) * max lowerCoefficient 1 *
        flaggedTargetScale Lambda a eps A := by
      simp [K, mul_assoc]

end WallCertificate

/-- Uniform nonrecursive coefficient at a dimension layer: the first term is
the twice-crossed exceptional contribution and the second is the bounded
wall union. -/
noncomputable def nodeBaseCoefficient
    (L J : ℕ) (lowerCoefficient : ℝ) : ℝ :=
  16 * ((L : ℝ) + 1) +
    8 * (J : ℝ) ^ (3 : ℕ) * max lowerCoefficient 1

/-- One certified partition node.  `Eligible` records the hereditary class
on which cardinality induction runs.  The strict-cardinality field prevents
the certificate from hiding a circular invocation of the desired bound. -/
structure NodeCertificate
    (W : PaperVariety n) (Eligible : Finset (RVec n) → Prop)
    (A : Finset (RVec n)) (Lambda R L J : ℕ)
    (a eps cellRatio rho : ℝ) where
  retained : Finset (RVec n)
  wall : Finset (RVec n)
  decomposition : A = retained ∪ wall
  retained_wall_disjoint : Disjoint retained wall
  points_on_node : ∀ x ∈ A, x ∈ W.realPoints
  local_bound : W.LocalConcentrationBound A Lambda
  intrinsic_exponent_le : W.alpha ≤ a
  positive_dimensional : 0 < W.complexDim
  partitionDegree : ℕ
  two_le_partitionDegree : 2 ≤ partitionDegree
  crossing : CrossingCertificate W A retained L
  cell_eligible : ∀ B ∈ crossing.cells, Eligible B
  cell_strict : ∀ B ∈ crossing.cells, B.card < A.card
  cell_size : ∀ B ∈ crossing.cells,
    ((B.card : ℕ) : ℝ) ≤ cellRatio * (A.card : ℝ)
  cell_card_sum :
    (∑ B ∈ crossing.cells, ((B.card : ℕ) : ℝ)) ≤
      (A.card : ℝ)
  wallData : WallCertificate W A wall Lambda R a
  wall_count : wallData.indices.card ≤ J
  /-- This is the checked numerical output of the degree/exponent choice,
  not an energy inequality. -/
  contraction :
    8 * (L : ℝ) ^ (2 : ℕ) *
      cellRatio ^ (a + eps - 1) ≤ rho

namespace NodeCertificate

variable {W : PaperVariety n}
  {Eligible : Finset (RVec n) → Prop}
  {A : Finset (RVec n)} {Lambda R L J : ℕ}
  {a eps cellRatio rho C lowerCoefficient : ℝ}

/-- Single-node verifier.  The recursive hypotheses occur only on certified
strictly smaller cells; wall hypotheses occur only on certified
lower-dimensional components. -/
theorem recurrence_step
    (N : NodeCertificate W Eligible A Lambda R L J
      a eps cellRatio rho)
    (hA : A.Nonempty) (hLambda : 1 ≤ Lambda)
    (ha2 : 2 ≤ a) (ha3 : a ≤ 3) (heps : 0 < eps)
    (hcellRatio : 0 ≤ cellRatio) (hC : 0 ≤ C)
    (hlower : 0 ≤ lowerCoefficient)
    (hCells : ∀ B ∈ N.crossing.cells,
      realEnergy B ≤ C * flaggedTargetScale Lambda a eps B)
    (hLower : ∀ i ∈ N.wallData.indices,
      (N.wallData.variety i).alpha ≤ a →
        realEnergy (N.wallData.piece i) ≤
          lowerCoefficient *
            flaggedTargetScale Lambda a eps (N.wallData.piece i)) :
    realEnergy A ≤
      (nodeBaseCoefficient L J lowerCoefficient + rho * C) *
        flaggedTargetScale Lambda a eps A := by
  classical
  let T := flaggedTargetScale Lambda a eps A
  let bad : ℝ := 2 * ((L : ℝ) + 1) *
    (W.energyLocalLambda A : ℝ) * (A.card : ℝ) ^ (2 : ℕ)
  let cells : ℝ := (L : ℝ) ^ (2 : ℕ) *
    ∑ B ∈ N.crossing.cells, realEnergy B
  have hT0 : 0 ≤ T := flaggedTargetScale_nonneg _ _ _ _
  have hp : 1 ≤ a + eps := by linarith
  have hM : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hcrossNat := N.crossing.two_crossing_local_lambda N.points_on_node
  have hcross : realEnergy N.retained ≤ bad + cells := by
    dsimp only [bad, cells]
    exact_mod_cast hcrossNat
  have hlocal := localLambda_mul_card_sq_le_flaggedTargetScale
    W hA N.local_bound ha2 ha3 heps
  have hbad : 8 * bad ≤ 16 * ((L : ℝ) + 1) * T := by
    dsimp only [bad, T]
    calc
      8 * (2 * ((L : ℝ) + 1) *
          (W.energyLocalLambda A : ℝ) * (A.card : ℝ) ^ (2 : ℕ)) =
          (16 * ((L : ℝ) + 1)) *
            ((W.energyLocalLambda A : ℝ) *
              (A.card : ℝ) ^ (2 : ℕ)) := by ring
      _ ≤ (16 * ((L : ℝ) + 1)) *
          flaggedTargetScale Lambda a eps A := by
        exact mul_le_mul_of_nonneg_left hlocal (by positivity)
      _ = 16 * ((L : ℝ) + 1) *
          flaggedTargetScale Lambda a eps A := by ring
  have hpower :
      (∑ B ∈ N.crossing.cells, ((B.card : ℕ) : ℝ) ^ (a + eps)) ≤
        cellRatio ^ (a + eps - 1) * (A.card : ℝ) ^ (a + eps) :=
    sum_rpow_le_of_le_mul_and_sum_le N.crossing.cells
      (fun B => ((B.card : ℕ) : ℝ))
      (fun B hB => by positivity) N.cell_size N.cell_card_sum
      hcellRatio hM hp
  have hLambdaPow : 0 ≤ (Lambda : ℝ) ^ (3 - a) := by positivity
  have hsumCells :
      (∑ B ∈ N.crossing.cells, realEnergy B) ≤
        C * (Lambda : ℝ) ^ (3 - a) *
          (cellRatio ^ (a + eps - 1) *
            (A.card : ℝ) ^ (a + eps)) := by
    calc
      (∑ B ∈ N.crossing.cells, realEnergy B) ≤
          ∑ B ∈ N.crossing.cells,
            C * flaggedTargetScale Lambda a eps B := by
        exact Finset.sum_le_sum fun B hB => hCells B hB
      _ = C * (Lambda : ℝ) ^ (3 - a) *
          ∑ B ∈ N.crossing.cells,
            ((B.card : ℕ) : ℝ) ^ (a + eps) := by
        simp only [flaggedTargetScale]
        simp_rw [← mul_assoc]
        rw [Finset.mul_sum]
      _ ≤ C * (Lambda : ℝ) ^ (3 - a) *
          (cellRatio ^ (a + eps - 1) *
            (A.card : ℝ) ^ (a + eps)) := by
        exact mul_le_mul_of_nonneg_left hpower (mul_nonneg hC hLambdaPow)
  have hcell : 8 * cells ≤ rho * C * T := by
    dsimp only [cells, T]
    calc
      8 * ((L : ℝ) ^ (2 : ℕ) *
          ∑ B ∈ N.crossing.cells, realEnergy B) =
          (8 * (L : ℝ) ^ (2 : ℕ)) *
            ∑ B ∈ N.crossing.cells, realEnergy B := by ring
      _ ≤ (8 * (L : ℝ) ^ (2 : ℕ)) *
            (C * (Lambda : ℝ) ^ (3 - a) *
              (cellRatio ^ (a + eps - 1) *
                (A.card : ℝ) ^ (a + eps))) := by
        exact mul_le_mul_of_nonneg_left hsumCells (by positivity)
      _ = (8 * (L : ℝ) ^ (2 : ℕ) *
            cellRatio ^ (a + eps - 1)) *
          (C * flaggedTargetScale Lambda a eps A) := by
        simp only [flaggedTargetScale]
        ring
      _ ≤ rho * (C * flaggedTargetScale Lambda a eps A) := by
        exact mul_le_mul_of_nonneg_right N.contraction (mul_nonneg hC hT0)
      _ = rho * C * flaggedTargetScale Lambda a eps A := by ring
  have hwall := N.wallData.energy_le N.wall_count hA hLambda
    ha2 ha3 heps hlower hLower
  have hwall8 : 8 * realEnergy N.wall ≤
      8 * (J : ℝ) ^ (3 : ℕ) * max lowerCoefficient 1 * T := by
    dsimp only [T]
    calc
      8 * realEnergy N.wall ≤
          8 * ((J : ℝ) ^ (3 : ℕ) * max lowerCoefficient 1 *
            flaggedTargetScale Lambda a eps A) := by
        exact mul_le_mul_of_nonneg_left hwall (by norm_num)
      _ = 8 * (J : ℝ) ^ (3 : ℕ) * max lowerCoefficient 1 *
          flaggedTargetScale Lambda a eps A := by ring
  have houter : realEnergy A ≤
      8 * (realEnergy N.retained + realEnergy N.wall) := by
    calc
      realEnergy A = realEnergy (N.retained ∪ N.wall) :=
        congrArg (fun S : Finset (RVec n) => realEnergy S) N.decomposition
      _ ≤ 8 * (realEnergy N.retained + realEnergy N.wall) :=
        energy_union_le_eight_unconditional _ _ N.retained_wall_disjoint
  calc
    realEnergy A ≤ 8 * (realEnergy N.retained + realEnergy N.wall) := houter
    _ ≤ 8 * ((bad + cells) + realEnergy N.wall) := by
      gcongr
    _ = 8 * bad + 8 * cells + 8 * realEnergy N.wall := by ring
    _ ≤ 16 * ((L : ℝ) + 1) * T + rho * C * T +
        8 * (J : ℝ) ^ (3 : ℕ) * max lowerCoefficient 1 * T :=
      add_le_add (add_le_add hbad hcell) hwall8
    _ = (nodeBaseCoefficient L J lowerCoefficient + rho * C) *
        flaggedTargetScale Lambda a eps A := by
      dsimp only [T, nodeBaseCoefficient]
      ring

end NodeCertificate

/-- The explicit fixed point used for cardinality induction at one dimension
layer. -/
noncomputable def flaggedInductionConstant
    (L J : ℕ) (lowerCoefficient rho : ℝ) : ℝ :=
  nodeBaseCoefficient L J lowerCoefficient / (1 - rho)

/-- Lexicographic induction principle matching the paper's two inductions:
walls decrease dimension, while cells preserve dimension and strictly
decrease cardinality. -/
theorem dimension_cardinality_strong_induction
    {P : ℕ → ℕ → Prop}
    (hstep : ∀ k M,
      (∀ j < k, ∀ m, P j m) →
      (∀ m < M, P k m) → P k M) :
    ∀ k M, P k M := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ihDimension =>
      intro M
      induction M using Nat.strong_induction_on with
      | h M ihCardinality =>
          exact hstep k M
            (fun j hj m => ihDimension j hj m)
            (fun m hm => ihCardinality m hm)

/-- Strong-induction closure of the certified single-node recurrence.

The lower-dimensional estimate is an explicit hypothesis.  It is therefore
impossible to use the conclusion recursively on a wall of the same
dimension.  Same-dimensional recursion is accepted only through
`cell_strict`. -/
theorem flagged_energy_cardinality_strong_induction
    {W : PaperVariety n}
    {Eligible : Finset (RVec n) → Prop}
    {Lambda R L J : ℕ} {a eps cellRatio rho lowerCoefficient : ℝ}
    (hLambda : 1 ≤ Lambda)
    (ha2 : 2 ≤ a) (ha3 : a < 3) (heps : 0 < eps)
    (hcellRatio : 0 ≤ cellRatio)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hlower : 0 ≤ lowerCoefficient)
    (certify : ∀ A, Eligible A → A.Nonempty →
      NodeCertificate W Eligible A Lambda R L J
        a eps cellRatio rho)
    (hLower : ∀ A, Eligible A → ∀ _hA : A.Nonempty,
      ∀ N : NodeCertificate W Eligible A Lambda R L J
        a eps cellRatio rho,
      ∀ i ∈ N.wallData.indices,
        (N.wallData.variety i).alpha ≤ a →
          realEnergy (N.wallData.piece i) ≤
            lowerCoefficient * flaggedTargetScale Lambda a eps
              (N.wallData.piece i)) :
    ∀ A, Eligible A →
      realEnergy A ≤
        flaggedInductionConstant L J lowerCoefficient rho *
          flaggedTargetScale Lambda a eps A := by
  classical
  let base := nodeBaseCoefficient L J lowerCoefficient
  let Cstar := flaggedInductionConstant L J lowerCoefficient rho
  have hbase0 : 0 ≤ base := by
    dsimp only [base, nodeBaseCoefficient]
    positivity
  have hden0 : 0 ≤ 1 - rho := sub_nonneg.mpr hrho1.le
  have hCstar0 : 0 ≤ Cstar := by
    exact div_nonneg hbase0 hden0
  have hclose : base + rho * Cstar ≤ Cstar := by
    have hclosed := close_contractive_strong_induction
      (u := fun _ : ℕ => base + rho * Cstar)
      hbase0 hrho0 hrho1
      (by
        intro m ih
        change base + rho * Cstar ≤ base + rho * Cstar
        exact le_rfl)
    simpa only [Cstar, flaggedInductionConstant, base] using hclosed 0
  have hall : ∀ m : ℕ, ∀ A : Finset (RVec n),
      A.card = m → Eligible A →
        realEnergy A ≤ Cstar * flaggedTargetScale Lambda a eps A := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro A hcard hEligible
        by_cases hA : A.Nonempty
        · let N := certify A hEligible hA
          have hCells : ∀ B ∈ N.crossing.cells,
              realEnergy B ≤
                Cstar * flaggedTargetScale Lambda a eps B := by
            intro B hB
            have hlt : B.card < m :=
              (N.cell_strict B hB).trans_le hcard.le
            exact ih B.card hlt B rfl (N.cell_eligible B hB)
          have hstep := N.recurrence_step hA hLambda
            ha2 ha3.le heps hcellRatio hCstar0 hlower hCells
            (hLower A hEligible hA N)
          exact hstep.trans <| by
            exact mul_le_mul_of_nonneg_right hclose
              (flaggedTargetScale_nonneg Lambda a eps A)
        · have hEmpty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
          subst A
          have hp : 0 < a + eps := by linarith
          simp [flaggedTargetScale, Cstar, Real.zero_rpow hp.ne']
  intro A hEligible
  simpa only [Cstar] using hall A.card A rfl hEligible

end ComplexitySensitiveEnergy.PaperVariety
