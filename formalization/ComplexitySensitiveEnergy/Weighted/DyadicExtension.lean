import Mathlib
import ComplexitySensitiveEnergy.Weighted.Correlation

/-!
# Finite dyadic extension of hereditary energy estimates

This file separates three logically different steps in the weighted argument.

* `dyadicLevel` is the canonical level
  `2^(-(j+1)) < ‖f x‖ ≤ 2^(-j)` inside a finite support.
* The phase of a complex coefficient is removed internally, by applying the
  correlation estimates proved in `Weighted.Correlation` on every level.
* A purely finite fourth-power inequality assembles level estimates for any
  nonnegative, subadditive size functional.

The last step deliberately does **not** assert that the correlation energy of
a sum is bounded by the sum of the self-correlation energies of its levels:
there are cross-level terms.  To obtain a theorem about the original function,
`finiteDyadicExtension` therefore asks for the usual Fourier `L⁴` realization
(or any other subadditive size) explicitly.  Thus the standard Fourier/Parseval
interface remains visible at the trust boundary, while the complex restricted
type and finite dyadic arguments are proved here.
-/

open scoped BigOperators

namespace ComplexitySensitiveEnergy

noncomputable section

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-! ## Canonical dyadic levels -/

/-- The upper amplitude of dyadic level `j`, namely `2⁻ʲ`. -/
def dyadicScale (j : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ j

@[simp]
theorem dyadicScale_zero : dyadicScale 0 = 1 := by
  simp [dyadicScale]

theorem dyadicScale_pos (j : ℕ) : 0 < dyadicScale j := by
  unfold dyadicScale
  positivity

theorem dyadicScale_nonneg (j : ℕ) : 0 ≤ dyadicScale j :=
  (dyadicScale_pos j).le

@[simp]
theorem dyadicScale_succ (j : ℕ) :
    dyadicScale (j + 1) = dyadicScale j / 2 := by
  simp [dyadicScale, pow_succ, div_eq_mul_inv, mul_comm]

theorem dyadicScale_antitone : Antitone dyadicScale := by
  intro i j hij
  exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 ≤ 1) hij

/-- The points of `A` whose coefficient has size in
`(2^(-(j+1)), 2^(-j)]`.  Zero coefficients occur in no level. -/
def dyadicLevel (A : Finset G) (f : G → ℂ) (j : ℕ) : Finset G :=
  A.filter fun x ↦
    dyadicScale (j + 1) < ‖f x‖ ∧ ‖f x‖ ≤ dyadicScale j

@[simp]
theorem mem_dyadicLevel {A : Finset G} {f : G → ℂ} {j : ℕ} {x : G} :
    x ∈ dyadicLevel A f j ↔
      x ∈ A ∧ dyadicScale (j + 1) < ‖f x‖ ∧
        ‖f x‖ ≤ dyadicScale j := by
  simp [dyadicLevel]

theorem dyadicLevel_subset (A : Finset G) (f : G → ℂ) (j : ℕ) :
    dyadicLevel A f j ⊆ A := by
  intro x hx
  exact (mem_dyadicLevel.mp hx).1

theorem norm_le_dyadicScale_of_mem {A : Finset G} {f : G → ℂ}
    {j : ℕ} {x : G} (hx : x ∈ dyadicLevel A f j) :
    ‖f x‖ ≤ dyadicScale j :=
  (mem_dyadicLevel.mp hx).2.2

theorem dyadicLevel_disjoint (A : Finset G) (f : G → ℂ)
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint (dyadicLevel A f i) (dyadicLevel A f j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hscale : dyadicScale j ≤ dyadicScale (i + 1) :=
      dyadicScale_antitone (Nat.succ_le_of_lt hij')
    have hiLower := (mem_dyadicLevel.mp hxi).2.1
    have hjUpper := (mem_dyadicLevel.mp hxj).2.2
    linarith
  · have hscale : dyadicScale i ≤ dyadicScale (j + 1) :=
      dyadicScale_antitone (Nat.succ_le_of_lt hji')
    have hjLower := (mem_dyadicLevel.mp hxj).2.1
    have hiUpper := (mem_dyadicLevel.mp hxi).2.2
    linarith

/-- Restrict a complex coefficient function to one canonical dyadic level. -/
def dyadicRestriction (A : Finset G) (f : G → ℂ) (j : ℕ) : G → ℂ :=
  fun x ↦ if x ∈ dyadicLevel A f j then f x else 0

@[simp]
theorem dyadicRestriction_of_mem {A : Finset G} {f : G → ℂ}
    {j : ℕ} {x : G} (hx : x ∈ dyadicLevel A f j) :
    dyadicRestriction A f j x = f x := by
  simp [dyadicRestriction, hx]

@[simp]
theorem dyadicRestriction_of_not_mem {A : Finset G} {f : G → ℂ}
    {j : ℕ} {x : G} (hx : x ∉ dyadicLevel A f j) :
    dyadicRestriction A f j x = 0 := by
  simp [dyadicRestriction, hx]

theorem norm_dyadicRestriction_le_of_mem {A : Finset G} {f : G → ℂ}
    {j : ℕ} {x : G} (hx : x ∈ dyadicLevel A f j) :
    ‖dyadicRestriction A f j x‖ ≤ dyadicScale j := by
  rw [dyadicRestriction_of_mem hx]
  exact norm_le_dyadicScale_of_mem hx

/-- Every nonzero coefficient of size at most one belongs to a dyadic level. -/
theorem exists_mem_dyadicLevel {A : Finset G} {f : G → ℂ} {x : G}
    (hxA : x ∈ A) (hx0 : f x ≠ 0) (hx1 : ‖f x‖ ≤ 1) :
    ∃ j : ℕ, x ∈ dyadicLevel A f j := by
  have hxpos : 0 < ‖f x‖ := norm_pos_iff.mpr hx0
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < ‖f x‖ :=
    exists_pow_lt_of_lt_one hxpos (by norm_num)
  have hex : ∃ n : ℕ, dyadicScale n < ‖f x‖ := by
    exact ⟨n, by simpa [dyadicScale] using hn⟩
  have hfind_spec : dyadicScale (Nat.find hex) < ‖f x‖ :=
    Nat.find_spec hex
  have hfind_ne : Nat.find hex ≠ 0 := by
    intro hzero
    rw [hzero, dyadicScale_zero] at hfind_spec
    linarith
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hfind_ne
  have hj_spec : dyadicScale (j + 1) < ‖f x‖ := by
    rw [hj] at hfind_spec
    simpa [Nat.succ_eq_add_one] using hfind_spec
  have hj_not : ¬dyadicScale j < ‖f x‖ := by
    apply Nat.find_min hex
    rw [hj]
    exact Nat.lt_succ_self j
  refine ⟨j, mem_dyadicLevel.mpr ⟨hxA, hj_spec, ?_⟩⟩
  exact le_of_not_gt hj_not

/-- A finite support with coefficients bounded by one is covered by finitely
many canonical dyadic levels. -/
theorem exists_finite_dyadic_cover (A : Finset G) (f : G → ℂ)
    (hf : ∀ x ∈ A, ‖f x‖ ≤ 1) :
    ∃ levels : Finset ℕ,
      ∀ x ∈ A, f x ≠ 0 →
        ∃ j ∈ levels, x ∈ dyadicLevel A f j := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      exact ⟨∅, by simp⟩
  | @insert x A hx ih =>
      have hfA : ∀ y ∈ A, ‖f y‖ ≤ 1 := by
        intro y hy
        exact hf y (Finset.mem_insert_of_mem hy)
      obtain ⟨levels, hlevels⟩ := ih hfA
      by_cases hx0 : f x = 0
      · refine ⟨levels, ?_⟩
        intro y hy hy0
        rcases Finset.mem_insert.mp hy with rfl | hyA
        · exact (hy0 hx0).elim
        · obtain ⟨k, hk, hykA⟩ := hlevels y hyA hy0
          have hyk : y ∈ dyadicLevel (insert x A) f k := by
            rw [mem_dyadicLevel] at hykA ⊢
            exact ⟨Finset.mem_insert_of_mem hykA.1, hykA.2⟩
          exact ⟨k, hk, hyk⟩
      · obtain ⟨j, hj⟩ := exists_mem_dyadicLevel
          (A := insert x A) (f := f) (x := x) (by simp) hx0 (hf x (by simp))
        refine ⟨insert j levels, ?_⟩
        intro y hy hy0
        rcases Finset.mem_insert.mp hy with rfl | hyA
        · exact ⟨j, by simp, hj⟩
        · obtain ⟨k, hk, hykA⟩ := hlevels y hyA hy0
          have hyk : y ∈ dyadicLevel (insert x A) f k := by
            rw [mem_dyadicLevel] at hykA ⊢
            exact ⟨Finset.mem_insert_of_mem hykA.1, hykA.2⟩
          exact ⟨k, by simp [hk], hyk⟩

/-- If the selected levels cover all nonzero coefficients on `A`, and `f`
vanishes off `A`, then their restrictions sum exactly to `f`. -/
theorem sum_dyadicRestriction_eq
    (A : Finset G) (f : G → ℂ) (levels : Finset ℕ)
    (hsupport : ∀ x ∉ A, f x = 0)
    (hcover : ∀ x ∈ A, f x ≠ 0 →
      ∃ j ∈ levels, x ∈ dyadicLevel A f j) :
    (∑ j ∈ levels, dyadicRestriction A f j) = f := by
  classical
  funext x
  simp only [Finset.sum_apply]
  by_cases hx0 : f x = 0
  · simp [dyadicRestriction, hx0]
  by_cases hxA : x ∈ A
  · obtain ⟨j, hj, hxj⟩ := hcover x hxA hx0
    rw [Finset.sum_eq_single j]
    · exact dyadicRestriction_of_mem hxj
    · intro k hk hkj
      have hxk : x ∉ dyadicLevel A f k := by
        intro hxk
        exact (Finset.disjoint_left.mp
          (dyadicLevel_disjoint A f hkj) hxk hxj)
      exact dyadicRestriction_of_not_mem hxk
    · exact fun hnot ↦ (hnot hj).elim
  · have hfx := hsupport x hxA
    exact (hx0 hfx).elim

/-- Every finitely supported coefficient function bounded by one admits an
exact finite canonical dyadic decomposition. -/
theorem exists_finite_dyadic_decomposition
    (A : Finset G) (f : G → ℂ)
    (hsupport : ∀ x ∉ A, f x = 0)
    (hf : ∀ x ∈ A, ‖f x‖ ≤ 1) :
    ∃ levels : Finset ℕ,
      (∑ j ∈ levels, dyadicRestriction A f j) = f := by
  obtain ⟨levels, hcover⟩ := exists_finite_dyadic_cover A f hf
  exact ⟨levels, sum_dyadicRestriction_eq A f levels hsupport hcover⟩

/-! ## Hereditary energy bounds and phase-safe level estimates -/

/-- A set-energy estimate which is valid for every subset of `A`.  The
function `profile n` is the desired upper bound for a set of cardinality `n`.
This form includes power profiles without fixing an exponent prematurely. -/
def HereditaryEnergyBound (A : Finset G) (profile : ℕ → ℝ) : Prop :=
  ∀ B : Finset G, B ⊆ A → (energy B : ℝ) ≤ profile B.card

/-- The power profile `C n^p` used in the paper's applications. -/
def powerEnergyProfile (C p : ℝ) (n : ℕ) : ℝ :=
  C * (n : ℝ) ^ p

/-- The pointwise complex phase majorant on a dyadic level.  This is a direct
application of `norm_weightedDifferenceCorrelation_le_representation`; no
indicator-to-complex restricted-type principle is assumed. -/
theorem dyadicLevel_phase_majorant
    (A : Finset G) (f : G → ℂ) (j : ℕ) (t : G) :
    ‖weightedDifferenceCorrelation (dyadicLevel A f j)
        (dyadicRestriction A f j) t‖ ≤
      dyadicScale j ^ 2 *
        (differenceRepresentation (dyadicLevel A f j)
          (dyadicLevel A f j) t : ℝ) := by
  apply norm_weightedDifferenceCorrelation_le_representation
  · exact dyadicScale_nonneg j
  · intro x hx
    exact norm_dyadicRestriction_le_of_mem hx

/-- The squared-correlation estimate on one dyadic level.  Complex phases
have already been dealt with by `Weighted.Correlation`. -/
theorem dyadicLevel_weightedCorrelationSquareSum_le
    (A : Finset G) (f : G → ℂ) (j : ℕ) :
    weightedCorrelationSquareSum (dyadicLevel A f j)
        (dyadicRestriction A f j) ≤
      dyadicScale j ^ 4 * (energy (dyadicLevel A f j) : ℝ) := by
  apply weightedCorrelationSquareSum_le
  · exact dyadicScale_nonneg j
  · intro x hx
    exact norm_dyadicRestriction_le_of_mem hx

/-- Apply a hereditary set-energy bound after the internally proved complex
phase estimate on one level. -/
theorem dyadicLevel_weightedCorrelationSquareSum_le_of_hereditary
    (A : Finset G) (f : G → ℂ) (profile : ℕ → ℝ)
    (henergy : HereditaryEnergyBound A profile) (j : ℕ) :
    weightedCorrelationSquareSum (dyadicLevel A f j)
        (dyadicRestriction A f j) ≤
      dyadicScale j ^ 4 * profile (dyadicLevel A f j).card := by
  refine (dyadicLevel_weightedCorrelationSquareSum_le A f j).trans ?_
  exact mul_le_mul_of_nonneg_left
    (henergy (dyadicLevel A f j) (dyadicLevel_subset A f j))
    (by positivity)

/-- Power-profile specialization of the hereditary level estimate. -/
theorem dyadicLevel_weightedCorrelationSquareSum_le_power
    (A : Finset G) (f : G → ℂ) (C p : ℝ)
    (henergy : HereditaryEnergyBound A (powerEnergyProfile C p)) (j : ℕ) :
    weightedCorrelationSquareSum (dyadicLevel A f j)
        (dyadicRestriction A f j) ≤
      dyadicScale j ^ 4 *
        (C * ((dyadicLevel A f j).card : ℝ) ^ p) := by
  simpa [powerEnergyProfile] using
    dyadicLevel_weightedCorrelationSquareSum_le_of_hereditary
      A f (powerEnergyProfile C p) henergy j

/-! ## Purely finite triangle and fourth-power assembly -/

/-- A finite triangle inequality derived from the zero and binary triangle
laws of an abstract nonnegative size functional. -/
theorem size_finset_sum_le
    {ι V : Type*} [AddCommMonoid V]
    (size : V → ℝ)
    (hzero : size 0 = 0)
    (hadd : ∀ u v, size (u + v) ≤ size u + size v)
    (s : Finset ι) (v : ι → V) :
    size (∑ i ∈ s, v i) ≤ ∑ i ∈ s, size (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      calc
        size (v i + ∑ k ∈ s, v k)
            ≤ size (v i) + size (∑ k ∈ s, v k) := hadd _ _
        _ ≤ size (v i) + ∑ k ∈ s, size (v k) := by gcongr

/-- Finite `L¹ → L⁴` power-sum inequality. -/
theorem sum_fourth_le_card_cube_mul_sum_fourth
    {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i) :
    (∑ i ∈ s, u i) ^ 4 ≤
      (s.card : ℝ) ^ 3 * ∑ i ∈ s, u i ^ 4 := by
  simpa using
    (pow_sum_le_card_mul_sum_pow (s := s) (f := u) hu 3)

/-- Assemble fourth-power majorants for finitely many vectors under an
abstract seminorm-like triangle law.  This is the numerical Lorentz step. -/
theorem finiteLevel_fourthPower_le
    {ι V : Type*} [AddCommMonoid V]
    (levels : Finset ι) (v : ι → V) (size : V → ℝ) (majorant : ι → ℝ)
    (hsize : ∀ u, 0 ≤ size u)
    (hzero : size 0 = 0)
    (hadd : ∀ u w, size (u + w) ≤ size u + size w)
    (hlevel : ∀ i ∈ levels, size (v i) ^ 4 ≤ majorant i) :
    size (∑ i ∈ levels, v i) ^ 4 ≤
      (levels.card : ℝ) ^ 3 * ∑ i ∈ levels, majorant i := by
  have htriangle := size_finset_sum_le size hzero hadd levels v
  have hpow : size (∑ i ∈ levels, v i) ^ 4 ≤
      (∑ i ∈ levels, size (v i)) ^ 4 :=
    pow_le_pow_left₀ (hsize _) htriangle 4
  have hfinite := sum_fourth_le_card_cube_mul_sum_fourth
    levels (fun i ↦ size (v i)) (fun i _ ↦ hsize (v i))
  have hmaj : (∑ i ∈ levels, size (v i) ^ 4) ≤
      ∑ i ∈ levels, majorant i :=
    Finset.sum_le_sum hlevel
  calc
    size (∑ i ∈ levels, v i) ^ 4
        ≤ (∑ i ∈ levels, size (v i)) ^ 4 := hpow
    _ ≤ (levels.card : ℝ) ^ 3 *
          ∑ i ∈ levels, size (v i) ^ 4 := hfinite
    _ ≤ (levels.card : ℝ) ^ 3 *
          ∑ i ∈ levels, majorant i :=
      mul_le_mul_of_nonneg_left hmaj (by positivity)

/-! ## Conditional Fourier/L⁴-facing conclusions -/

/-- Finite dyadic extension under an explicitly supplied subadditive `L⁴`
size.  The hypothesis `hcorrelation` is exactly the standard Fourier/Parseval
realization needed to compare the fourth power of the level size with its
correlation square sum.  Every subsequent phase, hereditary, and finite-level
step is proved in this file. -/
theorem finiteDyadicExtension
    (A : Finset G) (f : G → ℂ) (levels : Finset ℕ)
    (profile : ℕ → ℝ) (size : (G → ℂ) → ℝ)
    (hsize : ∀ u, 0 ≤ size u)
    (hzero : size 0 = 0)
    (hadd : ∀ u v, size (u + v) ≤ size u + size v)
    (hcorrelation : ∀ j ∈ levels,
      size (dyadicRestriction A f j) ^ 4 ≤
        weightedCorrelationSquareSum (dyadicLevel A f j)
          (dyadicRestriction A f j))
    (henergy : HereditaryEnergyBound A profile) :
    size (∑ j ∈ levels, dyadicRestriction A f j) ^ 4 ≤
      (levels.card : ℝ) ^ 3 *
        ∑ j ∈ levels,
          dyadicScale j ^ 4 * profile (dyadicLevel A f j).card := by
  apply finiteLevel_fourthPower_le levels
    (fun j ↦ dyadicRestriction A f j) size
    (fun j ↦ dyadicScale j ^ 4 * profile (dyadicLevel A f j).card)
    hsize hzero hadd
  intro j hj
  exact (hcorrelation j hj).trans
    (dyadicLevel_weightedCorrelationSquareSum_le_of_hereditary
      A f profile henergy j)

/-- Total-function form of `finiteDyadicExtension`.  Exact recovery of `f`
is proved combinatorially from finite support and level coverage; the only
analytic interface left as a hypothesis is the displayed levelwise
Fourier/`L⁴` comparison. -/
theorem finiteDyadicExtension_of_cover
    (A : Finset G) (f : G → ℂ) (levels : Finset ℕ)
    (profile : ℕ → ℝ) (size : (G → ℂ) → ℝ)
    (hsupport : ∀ x ∉ A, f x = 0)
    (hcover : ∀ x ∈ A, f x ≠ 0 →
      ∃ j ∈ levels, x ∈ dyadicLevel A f j)
    (hsize : ∀ u, 0 ≤ size u)
    (hzero : size 0 = 0)
    (hadd : ∀ u v, size (u + v) ≤ size u + size v)
    (hcorrelation : ∀ j ∈ levels,
      size (dyadicRestriction A f j) ^ 4 ≤
        weightedCorrelationSquareSum (dyadicLevel A f j)
          (dyadicRestriction A f j))
    (henergy : HereditaryEnergyBound A profile) :
    size f ^ 4 ≤
      (levels.card : ℝ) ^ 3 *
        ∑ j ∈ levels,
          dyadicScale j ^ 4 * profile (dyadicLevel A f j).card := by
  calc
    size f ^ 4 =
        size (∑ j ∈ levels, dyadicRestriction A f j) ^ 4 := by
      rw [sum_dyadicRestriction_eq A f levels hsupport hcover]
    _ ≤ (levels.card : ℝ) ^ 3 *
          ∑ j ∈ levels,
            dyadicScale j ^ 4 * profile (dyadicLevel A f j).card :=
      finiteDyadicExtension A f levels profile size hsize hzero hadd
        hcorrelation henergy

/-- Existential finite-support form of the dyadic extension.  For a function
supported on `A` with `‖f x‖ ≤ 1`, the finite collection of required dyadic
levels is constructed internally. -/
theorem exists_finiteDyadicExtension
    (A : Finset G) (f : G → ℂ)
    (profile : ℕ → ℝ) (size : (G → ℂ) → ℝ)
    (hsupport : ∀ x ∉ A, f x = 0)
    (hbounded : ∀ x ∈ A, ‖f x‖ ≤ 1)
    (hsize : ∀ u, 0 ≤ size u)
    (hzero : size 0 = 0)
    (hadd : ∀ u v, size (u + v) ≤ size u + size v)
    (hcorrelation : ∀ j : ℕ,
      size (dyadicRestriction A f j) ^ 4 ≤
        weightedCorrelationSquareSum (dyadicLevel A f j)
          (dyadicRestriction A f j))
    (henergy : HereditaryEnergyBound A profile) :
    ∃ levels : Finset ℕ,
      size f ^ 4 ≤
        (levels.card : ℝ) ^ 3 *
          ∑ j ∈ levels,
            dyadicScale j ^ 4 * profile (dyadicLevel A f j).card := by
  obtain ⟨levels, hcover⟩ := exists_finite_dyadic_cover A f hbounded
  refine ⟨levels, finiteDyadicExtension_of_cover A f levels profile size
    hsupport hcover hsize hzero hadd ?_ henergy⟩
  intro j _
  exact hcorrelation j

end

end ComplexitySensitiveEnergy
