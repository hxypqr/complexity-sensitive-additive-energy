import Mathlib
import ComplexitySensitiveEnergy.Additive.HigherEnergy
import ComplexitySensitiveEnergy.Algebraic.Variety

/-!
# Signed-convex turning complexity

The paper defines `κ_ℓ(P)` after ordering a finite planar set by an
injective linear functional `ℓ`.  We keep that ordering as data.  The
predicate `HasTurningComplexity` says exactly that `K` is the least number of
consecutive signed-convex blocks, without making a noncomputable choice of a
minimum.
-/

namespace ComplexitySensitiveEnergy.Turning

abbrev R2 := RVec 2

/-- Ordered planar points together with the two linear coordinates used to
form slopes. -/
structure OrderedConfiguration where
  points : List R2
  nodup : points.Nodup
  ell : LinearMap (RingHom.id ℝ) R2 ℝ
  transverse : LinearMap (RingHom.id ℝ) R2 ℝ
  /-- The two displayed functionals are complementary coordinates on
  `ℝ²`, as required in the paper. -/
  coordinates_injective :
    Function.Injective (fun p : R2 => (ell p, transverse p))
  ell_strict : (points.map ell).Pairwise (fun x y => x < y)

/-- Adjacent slopes for a list of points. -/
noncomputable def adjacentSlopes
    (ell transverse : LinearMap (RingHom.id ℝ) R2 ℝ) : List R2 → List ℝ
  | p :: q :: rest =>
      (transverse q - transverse p) / (ell q - ell p) ::
        adjacentSlopes ell transverse (q :: rest)
  | _ => []

/-- A consecutive block is signed-convex when its adjacent slopes are
strictly increasing or strictly decreasing. -/
def IsSignedConvexBlock
    (ell transverse : LinearMap (RingHom.id ℝ) R2 ℝ)
    (block : List R2) : Prop :=
  (adjacentSlopes ell transverse block).Pairwise (fun x y => x < y) ∨
    (adjacentSlopes ell transverse block).Pairwise (fun x y => x > y)

/-- A list of nonempty blocks is a consecutive signed-convex partition of
the ordered configuration. -/
def IsSignedConvexPartition (P : OrderedConfiguration)
    (blocks : List (List R2)) : Prop :=
  blocks.flatten = P.points ∧
  blocks.Forall (fun block => block ≠ [] ∧
    IsSignedConvexBlock P.ell P.transverse block)

/-- Upper-bound formulation `κ_ℓ(P) ≤ K`. -/
def HasSignedConvexPartitionAtMost (P : OrderedConfiguration) (K : ℕ) : Prop :=
  ∃ blocks : List (List R2),
    IsSignedConvexPartition P blocks ∧ blocks.length ≤ K

/-- Exact formulation `κ_ℓ(P) = K`. -/
def HasTurningComplexity (P : OrderedConfiguration) (K : ℕ) : Prop :=
  HasSignedConvexPartitionAtMost P K ∧
    ∀ k < K, ¬ HasSignedConvexPartitionAtMost P k

/-- The finite point set underlying an ordered configuration. -/
noncomputable def pointSet (P : OrderedConfiguration) : Finset R2 := P.points.toFinset

@[simp] theorem card_pointSet (P : OrderedConfiguration) :
    (pointSet P).card = P.points.length := by
  classical
  exact List.toFinset_card_of_nodup P.nodup

/-- Upper-bound form of Theorem 1.4.  Using any partition with at most `K`
blocks is slightly stronger and avoids selecting a minimizing partition. -/
def TurningComplexityUpperStatement : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : OrderedConfiguration) (K : ℕ),
      1 ≤ K → HasSignedConvexPartitionAtMost P K →
      (J3 (pointSet P) : ℝ) ≤
        C * (K : ℝ) ^ 2 * ((pointSet P).card : ℝ) ^ (3 + eps)

/-- Exact quantifier expansion of the “matching examples” clause in
Theorem 1.4.  Constants are absolute and uniform in `K,n`. -/
def TurningComplexitySharpStatement : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    ∀ K n : ℕ, 1 ≤ K → 1 ≤ n →
      ∃ P : OrderedConfiguration,
        (pointSet P).card = K * n ∧
        (∃ k : ℕ, HasTurningComplexity P k ∧
          c * (K : ℝ) ≤ (k : ℝ) ∧
          (k : ℝ) ≤ C * (K : ℝ)) ∧
        c * (K : ℝ) ^ 2 * ((pointSet P).card : ℝ) ^ 3 ≤
          (J3 (pointSet P) : ℝ) ∧
        (J3 (pointSet P) : ℝ) ≤
          C * (K : ℝ) ^ 2 * ((pointSet P).card : ℝ) ^ 3

/-- Paper-facing conjunction of the two parts of Theorem 1.4. -/
def Theorem14Statement : Prop :=
  TurningComplexityUpperStatement ∧ TurningComplexitySharpStatement

end ComplexitySensitiveEnergy.Turning
