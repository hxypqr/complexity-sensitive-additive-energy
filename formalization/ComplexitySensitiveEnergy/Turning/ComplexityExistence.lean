import ComplexitySensitiveEnergy.Turning.Definitions

/-!
# Existence and uniqueness of turning complexity

Every ordered configuration admits the partition into singleton blocks.
Consequently the set of admissible block-count bounds is nonempty, and its
least natural number is the unique turning complexity.
-/

namespace ComplexitySensitiveEnergy.Turning

/-- The canonical partition into one singleton block per point. -/
def singletonBlocks (P : OrderedConfiguration) : List (List R2) :=
  P.points.map fun p => [p]

theorem singletonBlocks_isSignedConvexPartition (P : OrderedConfiguration) :
    IsSignedConvexPartition P (singletonBlocks P) := by
  unfold singletonBlocks
  constructor
  · induction P.points with
    | nil => rfl
    | cons p ps ih => simp [ih]
  · induction P.points with
    | nil => simp
    | cons p ps ih =>
        simp only [List.map_cons, List.forall_cons]
        refine ⟨?_, ih⟩
        constructor
        · simp
        · exact Or.inl (by simp [adjacentSlopes])

/-- The singleton partition supplies the elementary finite upper bound
`κ(P) ≤ |P|`. -/
theorem hasSignedConvexPartitionAtMost_length (P : OrderedConfiguration) :
    HasSignedConvexPartitionAtMost P P.points.length := by
  refine ⟨singletonBlocks P, singletonBlocks_isSignedConvexPartition P, ?_⟩
  simp [singletonBlocks]

/-- The least admissible block-count bound. -/
noncomputable def turningComplexity (P : OrderedConfiguration) : ℕ :=
  by
    classical
    exact Nat.find
      ⟨P.points.length, hasSignedConvexPartitionAtMost_length P⟩

theorem hasTurningComplexity_turningComplexity (P : OrderedConfiguration) :
    HasTurningComplexity P (turningComplexity P) := by
  classical
  unfold turningComplexity
  constructor
  · exact Nat.find_spec
      (⟨P.points.length, hasSignedConvexPartitionAtMost_length P⟩ :
        ∃ k, HasSignedConvexPartitionAtMost P k)
  · intro k hk
    exact Nat.find_min
      (⟨P.points.length, hasSignedConvexPartitionAtMost_length P⟩ :
        ∃ k, HasSignedConvexPartitionAtMost P k) hk

/-- Minimal turning complexity is unique. -/
theorem hasTurningComplexity_unique (P : OrderedConfiguration) {k l : ℕ}
    (hk : HasTurningComplexity P k) (hl : HasTurningComplexity P l) :
    k = l := by
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · exact False.elim ((hl.2 k hkl) hk.1)
  · exact hkl
  · exact False.elim ((hk.2 l hlk) hl.1)

/-- Every ordered configuration has exactly one turning complexity. -/
theorem exists_unique_hasTurningComplexity (P : OrderedConfiguration) :
    ∃! k : ℕ, HasTurningComplexity P k := by
  refine ⟨turningComplexity P, hasTurningComplexity_turningComplexity P, ?_⟩
  intro k hk
  exact hasTurningComplexity_unique P hk
    (hasTurningComplexity_turningComplexity P)

end ComplexitySensitiveEnergy.Turning
