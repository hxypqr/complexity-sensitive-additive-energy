import ComplexitySensitiveEnergy.External.Literature
import ComplexitySensitiveEnergy.Turning.Definitions

/-!
# Strictly concave leaves reduce to the convex CDW theorem

Reflection in the second coordinate is an additive equivalence, so it
preserves every three-fold additive relation.  This discharges the decreasing
slope leaves without adding a second external theorem.
-/

namespace ComplexitySensitiveEnergy.Turning

open External

def reflectSecond : R2 →+ R2 where
  toFun p i := if i = 0 then p i else -p i
  map_zero' := by
    funext i
    fin_cases i <;> simp
  map_add' p q := by
    funext i
    fin_cases i <;> simp [add_comm]

@[simp] theorem reflectSecond_involutive (p : R2) :
    reflectSecond (reflectSecond p) = p := by
  funext i
  fin_cases i <;> simp [reflectSecond]

theorem reflectSecond_injective : Function.Injective reflectSecond := by
  intro p q hpq
  simpa only [reflectSecond_involutive] using congrArg reflectSecond hpq

private theorem mem_finiteGraph_iff (f : ℝ → ℝ) (X : Finset ℝ) (p : R2) :
    p ∈ finiteGraph f X ↔
      ∃ x ∈ X, (fun i => if i = 0 then x else f x) = p := by
  classical
  simp [finiteGraph]

theorem map_finiteGraph_neg (f : ℝ → ℝ) (X : Finset ℝ) :
    mapFinset reflectSecond reflectSecond_injective
        (finiteGraph (-f) X) = finiteGraph f X := by
  classical
  ext p
  constructor
  · intro hp
    rw [mem_mapFinset] at hp
    rcases hp with ⟨q, hq, rfl⟩
    rw [mem_finiteGraph_iff] at hq ⊢
    rcases hq with ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    funext i
    fin_cases i <;> simp [reflectSecond]
  · intro hp
    rw [mem_finiteGraph_iff] at hp
    rcases hp with ⟨x, hx, rfl⟩
    rw [mem_mapFinset]
    refine ⟨(fun i => if i = 0 then x else (-f) x), ?_, ?_⟩
    · rw [mem_finiteGraph_iff]
      exact ⟨x, hx, rfl⟩
    · funext i
      fin_cases i <;> simp [reflectSecond]

theorem J3_finiteGraph_neg (f : ℝ → ℝ) (X : Finset ℝ) :
    J3 (finiteGraph (-f) X) = J3 (finiteGraph f X) := by
  rw [← map_finiteGraph_neg f X]
  symm
  exact J3_mapFinset reflectSecond reflectSecond_injective (finiteGraph (-f) X)

/-- CDW for strictly convex functions implies the identical uniform estimate
for strictly concave functions. -/
theorem cushmanDemeterWu_concave
    (hCDW : CushmanDemeterWuStatement) :
    ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : ℝ → ℝ), StrictConcaveOn ℝ Set.univ f →
        ∀ X : Finset ℝ,
          (J3 (finiteGraph f X) : ℝ) ≤
            C * (X.card : ℝ) ^ (3 + eps) := by
  intro eps heps
  obtain ⟨C, hC, hconvex⟩ := hCDW eps heps
  refine ⟨C, hC, ?_⟩
  intro f hf X
  have hneg : StrictConvexOn ℝ Set.univ (-f) := hf.neg
  simpa only [J3_finiteGraph_neg] using hconvex (-f) hneg X

end ComplexitySensitiveEnergy.Turning
