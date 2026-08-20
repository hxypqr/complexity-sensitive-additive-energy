import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Prod

set_option linter.style.header false

/-!
# Basic finite-set infrastructure

This file contains the common map operation used to transport finite subsets
along injective additive homomorphisms.  The injectivity hypothesis is kept
explicit because all energy invariance statements depend on it.
-/

namespace ComplexitySensitiveEnergy

variable {G H : Type*}

/-- The underlying embedding of an injective additive homomorphism. -/
def additiveEmbedding [AddMonoid G] [AddMonoid H] (f : G →+ H)
    (hf : Function.Injective f) : G ↪ H :=
  ⟨f, hf⟩

/-- Image of a finite set under an injective additive homomorphism. -/
def mapFinset [AddMonoid G] [AddMonoid H] (f : G →+ H)
    (hf : Function.Injective f) (A : Finset G) : Finset H :=
  A.map (additiveEmbedding f hf)

@[simp]
theorem card_mapFinset [AddMonoid G] [AddMonoid H] (f : G →+ H)
    (hf : Function.Injective f) (A : Finset G) :
    (mapFinset f hf A).card = A.card := by
  simp [mapFinset]

@[simp]
theorem mem_mapFinset_image [AddMonoid G] [AddMonoid H] (f : G →+ H)
    (hf : Function.Injective f) (A : Finset G) (x : G) :
    f x ∈ mapFinset f hf A ↔ x ∈ A := by
  simp [mapFinset, additiveEmbedding]

theorem mem_mapFinset [AddMonoid G] [AddMonoid H] (f : G →+ H)
    (hf : Function.Injective f) (A : Finset G) (y : H) :
    y ∈ mapFinset f hf A ↔ ∃ x ∈ A, f x = y := by
  simp [mapFinset, additiveEmbedding]

end ComplexitySensitiveEnergy
