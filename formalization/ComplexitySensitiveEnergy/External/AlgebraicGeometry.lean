import ComplexitySensitiveEnergy.Algebraic.Variety
import ComplexitySensitiveEnergy.External.Literature

/-!
# Algebraic-geometry trust boundary

The paper invokes polynomial partitioning, real component bounds, affine
Bezout/decomposition, and a generic-projection theorem.  Mathlib currently
does not contain the common real/complex dimension-and-degree API needed to
derive these facts.  They are therefore stated here as proposition-valued
interfaces.  Importing the file adds no axiom.

Two distinctions are recorded explicitly.

* Walsh's theorem gives partitioning degree `O_n(D)` in its original
  parameter.  `WalshPartitionStatement` retains the multiplicative degree
  constant; the paper's degree-`D` form is a reparameterized corollary.
* The Barone--Basu input is a component estimate once the algebraic set has
  bounded defining complexity.  Passing from just “degree at most `B`” to
  bounded defining complexity is a separate bounded-degree input.
-/

open scoped Pointwise

namespace ComplexitySensitiveEnergy.External

variable {n : ℕ}

/-- Real zero set of an `n`-variable polynomial. -/
def polynomialZeroSet (P : MvPolynomial (Fin n) ℝ) : Set (RVec n) :=
  {x | MvPolynomial.eval x P = 0}

/-- “Does not vanish identically on the complex variety”, represented on
the Zariski-dense real locus supplied by `PaperVariety`. -/
def DoesNotVanishIdentically (W : PaperVariety n)
    (P : MvPolynomial (Fin n) ℝ) : Prop :=
  ∃ x ∈ W.realPoints, MvPolynomial.eval x P ≠ 0

/-- Maximal connected-subset formulation of a connected component.  For the
semialgebraic sets below, ordinary and semialgebraic connected components
coincide. -/
def IsConnectedComponentOf (C S : Set (RVec n)) : Prop :=
  C.Nonempty ∧ C ⊆ S ∧ IsPreconnected C ∧
    ∀ C' : Set (RVec n), C ⊆ C' → C' ⊆ S →
      IsPreconnected C' → C' = C

/-- A finite, disjoint list of all connected components of `S`. -/
structure FiniteComponentDecomposition (S : Set (RVec n)) where
  cells : Finset (Set (RVec n))
  each_component : ∀ C ∈ cells, IsConnectedComponentOf C S
  pairwise_disjoint : ((↑cells : Set (Set (RVec n)))).PairwiseDisjoint id
  covers : ∀ x, x ∈ S ↔ ∃ C ∈ cells, x ∈ C

/-- Occupancy of an arbitrary displayed subset by a finite point set. -/
noncomputable def setOccupancy (A : Finset (RVec n))
    (C : Set (RVec n)) : ℕ := by
  classical
  exact (A.filter fun x => x ∈ C).card

/-- The concrete certificate delivered by one polynomial partition. -/
structure PolynomialPartitionCertificate (W : PaperVariety n)
    (A : Finset (RVec n)) (D : ℕ) (degreeConstant cellConstant : ℝ) where
  polynomial : MvPolynomial (Fin n) ℝ
  degree_le : (polynomial.totalDegree : WithBot ℕ) ≤
    (((⌈degreeConstant⌉₊ : ℕ) * D : ℕ) : WithBot ℕ)
  nonvanishing : DoesNotVanishIdentically W polynomial
  decomposition : FiniteComponentDecomposition
    (W.realPoints \ polynomialZeroSet polynomial)
  cell_occupancy : ∀ C ∈ decomposition.cells,
    (setOccupancy A C : ℝ) * (D : ℝ) ^ W.complexDim ≤
      cellConstant * (A.card : ℝ)
  number_of_cells : (decomposition.cells.card : ℝ) ≤
    cellConstant * (D : ℝ) ^ W.complexDim

/-- Source-faithful `O_n(D)`-degree form of Walsh's partition theorem,
including the standard bounded-degree component-count consequence. -/
def WalshPartitionStatement : Prop :=
  ∀ (n Delta : ℕ), 1 ≤ n → 1 ≤ Delta →
    ∃ degreeConstant cellConstant : ℝ,
      1 ≤ degreeConstant ∧ 1 ≤ cellConstant ∧
      ∀ (W : PaperVariety n), W.admissibleIrreducible →
        W.degree ≤ Delta → 0 < W.complexDim →
        ∀ (A : Finset (RVec n)) (D : ℕ), 2 ≤ D →
          Nonempty (PolynomialPartitionCertificate W A D
            degreeConstant cellConstant)

/-- Abstract data for a real algebraic set to which the component theorem is
applied.  The intended invariants are complex-algebraic dimension and total
degree, not topological dimension. -/
structure BoundedAlgebraicSet (n : ℕ) where
  carrier : Set (RVec n)
  complexDimension : ℕ
  degree : ℕ
  boundedDefiningComplexity : Prop

/-- The two-polynomial complement form of the Barone--Basu sign-condition
estimate used in the proof.  Its constant is uniform after ambient dimension
and the defining-complexity/degree bound are fixed. -/
def BaroneBasuComponentStatement : Prop :=
  ∀ (n B : ℕ), 1 ≤ n → 1 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Z : BoundedAlgebraicSet n), Z.degree ≤ B →
      Z.boundedDefiningComplexity → ∀ (s D : ℕ),
        Z.complexDimension ≤ s →
        ∀ P₁ P₂ : MvPolynomial (Fin n) ℝ,
          P₁.totalDegree ≤ (D : WithBot ℕ) →
          P₂.totalDegree ≤ (D : WithBot ℕ) →
          ∃ decomp : FiniteComponentDecomposition
              (Z.carrier \ (polynomialZeroSet P₁ ∪ polynomialZeroSet P₂)),
            (decomp.cells.card : ℝ) ≤ C * (D + 1 : ℝ) ^ s

/-- Finite irreducible decomposition certificate for a partition wall.  The
`residual` contains all zero-dimensional components. -/
structure WallDecompositionCertificate (W : PaperVariety n)
    (P : MvPolynomial (Fin n) ℝ) (R componentBound pointBound : ℕ) where
  number : ℕ
  number_le : number ≤ componentBound
  component : Fin number → PaperVariety n
  positive_dimensional : ∀ j, (component j).IsPositiveDimensionalSubvariety W
  dimension_drops : ∀ j, (component j).complexDim < W.complexDim
  degree_le : ∀ j, (component j).degree ≤ R
  residual : Finset (RVec n)
  residual_card : residual.card ≤ pointBound
  covers_wall : ∀ x ∈ W.realPoints, x ∈ polynomialZeroSet P →
    x ∈ residual ∨ ∃ j, x ∈ (component j).realPoints

/-- Affine Bezout plus irreducible decomposition in exactly the uniform form
needed for the finite degree tower. -/
def BezoutWallDecompositionStatement : Prop :=
  ∀ (n Delta D : ℕ), 1 ≤ n → 1 ≤ Delta → 1 ≤ D →
    ∃ R componentBound pointBound : ℕ,
      ∀ (W : PaperVariety n), W.admissibleIrreducible →
        W.degree ≤ Delta → 0 < W.complexDim →
        ∀ P : MvPolynomial (Fin n) ℝ,
          P.totalDegree ≤ (D : WithBot ℕ) →
          DoesNotVanishIdentically W P →
          Nonempty (WallDecompositionCertificate W P R
            componentBound pointBound)

/-- The finite-set property needed of a generic linear projection: it is a
Freiman isomorphism of order two on the selected set. -/
def IsFreimanTwoOn {m : ℕ}
    (L : LinearMap (RingHom.id ℝ) (RVec n) (RVec m))
    (A : Finset (RVec n)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    L a + L b = L c + L d ↔ a + b = c + d

/-- A genuine affine line in real `n`-space. -/
structure AffineLineN (n : ℕ) where
  base : RVec n
  direction : RVec n
  direction_ne_zero : direction ≠ 0

namespace AffineLineN

def carrier (ell : AffineLineN n) : Set (RVec n) :=
  {x | ∃ s : ℝ, x = ell.base + s • ell.direction}

end AffineLineN

/-- The source surface in Lemma 4.3 contains no affine line. -/
def ContainsNoAffineLine (S : PaperVariety n) : Prop :=
  ∀ ell : AffineLineN n, ¬ ell.carrier ⊆ S.realPoints

/-- Affine collinearity of a labelled triple, expressed by a nontrivial
affine dependence. -/
def AffinelyCollinear {m : ℕ} (x y z : RVec m) : Prop :=
  ∃ a b c : ℝ,
    (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧ a + b + c = 0 ∧
      a • x + b • y + c • z = 0

/-- The finite generic projection also preserves noncollinearity of every
triple selected from `A`. -/
def PreservesNoncollinearTriples {m : ℕ}
    (L : LinearMap (RingHom.id ℝ) (RVec n) (RVec m))
    (A : Finset (RVec n)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
    ¬ AffinelyCollinear x y z →
      ¬ AffinelyCollinear (L x) (L y) (L z)

/-- A complex-linear map genuinely extends the displayed real-linear map. -/
def IsComplexLinearExtension {m : ℕ}
    (L : LinearMap (RingHom.id ℝ) (RVec n) (RVec m))
    (LC : LinearMap (RingHom.id ℂ) (CVec n) (CVec m)) : Prop :=
  ∀ x : RVec n, LC (complexifyPoint x) = complexifyPoint (L x)

/-- Semantic minimality formulation of
`T = ZarClosure(LC(S))`.  It uses the complex carriers and quantifies over
all admissible irreducible complex-algebraic carriers in the target. -/
def IsZariskiImageClosure {m : ℕ}
    (S : PaperVariety n)
    (LC : LinearMap (RingHom.id ℂ) (CVec n) (CVec m))
    (T : PaperVariety m) : Prop :=
  (∀ z ∈ S.complexPoints, LC z ∈ T.complexPoints) ∧
    ∀ U : PaperVariety m, U.admissibleIrreducible →
      (∀ z ∈ S.complexPoints, LC z ∈ U.complexPoints) →
        T.complexPoints ⊆ U.complexPoints

/-- Image of a finite real set under the projection. -/
noncomputable def linearImageFinset {m : ℕ}
    (L : LinearMap (RingHom.id ℝ) (RVec n) (RVec m))
    (A : Finset (RVec n)) : Finset (RVec m) := by
  classical
  exact A.image L

/-- Source-faithful `ℝ⁵` specialization of the finite Freiman projection in
Lemma 4.3.
Besides Freiman order two, it records preservation of noncollinear triples,
the actual complex Zariski image closure, nonplanarity/degree control, and the
line-occupancy bound needed by Jing--Wu.  It is deliberately separate from
Walsh/Barone--Basu: the manuscript cites no specific source for this generic
projection black box. -/
def GenericSurfaceProjectionStatement : Prop :=
  ∀ (B : ℕ), 1 ≤ B → ∃ projectedDegree : ℕ,
    ∀ (S : PaperVariety 5), S.admissibleIrreducible →
      S.complexDim = 2 → S.degree ≤ B → ContainsNoAffineLine S →
      ∀ A : Finset (RVec 5), ↑A ⊆ S.realPoints →
        ∃ (L : LinearMap (RingHom.id ℝ) (RVec 5) (RVec 3))
          (LC : LinearMap (RingHom.id ℂ) (CVec 5) (CVec 3))
          (T : PaperVariety 3) (F : MvPolynomial (Fin 3) ℝ),
          IsComplexLinearExtension L LC ∧
          IsFreimanTwoOn L A ∧ PreservesNoncollinearTriples L A ∧
          IsZariskiImageClosure S LC T ∧ T.admissibleIrreducible ∧
          T.complexDim = 2 ∧ 2 ≤ T.degree ∧
          T.degree ≤ projectedDegree ∧ Irreducible F ∧
          F.totalDegree = (T.degree : WithBot ℕ) ∧
          T.realPoints = polynomialZeroSet F ∧
          (∀ x ∈ A, L x ∈ T.realPoints) ∧
          LineOccupancyBound F (linearImageFinset L A) B

/-- All algebraic-geometry inputs, packaged rather than asserted. -/
structure AlgebraicGeometryInputs : Prop where
  walsh : WalshPartitionStatement
  baroneBasu : BaroneBasuComponentStatement
  bezoutWalls : BezoutWallDecompositionStatement
  genericSurfaceProjection : GenericSurfaceProjectionStatement

end ComplexitySensitiveEnergy.External
