import ComplexitySensitiveEnergy.Algebraic.Variety

/-!
# The local concentration parameter used inside a node

The paper's proof of Theorem 1.1 needs a concentration parameter which is
both bounded by the global flag parameter and, at a nonempty node of size
`M`, bounded by `M`.  The latter statement is false for the *global* flag
parameter.  We therefore keep the finite, node-local quantity below until
after applying the interpolation inequality.
-/

open scoped Pointwise

namespace ComplexitySensitiveEnergy.PaperVariety

variable {n : ℕ}

/-- Maximum stabilizer-coset occupancy among cosets which meet `A`. -/
noncomputable def finiteStabilizerOccupancy
    (W : PaperVariety n) (A : Finset (RVec n)) : ℕ := by
  classical
  exact A.sup (W.stabilizerCosetOccupancy A)

/-- Maximum exceptional-fiber occupancy among translations which actually
occur as a difference of two points of `A`.  Other exceptional translations
never enter the exceptional-energy sum. -/
noncomputable def finiteBadFiberOccupancy
    (W : PaperVariety n) (A : Finset (RVec n)) : ℕ := by
  classical
  exact (A - A).sup fun t =>
    if t ∈ W.badTranslations then W.translateFiberOccupancy A t else 0

/-- Energy-relevant local parameter. -/
noncomputable def energyLocalLambda
    (W : PaperVariety n) (A : Finset (RVec n)) : ℕ :=
  max 1 (max (W.finiteStabilizerOccupancy A) (W.finiteBadFiberOccupancy A))

theorem one_le_energyLocalLambda (W : PaperVariety n)
    (A : Finset (RVec n)) :
    1 ≤ W.energyLocalLambda A := by
  simp [energyLocalLambda]

theorem stabilizerCosetOccupancy_le_card
    (W : PaperVariety n) (A : Finset (RVec n)) (z : RVec n) :
    W.stabilizerCosetOccupancy A z ≤ A.card := by
  classical
  exact Finset.card_filter_le _ _

theorem translateFiberOccupancy_le_card
    (W : PaperVariety n) (A : Finset (RVec n)) (t : RVec n) :
    W.translateFiberOccupancy A t ≤ A.card := by
  classical
  exact Finset.card_filter_le _ _

theorem stabilizerCosetOccupancy_mono
    (W : PaperVariety n) {A B : Finset (RVec n)}
    (hAB : A ⊆ B) (z : RVec n) :
    W.stabilizerCosetOccupancy A z ≤
      W.stabilizerCosetOccupancy B z := by
  classical
  unfold stabilizerCosetOccupancy
  apply Finset.card_le_card
  intro x hx
  exact Finset.mem_filter.mpr
    ⟨hAB (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

theorem translateFiberOccupancy_mono
    (W : PaperVariety n) {A B : Finset (RVec n)}
    (hAB : A ⊆ B) (t : RVec n) :
    W.translateFiberOccupancy A t ≤
      W.translateFiberOccupancy B t := by
  classical
  unfold translateFiberOccupancy
  apply Finset.card_le_card
  intro x hx
  exact Finset.mem_filter.mpr
    ⟨hAB (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

theorem finiteStabilizerOccupancy_le_card
    (W : PaperVariety n) (A : Finset (RVec n)) :
    W.finiteStabilizerOccupancy A ≤ A.card := by
  classical
  apply Finset.sup_le
  intro z hz
  exact W.stabilizerCosetOccupancy_le_card A z

theorem finiteBadFiberOccupancy_le_card
    (W : PaperVariety n) (A : Finset (RVec n)) :
    W.finiteBadFiberOccupancy A ≤ A.card := by
  classical
  apply Finset.sup_le
  intro t ht
  split_ifs
  · exact W.translateFiberOccupancy_le_card A t
  · exact Nat.zero_le _

/-- The node-local parameter is genuinely hereditary.  This is proved from
the finite suprema; no monotonicity of a global flag parameter is smuggled
into the local interpolation step. -/
theorem energyLocalLambda_mono
    (W : PaperVariety n) {A B : Finset (RVec n)} (hAB : A ⊆ B) :
    W.energyLocalLambda A ≤ W.energyLocalLambda B := by
  classical
  rw [energyLocalLambda, energyLocalLambda]
  apply max_le_max_left
  apply max_le_max
  · apply Finset.sup_le
    intro z hzA
    calc
      W.stabilizerCosetOccupancy A z ≤
          W.stabilizerCosetOccupancy B z :=
        W.stabilizerCosetOccupancy_mono hAB z
      _ ≤ W.finiteStabilizerOccupancy B :=
        Finset.le_sup (hAB hzA)
  · apply Finset.sup_le
    intro t htA
    have htB : t ∈ B - B := by
      rw [Finset.mem_sub] at htA ⊢
      rcases htA with ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, hAB ha, b, hAB hb, rfl⟩
    split_ifs with htbad
    · calc
        W.translateFiberOccupancy A t ≤
            W.translateFiberOccupancy B t :=
          W.translateFiberOccupancy_mono hAB t
        _ = (if t ∈ W.badTranslations then
              W.translateFiberOccupancy B t else 0) := by simp [htbad]
        _ ≤ W.finiteBadFiberOccupancy B := by
          unfold finiteBadFiberOccupancy
          exact Finset.le_sup
            (f := fun u => if u ∈ W.badTranslations then
              W.translateFiberOccupancy B u else 0) htB
    · exact Nat.zero_le _

/-- The crucial local fact omitted when the paper prematurely replaced the
node parameter by the global flag parameter. -/
theorem energyLocalLambda_le_card
    (W : PaperVariety n) {A : Finset (RVec n)} (hA : A.Nonempty) :
    W.energyLocalLambda A ≤ A.card := by
  rw [energyLocalLambda, max_le_iff, max_le_iff]
  exact ⟨hA.card_pos, W.finiteStabilizerOccupancy_le_card A,
    W.finiteBadFiberOccupancy_le_card A⟩

/-- Any upper bound for the paper's full local parameter also bounds the
finite parameter relevant to the energy sum. -/
theorem energyLocalLambda_le_of_localConcentrationBound
    (W : PaperVariety n) (A : Finset (RVec n)) {L : ℕ}
    (hL : W.LocalConcentrationBound A L) :
    W.energyLocalLambda A ≤ L := by
  classical
  rcases hL with ⟨hone, hcoset, hbad⟩
  rw [energyLocalLambda, max_le_iff, max_le_iff]
  refine ⟨hone, ?_, ?_⟩
  · apply Finset.sup_le
    intro z hz
    exact hcoset z
  · apply Finset.sup_le
    intro t ht
    split_ifs with htb
    · exact hbad t htb
    · exact Nat.zero_le _

theorem localConcentrationBound_mono
    (W : PaperVariety n) {A B : Finset (RVec n)} {L : ℕ}
    (hAB : A ⊆ B) (hB : W.LocalConcentrationBound B L) :
    W.LocalConcentrationBound A L := by
  rcases hB with ⟨hone, hcoset, hbad⟩
  exact ⟨hone,
    fun z => (W.stabilizerCosetOccupancy_mono hAB z).trans (hcoset z),
    fun t ht => (W.translateFiberOccupancy_mono hAB t).trans (hbad t ht)⟩

/-- Monotonicity (3.2) of the upper-bound formulation of the flag parameter. -/
theorem flagBound_mono
    (V : PaperVariety n) {X X' : Finset (RVec n)} {a : ℝ} {R Lambda : ℕ}
    (hXX : X' ⊆ X) (hflag : V.FlagBound a R X Lambda) :
    V.FlagBound a R X' Lambda := by
  classical
  refine ⟨hflag.1, ?_⟩
  intro W hWV hdegree
  have hrestrict : W.restrict X' ⊆ W.restrict X := by
    intro x hx
    rw [mem_restrict] at hx ⊢
    exact ⟨hXX hx.1, hx.2⟩
  have hnode := hflag.2 W hWV hdegree
  by_cases halpha : W.alpha ≤ a
  · simp only [if_pos halpha] at hnode ⊢
    exact W.localConcentrationBound_mono hrestrict hnode
  · simp only [if_neg halpha] at hnode ⊢
    exact (Finset.card_le_card hrestrict).trans hnode

end ComplexitySensitiveEnergy.PaperVariety
