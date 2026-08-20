import ComplexitySensitiveEnergy.Additive.HigherEnergy
import Mathlib

/-!
# Finite combinatorics for the turning-complexity sharpness example

This file contains only the internal counting part of the sharpness example.
It proves that third additive energy is multiplicative on Cartesian products
and gives explicit constant-factor bounds for an integer interval.
-/

namespace ComplexitySensitiveEnergy
namespace Turning

open scoped BigOperators

section Product

variable {G H : Type*}

/-- Split a labelled triple of pairs into the labelled triples of its two
coordinates. -/
def splitAdditiveTripleEquiv :
    AdditiveTriple (G × H) ≃ AdditiveTriple G × AdditiveTriple H where
  toFun x :=
    (((x.1.1.1, x.1.2.1), x.2.1),
      ((x.1.1.2, x.1.2.2), x.2.2))
  invFun x :=
    (((x.1.1.1, x.2.1.1), (x.1.1.2, x.2.1.2)),
      (x.1.2, x.2.2))
  left_inv x := by
    rcases x with ⟨⟨⟨g1, h1⟩, ⟨g2, h2⟩⟩, ⟨g3, h3⟩⟩
    rfl
  right_inv x := by
    rcases x with ⟨⟨⟨g1, g2⟩, g3⟩, ⟨⟨h1, h2⟩, h3⟩⟩
    rfl

/-- Split both triples and regroup the two coordinate witnesses. -/
def splitJ3WitnessEquiv :
    (AdditiveTriple (G × H) × AdditiveTriple (G × H)) ≃
      (AdditiveTriple G × AdditiveTriple G) ×
        (AdditiveTriple H × AdditiveTriple H) :=
  ((splitAdditiveTripleEquiv (G := G) (H := H)).prodCongr
      (splitAdditiveTripleEquiv (G := G) (H := H))).trans
    (Equiv.prodProdProdComm _ _ _ _)

/-- Third additive energy factors exactly across Cartesian products. -/
theorem J3_product [Add G] [Add H] [DecidableEq G] [DecidableEq H]
    (A : Finset G) (B : Finset H) :
    J3 (A ×ˢ B) = J3 A * J3 B := by
  unfold J3
  rw [← Finset.card_product]
  apply Finset.card_equiv (splitJ3WitnessEquiv (G := G) (H := H))
  rintro ⟨⟨⟨⟨g1, h1⟩, ⟨g2, h2⟩⟩, ⟨g3, h3⟩⟩,
    ⟨⟨⟨g4, h4⟩, ⟨g5, h5⟩⟩, ⟨g6, h6⟩⟩⟩
  simp [j3Witnesses, tripleProduct, tripleSum, splitJ3WitnessEquiv,
    splitAdditiveTripleEquiv, and_assoc, and_left_comm, and_comm]

end Product

section CancelativeUpperBound

variable {G : Type*} [AddLeftCancelSemigroup G] [DecidableEq G]

/-- The universal `|A|⁵` upper bound needs only left cancellation, not additive
inverses.  This permits direct application to natural-number intervals. -/
theorem J3_le_card_fifth_of_leftCancel (A : Finset G) :
    J3 A ≤ A.card ^ 5 := by
  unfold J3
  calc
    (j3Witnesses A).card ≤
        ((tripleProduct A) ×ˢ (A ×ˢ A)).card := by
      apply Finset.card_le_card_of_injOn (fun q ↦ (q.1, q.2.1))
      · intro q hq
        have hmem := (Finset.mem_filter.mp hq).1
        exact Finset.mem_product.mpr
          ⟨(Finset.mem_product.mp hmem).1,
            (Finset.mem_product.mp
              (Finset.mem_product.mp hmem).2).1⟩
      · intro q1 hq1 q2 hq2 h
        have hsum1 := (Finset.mem_filter.mp hq1).2
        have hsum2 := (Finset.mem_filter.mp hq2).2
        have hleft : q1.1 = q2.1 :=
          congrArg (fun z : AdditiveTriple G × (G × G) ↦ z.1) h
        have hrightPair : q1.2.1 = q2.2.1 :=
          congrArg (fun z : AdditiveTriple G × (G × G) ↦ z.2) h
        have hlast : q1.2.2 = q2.2.2 := by
          apply add_left_cancel (a := q1.2.1.1 + q1.2.1.2)
          calc
            q1.2.1.1 + q1.2.1.2 + q1.2.2 = tripleSum q1.2 := rfl
            _ = tripleSum q1.1 := hsum1.symm
            _ = tripleSum q2.1 := by rw [hleft]
            _ = tripleSum q2.2 := hsum2
            _ = q2.2.1.1 + q2.2.1.2 + q2.2.2 := rfl
            _ = q1.2.1.1 + q1.2.1.2 + q2.2.2 := by rw [hrightPair]
        exact Prod.ext hleft (Prod.ext hrightPair hlast)
    _ = A.card ^ 5 := by
      rw [Finset.card_product, card_tripleProduct,
        Finset.card_product]
      simp [pow_succ]
      ac_rfl

end CancelativeUpperBound

section Interval

/-- Five freely chosen parameters for the interval lower-bound family. -/
abbrev FiveTuple (G : Type*) := (G × G) × ((G × G) × G)

/-- The Cartesian fifth power of a finite set, with a convenient bracketing. -/
def fiveProduct {G : Type*} (A : Finset G) : Finset (FiveTuple G) :=
  (A ×ˢ A) ×ˢ ((A ×ˢ A) ×ˢ A)

@[simp]
theorem card_fiveProduct {G : Type*} (A : Finset G) :
    (fiveProduct A).card = A.card ^ 5 := by
  simp [fiveProduct, pow_succ]
  ring

/-- From parameters `(u,v,w,x,y)`, form the identity

`(u+x) + (v+y) + w = u + v + (w+x+y)`.
-/
def intervalWitness (p : FiveTuple ℕ) :
    AdditiveTriple ℕ × AdditiveTriple ℕ :=
  (((p.1.1 + p.2.1.2, p.1.2 + p.2.2), p.2.1.1),
    ((p.1.1, p.1.2), p.2.1.1 + p.2.1.2 + p.2.2))

theorem intervalWitness_injective : Function.Injective intervalWitness := by
  rintro ⟨⟨u, v⟩, ⟨⟨w, x⟩, y⟩⟩
    ⟨⟨u', v'⟩, ⟨⟨w', x'⟩, y'⟩⟩ h
  have hu : u = u' := congrArg (fun q ↦ q.2.1.1) h
  have hv : v = v' := congrArg (fun q ↦ q.2.1.2) h
  have hw : w = w' := congrArg (fun q ↦ q.1.2) h
  have hux : u + x = u' + x' := congrArg (fun q ↦ q.1.1.1) h
  have hvy : v + y = v' + y' := congrArg (fun q ↦ q.1.1.2) h
  subst u'
  subst v'
  subst w'
  have hx : x = x' := Nat.add_left_cancel hux
  have hy : y = y' := Nat.add_left_cancel hvy
  subst x'
  subst y'
  rfl

/-- If `3m ≤ K`, the five-parameter family injects into the `J3` witnesses of
the interval `0, …, K-1`. -/
theorem pow_five_le_J3_range_of_three_mul_le (m K : ℕ) (hmK : 3 * m ≤ K) :
    m ^ 5 ≤ J3 (Finset.range K) := by
  rw [← Finset.card_range m, ← card_fiveProduct]
  unfold J3
  apply Finset.card_le_card_of_injOn intervalWitness
  · rintro ⟨⟨u, v⟩, ⟨⟨w, x⟩, y⟩⟩ hp
    rw [fiveProduct] at hp
    rcases Finset.mem_product.mp hp with ⟨huv, hwxy⟩
    rcases Finset.mem_product.mp huv with ⟨hu, hv⟩
    rcases Finset.mem_product.mp hwxy with ⟨hwx, hy⟩
    rcases Finset.mem_product.mp hwx with ⟨hw, hx⟩
    simp only [Finset.mem_range] at hu hv hw hx hy
    have hux : u + x < K := by omega
    have hvy : v + y < K := by omega
    have huK : u < K := by omega
    have hvK : v < K := by omega
    have hwK : w < K := by omega
    have hwxy : w + x + y < K := by omega
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr
            ⟨Finset.mem_range.mpr hux, Finset.mem_range.mpr hvy⟩,
            Finset.mem_range.mpr hwK⟩,
          Finset.mem_product.mpr
            ⟨Finset.mem_product.mpr
              ⟨Finset.mem_range.mpr huK, Finset.mem_range.mpr hvK⟩,
              Finset.mem_range.mpr hwxy⟩⟩
    · simp [intervalWitness, tripleSum]
      omega
  · intro p _ q _ hpq
    exact intervalWitness_injective hpq

/-- Explicit interval bounds: the lower bound already has the correct fifth
power scale, and the upper bound is sharp with constant one. -/
theorem J3_range_between (K : ℕ) :
    (K / 3) ^ 5 ≤ J3 (Finset.range K) ∧
      J3 (Finset.range K) ≤ K ^ 5 := by
  constructor
  · apply pow_five_le_J3_range_of_three_mul_le
    omega
  · simpa only [Finset.card_range] using
      (J3_le_card_fifth_of_leftCancel (Finset.range K))

/-- A conventional constant-factor formulation valid for every `K`, including
the two intervals too short for the five-parameter family with `m = K/3`. -/
theorem J3_range_explicit_comparison (K : ℕ) :
    K ^ 5 ≤ 3125 * J3 (Finset.range K) ∧
      J3 (Finset.range K) ≤ K ^ 5 := by
  constructor
  · by_cases hK : 3 ≤ K
    · have hlower : (K / 3) ^ 5 ≤ J3 (Finset.range K) :=
        (J3_range_between K).1
      have hscale : K ≤ 5 * (K / 3) := by omega
      calc
        K ^ 5 ≤ (5 * (K / 3)) ^ 5 := Nat.pow_le_pow_left hscale 5
        _ = 3125 * (K / 3) ^ 5 := by norm_num [mul_pow]
        _ ≤ 3125 * J3 (Finset.range K) :=
          Nat.mul_le_mul_left 3125 hlower
    · have hdiag : K ^ 3 ≤ J3 (Finset.range K) := by
        have hcard : (Finset.range K).card ^ 3 = K ^ 3 := by simp
        rw [← hcard]
        unfold J3
        rw [← card_tripleProduct]
        apply Finset.card_le_card_of_injOn (fun x ↦ (x, x))
        · intro x hx
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hx, hx⟩, rfl⟩
        · intro x _ y _ hxy
          exact congrArg Prod.fst hxy
      have hcases : K = 0 ∨ K = 1 ∨ K = 2 := by omega
      rcases hcases with rfl | rfl | rfl <;> norm_num at hdiag ⊢ <;> omega
  · exact (J3_range_between K).2

end Interval

section ThreePowers

/-- The base-`B` digit contributed at position `i` by three exponents. -/
def triplePowerDigit (a b c i : ℕ) : ℕ :=
  (if a = i then 1 else 0) + (if b = i then 1 else 0) +
    (if c = i then 1 else 0)

/-- A fixed-length base-`B` digit vector for a three-power sum. -/
def triplePowerDigits (n a b c : ℕ) : List ℕ :=
  List.ofFn fun i : Fin n ↦ triplePowerDigit a b c i

theorem triplePowerDigit_lt_four (a b c i : ℕ) :
    triplePowerDigit a b c i < 4 := by
  unfold triplePowerDigit
  split_ifs <;> omega

theorem triplePowerDigit_eq_count (a b c i : ℕ) :
    triplePowerDigit a b c i = [a, b, c].count i := by
  simp [triplePowerDigit, List.count_cons, beq_iff_eq]
  omega

private theorem sum_fin_indicator_pow {B n a : ℕ} (ha : a < n) :
    (∑ i : Fin n, if a = (i : ℕ) then B ^ (i : ℕ) else 0) = B ^ a := by
  classical
  let ia : Fin n := ⟨a, ha⟩
  have hindex (i : Fin n) : (a = (i : ℕ)) ↔ i = ia := by
    constructor
    · intro h
      apply Fin.ext
      simpa [ia] using h.symm
    · intro h
      have hval := congrArg Fin.val h
      simpa [ia] using hval.symm
  simp_rw [hindex]
  simp [ia]

/-- The digit vector evaluates to the intended sum of three powers. -/
theorem ofDigits_triplePowerDigits {B n a b c : ℕ}
    (ha : a < n) (hb : b < n) (hc : c < n) :
    Nat.ofDigits B (triplePowerDigits n a b c) =
      B ^ a + B ^ b + B ^ c := by
  simp only [triplePowerDigits, Nat.ofDigits_eq_sum_mapIdx,
    List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn, Fin.val_cast,
    List.sum_ofFn, triplePowerDigit]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [ite_mul, one_mul, zero_mul]
  rw [sum_fin_indicator_pow ha, sum_fin_indicator_pow hb,
    sum_fin_indicator_pow hc]

/-- For base at least four, equality of two three-power sums is exactly
equality of the exponent multisets.  The proof is the no-carry base-`B`
argument made explicit through fixed-length digit vectors. -/
theorem three_powers_sum_eq_iff_perm
    {B n a b c d e f : ℕ} (hB : 4 ≤ B)
    (ha : a < n) (hb : b < n) (hc : c < n)
    (hd : d < n) (he : e < n) (hf : f < n) :
    B ^ a + B ^ b + B ^ c = B ^ d + B ^ e + B ^ f ↔
      [a, b, c].Perm [d, e, f] := by
  constructor
  · intro hsum
    have hdigits :
        triplePowerDigits n a b c = triplePowerDigits n d e f := by
      apply Nat.ofDigits_inj_of_len_eq
        (lt_of_lt_of_le (by norm_num : 1 < 4) hB)
      · simp [triplePowerDigits]
      · intro x hx
        rw [triplePowerDigits, List.mem_ofFn] at hx
        rcases hx with ⟨i, rfl⟩
        exact (triplePowerDigit_lt_four a b c i).trans_le hB
      · intro x hx
        rw [triplePowerDigits, List.mem_ofFn] at hx
        rcases hx with ⟨i, rfl⟩
        exact (triplePowerDigit_lt_four d e f i).trans_le hB
      · rw [ofDigits_triplePowerDigits ha hb hc,
          ofDigits_triplePowerDigits hd he hf]
        exact hsum
    have hfun :
        (fun i : Fin n ↦ triplePowerDigit a b c i) =
          (fun i : Fin n ↦ triplePowerDigit d e f i) := by
      exact List.ofFn_inj.mp hdigits
    apply List.perm_iff_count.mpr
    intro x
    by_cases hx : x < n
    · have hdigit := congrFun hfun (⟨x, hx⟩ : Fin n)
      rw [← triplePowerDigit_eq_count, ← triplePowerDigit_eq_count]
      exact hdigit
    · have hxa : x ≠ a := by omega
      have hxb : x ≠ b := by omega
      have hxc : x ≠ c := by omega
      have hxd : x ≠ d := by omega
      have hxe : x ≠ e := by omega
      have hxf : x ≠ f := by omega
      have hax : a ≠ x := by omega
      have hbx : b ≠ x := by omega
      have hcx : c ≠ x := by omega
      have hdx : d ≠ x := by omega
      have hex : e ≠ x := by omega
      have hfx : f ≠ x := by omega
      rw [← triplePowerDigit_eq_count, ← triplePowerDigit_eq_count]
      simp [triplePowerDigit, hax, hbx, hcx, hdx, hex, hfx]
  · intro hperm
    have hmap := hperm.map (fun i ↦ B ^ i)
    have hsum :
        List.foldl (fun x y : ℕ ↦ x + y) 0
            ([a, b, c].map fun i ↦ B ^ i) =
          List.foldl (fun x y : ℕ ↦ x + y) 0
            ([d, e, f].map fun i ↦ B ^ i) :=
      hmap.foldl_eq 0
    simpa [List.sum_eq_foldl] using hsum

/-- Read a three-element list as a labelled additive triple.  The fallback is
irrelevant on the length-three lists used below. -/
def listToTriple {G : Type*} (fallback : AdditiveTriple G) :
    List G → AdditiveTriple G
  | [x, y, z] => ((x, y), z)
  | _ => fallback

/-- The at most six labelled reorderings of a triple.  Defining this through
`List.permutations` keeps multiplicities harmless when entries coincide. -/
def triplePermutations {G : Type*} [DecidableEq G]
    (x : AdditiveTriple G) : Finset (AdditiveTriple G) :=
  (List.permutations [x.1.1, x.1.2, x.2]).toFinset.image
    (listToTriple x)

theorem mem_triplePermutations_of_perm {G : Type*} [DecidableEq G]
    {x y : AdditiveTriple G}
    (hperm : [y.1.1, y.1.2, y.2].Perm [x.1.1, x.1.2, x.2]) :
    y ∈ triplePermutations x := by
  apply Finset.mem_image.mpr
  refine ⟨[y.1.1, y.1.2, y.2], ?_, rfl⟩
  simpa only [List.mem_toFinset, List.mem_permutations] using hperm

theorem card_triplePermutations_le_six {G : Type*} [DecidableEq G]
    (x : AdditiveTriple G) :
    (triplePermutations x).card ≤ 6 := by
  calc
    (triplePermutations x).card ≤
        (List.permutations [x.1.1, x.1.2, x.2]).toFinset.card := by
      exact Finset.card_image_le
    _ ≤ (List.permutations [x.1.1, x.1.2, x.2]).length :=
      List.toFinset_card_le _
    _ = 6 := by norm_num [List.length_permutations, Nat.factorial]

/-- A general six-reorderings bound.  It isolates the only counting step
needed after a structured set proves that equal triple sums force equality of
the entry multisets. -/
theorem J3_le_six_card_cubed_of_perm {G : Type*} [Add G] [DecidableEq G]
    (A : Finset G)
    (hperm : ∀ x ∈ tripleProduct A, ∀ y ∈ tripleProduct A,
      tripleSum x = tripleSum y →
        [y.1.1, y.1.2, y.2].Perm [x.1.1, x.1.2, x.2]) :
    J3 A ≤ 6 * A.card ^ 3 := by
  unfold J3
  let cover : Finset (AdditiveTriple G × AdditiveTriple G) :=
    (tripleProduct A).biUnion fun x =>
      ({x} : Finset (AdditiveTriple G)) ×ˢ triplePermutations x
  calc
    (j3Witnesses A).card ≤ cover.card := by
      apply Finset.card_le_card
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqmem, hqsum⟩
      rcases Finset.mem_product.mp hqmem with ⟨hx, hy⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨q.1, hx, Finset.mem_product.mpr ⟨by simp, ?_⟩⟩
      exact mem_triplePermutations_of_perm
        (hperm q.1 hx q.2 hy hqsum)
    _ ≤ (tripleProduct A).card * 6 := by
      apply Finset.card_biUnion_le_card_mul
      intro x _
      simpa only [Finset.card_product, Finset.card_singleton, one_mul] using
        card_triplePermutations_le_six x
    _ = 6 * A.card ^ 3 := by
      rw [card_tripleProduct]
      omega

/-- The diagonal triples give the matching lower bound under no cancellation
or inverse assumptions. -/
theorem card_cubed_le_J3_of_add {G : Type*} [Add G] [DecidableEq G]
    (A : Finset G) :
    A.card ^ 3 ≤ J3 A := by
  rw [← card_tripleProduct]
  unfold J3
  apply Finset.card_le_card_of_injOn (fun x => (x, x))
  · intro x hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hx, hx⟩, rfl⟩
  · intro x _ y _ hxy
    exact congrArg Prod.fst hxy

/-- The injective parametrization `i ↦ (i, B^i)`. -/
def powerCurveEmbedding (B : ℕ) : ℕ ↪ ℕ × ℕ where
  toFun i := (i, B ^ i)
  inj' := by
    intro i j h
    exact congrArg Prod.fst h

/-- The first `n` points of the discrete power curve. -/
def powerCurve (B n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n).map (powerCurveEmbedding B)

@[simp]
theorem card_powerCurve (B n : ℕ) :
    (powerCurve B n).card = n := by
  simp [powerCurve]

theorem mem_powerCurve_iff {B n : ℕ} {p : ℕ × ℕ} :
    p ∈ powerCurve B n ↔ ∃ i < n, p = (i, B ^ i) := by
  constructor
  · intro hp
    rcases Finset.mem_map.mp hp with ⟨i, hi, rfl⟩
    exact ⟨i, Finset.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact Finset.mem_map.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

/-- For `B ≥ 4`, the power-curve factor has third energy between `n³` and
`6n³`.  This is the precise finite version of `J₃(B_n) ≍ n³`. -/
theorem J3_powerCurve_between {B n : ℕ} (hB : 4 ≤ B) :
    n ^ 3 ≤ J3 (powerCurve B n) ∧
      J3 (powerCurve B n) ≤ 6 * n ^ 3 := by
  constructor
  · simpa only [card_powerCurve] using
      card_cubed_le_J3_of_add (powerCurve B n)
  · simpa only [card_powerCurve] using
      J3_le_six_card_cubed_of_perm (powerCurve B n) (by
        rintro ⟨⟨x₁, x₂⟩, x₃⟩ hx ⟨⟨y₁, y₂⟩, y₃⟩ hy hsum
        rcases Finset.mem_product.mp hx with ⟨hx₁₂, hx₃⟩
        rcases Finset.mem_product.mp hx₁₂ with ⟨hx₁, hx₂⟩
        rcases Finset.mem_product.mp hy with ⟨hy₁₂, hy₃⟩
        rcases Finset.mem_product.mp hy₁₂ with ⟨hy₁, hy₂⟩
        rcases mem_powerCurve_iff.mp hx₁ with ⟨a, ha, rfl⟩
        rcases mem_powerCurve_iff.mp hx₂ with ⟨b, hb, rfl⟩
        rcases mem_powerCurve_iff.mp hx₃ with ⟨c, hc, rfl⟩
        rcases mem_powerCurve_iff.mp hy₁ with ⟨d, hd, rfl⟩
        rcases mem_powerCurve_iff.mp hy₂ with ⟨e, he, rfl⟩
        rcases mem_powerCurve_iff.mp hy₃ with ⟨f, hf, rfl⟩
        have hpowers :
            B ^ a + B ^ b + B ^ c = B ^ d + B ^ e + B ^ f := by
          simpa [tripleSum] using congrArg Prod.snd hsum
        exact ((three_powers_sum_eq_iff_perm hB ha hb hc hd he hf).mp
          hpowers).symm.map fun i => (i, B ^ i))

/-- The purely numerical scaling identity used at the end of the Cartesian
product sharpness construction. -/
theorem packet_scale_identity (K n : ℕ) :
    K ^ 5 * n ^ 3 = K ^ 2 * (K * n) ^ 3 := by
  ring

end ThreePowers

end Turning
end ComplexitySensitiveEnergy
