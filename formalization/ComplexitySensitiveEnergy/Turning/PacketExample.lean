import ComplexitySensitiveEnergy.Turning.Definitions
import ComplexitySensitiveEnergy.Turning.Sharpness
import Mathlib

/-!
# The packet example for sharp turning complexity

This file connects the finite combinatorics in `Turning.Sharpness` to the
paper's packet construction.  The main point is kept explicit: a sufficiently
large horizontal spacing separates equality of three packet sums into the
interval coordinate and the power-curve coordinate.
-/

namespace ComplexitySensitiveEnergy
namespace Turning

/-- Apply an arbitrary function to the three labelled entries. -/
def mapTripleFn {G H : Type*} (f : G → H) (x : AdditiveTriple G) :
    AdditiveTriple H :=
  ((f x.1.1, f x.1.2), f x.2)

/-- A restricted Freiman three-isomorphism preserves `J3`.  Both injectivity
and reflection of triple-sum equality are required only on the finite source
set, so this applies to packet encodings that are not globally injective. -/
theorem J3_image_eq_of_threeFreiman
    {G H : Type*} [Add G] [Add H] [DecidableEq G] [DecidableEq H]
    (A : Finset G) (f : G → H)
    (hinj : Set.InjOn f A)
    (hthree : ∀ x ∈ tripleProduct A, ∀ y ∈ tripleProduct A,
      (tripleSum (mapTripleFn f x) = tripleSum (mapTripleFn f y) ↔
        tripleSum x = tripleSum y)) :
    J3 (A.image f) = J3 A := by
  unfold J3
  symm
  apply Finset.card_bij
    (fun q _ => (mapTripleFn f q.1, mapTripleFn f q.2))
  · intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqmem, hqsum⟩
    rcases Finset.mem_product.mp hqmem with ⟨hx, hy⟩
    apply Finset.mem_filter.mpr
    constructor
    · rcases q with ⟨⟨⟨a₁, a₂⟩, a₃⟩, ⟨⟨b₁, b₂⟩, b₃⟩⟩
      simp only [tripleProduct, Finset.mem_product] at hx hy ⊢
      exact ⟨⟨⟨Finset.mem_image.mpr ⟨a₁, hx.1.1, rfl⟩,
          Finset.mem_image.mpr ⟨a₂, hx.1.2, rfl⟩⟩,
          Finset.mem_image.mpr ⟨a₃, hx.2, rfl⟩⟩,
        ⟨⟨Finset.mem_image.mpr ⟨b₁, hy.1.1, rfl⟩,
          Finset.mem_image.mpr ⟨b₂, hy.1.2, rfl⟩⟩,
          Finset.mem_image.mpr ⟨b₃, hy.2, rfl⟩⟩⟩
    · exact (hthree q.1 hx q.2 hy).2 hqsum
  · rintro ⟨⟨⟨a₁, a₂⟩, a₃⟩, ⟨⟨b₁, b₂⟩, b₃⟩⟩ hq₁
      ⟨⟨⟨c₁, c₂⟩, c₃⟩, ⟨⟨d₁, d₂⟩, d₃⟩⟩ hq₂ heq
    have hm₁ := (Finset.mem_filter.mp hq₁).1
    have hm₂ := (Finset.mem_filter.mp hq₂).1
    simp only [Finset.mem_product, tripleProduct] at hm₁ hm₂
    simp only [mapTripleFn, Prod.mk.injEq] at heq
    rcases heq with ⟨⟨⟨ha₁, ha₂⟩, ha₃⟩, ⟨⟨hb₁, hb₂⟩, hb₃⟩⟩
    congr
    · exact hinj hm₁.1.1.1 hm₂.1.1.1 ha₁
    · exact hinj hm₁.1.1.2 hm₂.1.1.2 ha₂
    · exact hinj hm₁.1.2 hm₂.1.2 ha₃
    · exact hinj hm₁.2.1.1 hm₂.2.1.1 hb₁
    · exact hinj hm₁.2.1.2 hm₂.2.1.2 hb₂
    · exact hinj hm₁.2.2 hm₂.2.2 hb₃
  · rintro ⟨⟨⟨x₁, x₂⟩, x₃⟩, ⟨⟨y₁, y₂⟩, y₃⟩⟩ hq
    have hmem := (Finset.mem_filter.mp hq).1
    have hx := (Finset.mem_product.mp hmem).1
    have hy := (Finset.mem_product.mp hmem).2
    have hxPair := (Finset.mem_product.mp hx).1
    have hyPair := (Finset.mem_product.mp hy).1
    rcases Finset.mem_image.mp (Finset.mem_product.mp hxPair).1 with
      ⟨a₁, ha₁, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_product.mp hxPair).2 with
      ⟨a₂, ha₂, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_product.mp hx).2 with
      ⟨a₃, ha₃, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_product.mp hyPair).1 with
      ⟨b₁, hb₁, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_product.mp hyPair).2 with
      ⟨b₂, hb₂, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_product.mp hy).2 with
      ⟨b₃, hb₃, rfl⟩
    have hxA : ((a₁, a₂), a₃) ∈ tripleProduct A := by
      exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨ha₁, ha₂⟩, ha₃⟩
    have hyA : ((b₁, b₂), b₃) ∈ tripleProduct A := by
      exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hb₁, hb₂⟩, hb₃⟩
    have hsum : tripleSum ((a₁, a₂), a₃) =
        tripleSum ((b₁, b₂), b₃) :=
      (hthree _ hxA _ hyA).1 (Finset.mem_filter.mp hq).2
    refine ⟨(((a₁, a₂), a₃), ((b₁, b₂), b₃)), ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hxA, hyA⟩, hsum⟩

/-- The Cartesian source `(j,(i,B^i))`, with `j<K` and `i<n`. -/
def packetSource (B K n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  Finset.range K ×ˢ powerCurve B n

@[simp]
theorem card_packetSource (B K n : ℕ) :
    (packetSource B K n).card = K * n := by
  simp [packetSource]

/-- The paper's packet encoding
`(j,(i,y)) ↦ (Hj+i,Cj+y)`. -/
def packetEncode (H C : ℕ) (p : ℕ × (ℕ × ℕ)) : ℕ × ℕ :=
  (H * p.1 + p.2.1, C * p.1 + p.2.2)

/-- The finite natural-coordinate packet.  Its real realization is introduced
below after the exact combinatorial count has been established. -/
def packetNatSet (H C B K n : ℕ) : Finset (ℕ × ℕ) :=
  (packetSource B K n).image (packetEncode H C)

private theorem packetSource_index_lt {B K n : ℕ}
    {j i y : ℕ} (h : (j, (i, y)) ∈ packetSource B K n) :
    i < n := by
  rcases mem_powerCurve_iff.mp (Finset.mem_product.mp h).2 with
    ⟨a, ha, hp⟩
  have hia : i = a := congrArg Prod.fst hp
  simpa [hia] using ha

/-- Horizontal spacing at least `n` makes the packet encoding injective on
its finite source. -/
theorem packetEncode_injOn {H C B K n : ℕ}
    (hH : 0 < H) (hnH : n ≤ H) :
    Set.InjOn (packetEncode H C) (packetSource B K n) := by
  rintro ⟨j, ⟨i, y⟩⟩ hp ⟨j', ⟨i', y'⟩⟩ hp' hEq
  have hi : i < n := packetSource_index_lt hp
  have hi' : i' < n := packetSource_index_lt hp'
  have hfirst : H * j + i = H * j' + i' := congrArg Prod.fst hEq
  have hmod := congrArg (fun z => z % H) hfirst
  have hii : i = i' := by
    simpa [Nat.add_mod, Nat.mod_eq_of_lt (hi.trans_le hnH),
      Nat.mod_eq_of_lt (hi'.trans_le hnH)] using hmod
  subst i'
  have hjmul : H * j = H * j' := Nat.add_right_cancel hfirst
  have hj : j = j' := Nat.eq_of_mul_eq_mul_left hH hjmul
  subst j'
  have hsecond : C * j + y = C * j + y' := congrArg Prod.snd hEq
  have hy : y = y' := Nat.add_left_cancel hsecond
  subst y'
  rfl

theorem card_packetNatSet {H C B K n : ℕ}
    (hH : 0 < H) (hnH : n ≤ H) :
    (packetNatSet H C B K n).card = K * n := by
  rw [packetNatSet, Finset.card_image_of_injOn (packetEncode_injOn hH hnH)]
  exact card_packetSource B K n

/-- If `H` dominates every possible sum of three within-packet indices, an
equality of encoded triple sums is equivalent to equality in the Cartesian
source.  This is the internal Freiman-separation calculation. -/
theorem packetEncode_three_sum_iff {H C B K n : ℕ}
    (hsep : 3 * n ≤ H)
    (x : AdditiveTriple (ℕ × (ℕ × ℕ))) (hx : x ∈ tripleProduct (packetSource B K n))
    (y : AdditiveTriple (ℕ × (ℕ × ℕ))) (hy : y ∈ tripleProduct (packetSource B K n)) :
    tripleSum (mapTripleFn (packetEncode H C) x) =
        tripleSum (mapTripleFn (packetEncode H C) y) ↔
      tripleSum x = tripleSum y := by
  rcases x with ⟨⟨p₁, p₂⟩, p₃⟩
  rcases y with ⟨⟨q₁, q₂⟩, q₃⟩
  rcases p₁ with ⟨j₁, ⟨i₁, z₁⟩⟩
  rcases p₂ with ⟨j₂, ⟨i₂, z₂⟩⟩
  rcases p₃ with ⟨j₃, ⟨i₃, z₃⟩⟩
  rcases q₁ with ⟨k₁, ⟨u₁, w₁⟩⟩
  rcases q₂ with ⟨k₂, ⟨u₂, w₂⟩⟩
  rcases q₃ with ⟨k₃, ⟨u₃, w₃⟩⟩
  rcases Finset.mem_product.mp hx with ⟨hp₁₂, hp₃⟩
  rcases Finset.mem_product.mp hp₁₂ with ⟨hp₁, hp₂⟩
  rcases Finset.mem_product.mp hy with ⟨hq₁₂, hq₃⟩
  rcases Finset.mem_product.mp hq₁₂ with ⟨hq₁, hq₂⟩
  have hi₁ : i₁ < n := packetSource_index_lt hp₁
  have hi₂ : i₂ < n := packetSource_index_lt hp₂
  have hi₃ : i₃ < n := packetSource_index_lt hp₃
  have hu₁ : u₁ < n := packetSource_index_lt hq₁
  have hu₂ : u₂ < n := packetSource_index_lt hq₂
  have hu₃ : u₃ < n := packetSource_index_lt hq₃
  constructor
  · intro hencoded
    have hfirstRaw :
        (H * j₁ + i₁) + (H * j₂ + i₂) + (H * j₃ + i₃) =
          (H * k₁ + u₁) + (H * k₂ + u₂) + (H * k₃ + u₃) := by
      simpa [mapTripleFn, packetEncode, tripleSum] using
        congrArg Prod.fst hencoded
    have hfirst :
        H * (j₁ + j₂ + j₃) + (i₁ + i₂ + i₃) =
          H * (k₁ + k₂ + k₃) + (u₁ + u₂ + u₃) := by
      calc
        H * (j₁ + j₂ + j₃) + (i₁ + i₂ + i₃) =
            (H * j₁ + i₁) + (H * j₂ + i₂) + (H * j₃ + i₃) := by ring
        _ = (H * k₁ + u₁) + (H * k₂ + u₂) + (H * k₃ + u₃) := hfirstRaw
        _ = H * (k₁ + k₂ + k₃) + (u₁ + u₂ + u₃) := by ring
    have hiH : i₁ + i₂ + i₃ < H := by omega
    have huH : u₁ + u₂ + u₃ < H := by omega
    have hiSum : i₁ + i₂ + i₃ = u₁ + u₂ + u₃ := by
      have hmod := congrArg (fun z => z % H) hfirst
      simpa [Nat.add_mod, Nat.mod_eq_of_lt hiH,
        Nat.mod_eq_of_lt huH] using hmod
    have hH : 0 < H := by omega
    have hjSum : j₁ + j₂ + j₃ = k₁ + k₂ + k₃ := by
      have hfirst' := hfirst
      rw [hiSum] at hfirst'
      exact Nat.eq_of_mul_eq_mul_left hH (Nat.add_right_cancel hfirst')
    have hsecondRaw :
        (C * j₁ + z₁) + (C * j₂ + z₂) + (C * j₃ + z₃) =
          (C * k₁ + w₁) + (C * k₂ + w₂) + (C * k₃ + w₃) := by
      simpa [mapTripleFn, packetEncode, tripleSum] using
        congrArg Prod.snd hencoded
    have hsecond :
        C * (j₁ + j₂ + j₃) + (z₁ + z₂ + z₃) =
          C * (k₁ + k₂ + k₃) + (w₁ + w₂ + w₃) := by
      calc
        C * (j₁ + j₂ + j₃) + (z₁ + z₂ + z₃) =
            (C * j₁ + z₁) + (C * j₂ + z₂) + (C * j₃ + z₃) := by ring
        _ = (C * k₁ + w₁) + (C * k₂ + w₂) + (C * k₃ + w₃) := hsecondRaw
        _ = C * (k₁ + k₂ + k₃) + (w₁ + w₂ + w₃) := by ring
    have hzSum : z₁ + z₂ + z₃ = w₁ + w₂ + w₃ := by
      rw [hjSum] at hsecond
      exact Nat.add_left_cancel hsecond
    apply Prod.ext
    · simpa [tripleSum] using hjSum
    · apply Prod.ext
      · simpa [tripleSum] using hiSum
      · simpa [tripleSum] using hzSum
  · intro hsource
    have hjSum : j₁ + j₂ + j₃ = k₁ + k₂ + k₃ := by
      simpa [tripleSum] using congrArg Prod.fst hsource
    have hiSum : i₁ + i₂ + i₃ = u₁ + u₂ + u₃ := by
      simpa [tripleSum] using
        congrArg (fun p : ℕ × (ℕ × ℕ) => p.2.1) hsource
    have hzSum : z₁ + z₂ + z₃ = w₁ + w₂ + w₃ := by
      simpa [tripleSum] using
        congrArg (fun p : ℕ × (ℕ × ℕ) => p.2.2) hsource
    apply Prod.ext
    · change
        (H * j₁ + i₁) + (H * j₂ + i₂) + (H * j₃ + i₃) =
          (H * k₁ + u₁) + (H * k₂ + u₂) + (H * k₃ + u₃)
      calc
        (H * j₁ + i₁) + (H * j₂ + i₂) + (H * j₃ + i₃) =
            H * (j₁ + j₂ + j₃) + (i₁ + i₂ + i₃) := by ring
        _ = H * (k₁ + k₂ + k₃) + (u₁ + u₂ + u₃) := by rw [hjSum, hiSum]
        _ = (H * k₁ + u₁) + (H * k₂ + u₂) + (H * k₃ + u₃) := by ring
    · change
        (C * j₁ + z₁) + (C * j₂ + z₂) + (C * j₃ + z₃) =
          (C * k₁ + w₁) + (C * k₂ + w₂) + (C * k₃ + w₃)
      calc
        (C * j₁ + z₁) + (C * j₂ + z₂) + (C * j₃ + z₃) =
            C * (j₁ + j₂ + j₃) + (z₁ + z₂ + z₃) := by ring
        _ = C * (k₁ + k₂ + k₃) + (w₁ + w₂ + w₃) := by rw [hjSum, hzSum]
        _ = (C * k₁ + w₁) + (C * k₂ + w₂) + (C * k₃ + w₃) := by ring

/-- Exact factorization of packet energy into the interval and power-curve
energies. -/
theorem J3_packetNatSet_eq {H C B K n : ℕ}
    (hn : 0 < n) (hsep : 3 * n ≤ H) :
    J3 (packetNatSet H C B K n) =
      J3 (Finset.range K) * J3 (powerCurve B n) := by
  have hH : 0 < H := by omega
  have hnH : n ≤ H := by omega
  calc
    J3 (packetNatSet H C B K n) = J3 (packetSource B K n) := by
      exact J3_image_eq_of_threeFreiman
        (packetSource B K n) (packetEncode H C)
        (packetEncode_injOn hH hnH)
        (packetEncode_three_sum_iff hsep)
    _ = J3 (Finset.range K) * J3 (powerCurve B n) := by
      exact J3_product (Finset.range K) (powerCurve B n)

/-- Explicit product-form bounds for the packet. -/
theorem J3_packetNatSet_between {H C B K n : ℕ}
    (hB : 4 ≤ B) (hn : 0 < n) (hsep : 3 * n ≤ H) :
    (K / 3) ^ 5 * n ^ 3 ≤ J3 (packetNatSet H C B K n) ∧
      J3 (packetNatSet H C B K n) ≤ 6 * K ^ 5 * n ^ 3 := by
  rw [J3_packetNatSet_eq hn hsep]
  constructor
  · exact Nat.mul_le_mul (J3_range_between K).1
      (J3_powerCurve_between hB).1
  · calc
      J3 (Finset.range K) * J3 (powerCurve B n) ≤
          K ^ 5 * (6 * n ^ 3) :=
        Nat.mul_le_mul (J3_range_between K).2
          (J3_powerCurve_between hB).2
      _ = 6 * K ^ 5 * n ^ 3 := by ring

/-- The sharpness scale written in the paper's variables `N = K n`.
The constants `3125` and `6` are completely explicit. -/
theorem J3_packetNatSet_scale {H C B K n : ℕ}
    (hB : 4 ≤ B) (hn : 0 < n) (hsep : 3 * n ≤ H) :
    K ^ 2 * (K * n) ^ 3 ≤
        3125 * J3 (packetNatSet H C B K n) ∧
      J3 (packetNatSet H C B K n) ≤
        6 * (K ^ 2 * (K * n) ^ 3) := by
  rw [J3_packetNatSet_eq hn hsep]
  constructor
  · calc
      K ^ 2 * (K * n) ^ 3 = K ^ 5 * n ^ 3 :=
        (packet_scale_identity K n).symm
      _ ≤ (3125 * J3 (Finset.range K)) * n ^ 3 :=
        Nat.mul_le_mul_right (n ^ 3)
          (J3_range_explicit_comparison K).1
      _ ≤ (3125 * J3 (Finset.range K)) * J3 (powerCurve B n) :=
        Nat.mul_le_mul_left _ (J3_powerCurve_between hB).1
      _ = 3125 * (J3 (Finset.range K) * J3 (powerCurve B n)) := by ring
  · calc
      J3 (Finset.range K) * J3 (powerCurve B n) ≤
          K ^ 5 * (6 * n ^ 3) :=
        Nat.mul_le_mul (J3_range_between K).2
          (J3_powerCurve_between hB).2
      _ = 6 * (K ^ 2 * (K * n) ^ 3) := by
        rw [← packet_scale_identity]
        ring

/-- Coordinatewise casting of a natural pair into the paper's real plane. -/
def natPairR2 (p : ℕ × ℕ) : R2 :=
  ![(p.1 : ℝ), (p.2 : ℝ)]

theorem natPairR2_injective : Function.Injective natPairR2 := by
  intro p q h
  apply Prod.ext
  · have hzero := congrArg (fun v : R2 => v 0) h
    simpa [natPairR2] using hzero
  · have hone := congrArg (fun v : R2 => v 1) h
    simpa [natPairR2] using hone

@[simp]
theorem natPairR2_add (p q : ℕ × ℕ) :
    natPairR2 (p + q) = natPairR2 p + natPairR2 q := by
  ext i
  fin_cases i <;> simp [natPairR2]

theorem tripleSum_mapTripleFn_natPairR2 (x : AdditiveTriple (ℕ × ℕ)) :
    tripleSum (mapTripleFn natPairR2 x) = natPairR2 (tripleSum x) := by
  rcases x with ⟨⟨p, q⟩, r⟩
  simp [mapTripleFn, tripleSum]

/-- The packet as an actual finite subset of `R2`. -/
noncomputable def packetR2Set (H C B K n : ℕ) : Finset R2 :=
  (packetNatSet H C B K n).image natPairR2

@[simp]
theorem card_packetR2Set {H C B K n : ℕ}
    (hH : 0 < H) (hnH : n ≤ H) :
    (packetR2Set H C B K n).card = K * n := by
  rw [packetR2Set,
    Finset.card_image_of_injOn natPairR2_injective.injOn,
    card_packetNatSet hH hnH]

theorem J3_packetR2Set_eq_packetNatSet (H C B K n : ℕ) :
    J3 (packetR2Set H C B K n) = J3 (packetNatSet H C B K n) := by
  apply J3_image_eq_of_threeFreiman
  · exact natPairR2_injective.injOn
  · intro x _ y _
    rw [tripleSum_mapTripleFn_natPairR2,
      tripleSum_mapTripleFn_natPairR2]
    exact natPairR2_injective.eq_iff

theorem J3_packetR2Set_eq {H C B K n : ℕ}
    (hn : 0 < n) (hsep : 3 * n ≤ H) :
    J3 (packetR2Set H C B K n) =
      J3 (Finset.range K) * J3 (powerCurve B n) := by
  rw [J3_packetR2Set_eq_packetNatSet,
    J3_packetNatSet_eq hn hsep]

theorem J3_packetR2Set_scale {H C B K n : ℕ}
    (hB : 4 ≤ B) (hn : 0 < n) (hsep : 3 * n ≤ H) :
    K ^ 2 * (K * n) ^ 3 ≤
        3125 * J3 (packetR2Set H C B K n) ∧
      J3 (packetR2Set H C B K n) ≤
        6 * (K ^ 2 * (K * n) ^ 3) := by
  simpa only [J3_packetR2Set_eq_packetNatSet] using
    J3_packetNatSet_scale hB hn hsep

/-- First and second coordinate projections used to order packet points and
form their slopes. -/
def firstCoordinate : R2 →ₗ[ℝ] ℝ where
  toFun p := p 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def secondCoordinate : R2 →ₗ[ℝ] ℝ where
  toFun p := p 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinatePair_injective :
    Function.Injective
      (fun p : R2 => (firstCoordinate p, secondCoordinate p)) := by
  intro p q hpq
  funext i
  fin_cases i
  · exact congrArg Prod.fst hpq
  · exact congrArg Prod.snd hpq

/-- The literal paper point `(Hj+i, Cj+B^i)`. -/
def packetPointR2 (H C B j i : ℕ) : R2 :=
  natPairR2 (packetEncode H C (j, (i, B ^ i)))

/-- One consecutive packet, with `i=0,…,n-1`. -/
def packetBlock (H C B j n : ℕ) : List R2 :=
  (List.range n).map (packetPointR2 H C B j)

/-- The proposed `K` signed-convex blocks. -/
def packetBlocks (H C B K n : ℕ) : List (List R2) :=
  (List.range K).map fun j => packetBlock H C B j n

/-- The ordered packet configuration, before packaging the ordering proofs. -/
def packetPointList (H C B K n : ℕ) : List R2 :=
  (List.range K).flatMap fun j => packetBlock H C B j n

@[simp]
theorem length_packetBlock (H C B j n : ℕ) :
    (packetBlock H C B j n).length = n := by
  simp [packetBlock]

@[simp]
theorem length_packetBlocks (H C B K n : ℕ) :
    (packetBlocks H C B K n).length = K := by
  simp [packetBlocks]

@[simp]
theorem flatten_packetBlocks (H C B K n : ℕ) :
    (packetBlocks H C B K n).flatten = packetPointList H C B K n := by
  simp [packetBlocks, packetPointList, List.flatMap]

private theorem packetPointList_ell_strict {H C B K n : ℕ}
    (hnH : n ≤ H) :
    ((packetPointList H C B K n).map firstCoordinate).Pairwise
      (fun x y => x < y) := by
  rw [List.pairwise_map]
  rw [packetPointList, List.pairwise_flatMap]
  constructor
  · intro j hj
    rw [packetBlock, List.pairwise_map]
    exact List.pairwise_lt_range.imp fun {i i'} hii => by
      have hnat : H * j + i < H * j + i' :=
        Nat.add_lt_add_left hii (H * j)
      change ((H * j + i : ℕ) : ℝ) < ((H * j + i' : ℕ) : ℝ)
      exact_mod_cast hnat
  · exact List.pairwise_lt_range.imp fun {j j'} hjj => by
      intro p hp q hq
      rcases List.mem_map.mp hp with ⟨i, hi, rfl⟩
      rcases List.mem_map.mp hq with ⟨i', hi', rfl⟩
      have hiN : i < n := List.mem_range.mp hi
      have hiN' : i' < n := List.mem_range.mp hi'
      have hnat : H * j + i < H * j' + i' := by
        calc
          H * j + i < H * j + H :=
            Nat.add_lt_add_left (hiN.trans_le hnH) _
          _ = H * (j + 1) := by ring
          _ ≤ H * j' := Nat.mul_le_mul_left H (by omega)
          _ ≤ H * j' + i' := Nat.le_add_right _ _
      change ((H * j + i : ℕ) : ℝ) < ((H * j' + i' : ℕ) : ℝ)
      exact_mod_cast hnat

private theorem packetPointList_nodup {H C B K n : ℕ}
    (hnH : n ≤ H) :
    (packetPointList H C B K n).Nodup := by
  have hmap : ((packetPointList H C B K n).map firstCoordinate).Nodup :=
    (packetPointList_ell_strict hnH).imp fun h => ne_of_lt h
  exact hmap.of_map firstCoordinate

/-- Adjacent slopes of a list sampled on a consecutive natural range. -/
private theorem adjacentSlopes_map_range'
    (ell transverse : R2 →ₗ[ℝ] ℝ) (f : ℕ → R2)
    (start len : ℕ) :
    adjacentSlopes ell transverse ((List.range' start len).map f) =
      (List.range' start (len - 1)).map fun i =>
        (transverse (f (i + 1)) - transverse (f i)) /
          (ell (f (i + 1)) - ell (f i)) := by
  induction len generalizing start with
  | zero => simp [adjacentSlopes]
  | succ len ih =>
      cases len with
      | zero => simp [adjacentSlopes]
      | succ len =>
          simp only [List.range'_succ, List.map_cons, Nat.succ_sub_one]
          simp only [adjacentSlopes]
          have htail := ih (start := start + 1)
          simp only [List.range'_succ, List.map_cons,
            Nat.succ_sub_one] at htail
          rw [htail]

/-- Exact adjacent-slope list inside one packet. -/
theorem adjacentSlopes_packetBlock {H C B j n : ℕ} :
    adjacentSlopes firstCoordinate secondCoordinate
        (packetBlock H C B j n) =
      (List.range (n - 1)).map fun i =>
        (B : ℝ) ^ i * ((B : ℝ) - 1) := by
  unfold packetBlock
  simp only [List.range_eq_range']
  rw [adjacentSlopes_map_range']
  apply List.map_congr_left
  intro i hi
  simp [packetPointR2, natPairR2, packetEncode,
    firstCoordinate, secondCoordinate, pow_succ]
  ring

/-- Within a packet, the adjacent slopes are `B^i (B-1)`, hence strictly
increasing for `B≥2`. -/
theorem packetBlock_signedConvex {H C B j n : ℕ} (hB : 2 ≤ B) :
    IsSignedConvexBlock firstCoordinate secondCoordinate
      (packetBlock H C B j n) := by
  left
  rw [adjacentSlopes_packetBlock, List.pairwise_map]
  exact List.pairwise_lt_range.imp fun {i i'} hii => by
    have hbase : (1 : ℝ) < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
    exact mul_lt_mul_of_pos_right (pow_lt_pow_right₀ hbase hii)
      (sub_pos.mpr hbase)

/-- Adjacent slopes across an append consist of the slopes on the two lists
and the single joining slope. -/
private theorem adjacentSlopes_append_of_ne_nil
    (ell transverse : R2 →ₗ[ℝ] ℝ) (l r : List R2)
    (hl : l ≠ []) (hr : r ≠ []) :
    adjacentSlopes ell transverse (l ++ r) =
      adjacentSlopes ell transverse l ++
        [(transverse (r.head hr) - transverse (l.getLast hl)) /
          (ell (r.head hr) - ell (l.getLast hl))] ++
        adjacentSlopes ell transverse r := by
  induction l generalizing r with
  | nil => simp at hl
  | cons p l ih =>
      cases l with
      | nil =>
          rcases r with _ | ⟨q, r⟩
          · simp at hr
          · simp [adjacentSlopes]
      | cons q l =>
          have htail : (q :: l) ≠ [] := by simp
          have hih := ih (r := r) htail hr
          calc
            adjacentSlopes ell transverse ((p :: q :: l) ++ r) =
                (transverse q - transverse p) / (ell q - ell p) ::
                  adjacentSlopes ell transverse ((q :: l) ++ r) := rfl
            _ = (transverse q - transverse p) / (ell q - ell p) ::
                  (adjacentSlopes ell transverse (q :: l) ++
                    [(transverse (r.head hr) -
                        transverse ((q :: l).getLast htail)) /
                      (ell (r.head hr) - ell ((q :: l).getLast htail))] ++
                    adjacentSlopes ell transverse r) :=
              congrArg (List.cons
                ((transverse q - transverse p) / (ell q - ell p))) hih
            _ = adjacentSlopes ell transverse (p :: q :: l) ++
                  [(transverse (r.head hr) -
                      transverse ((p :: q :: l).getLast hl)) /
                    (ell (r.head hr) - ell ((p :: q :: l).getLast hl))] ++
                  adjacentSlopes ell transverse r := by
              simp only [adjacentSlopes, List.cons_append,
                List.getLast_cons htail]

theorem count_zero_adjacentSlopes_packetBlock
    {H C B j n : ℕ} (hB : 2 ≤ B) :
    (adjacentSlopes firstCoordinate secondCoordinate
      (packetBlock H C B j n)).count 0 = 0 := by
  rw [adjacentSlopes_packetBlock]
  apply List.count_eq_zero.mpr
  intro hzero
  rcases List.mem_map.mp hzero with ⟨i, hi, heq⟩
  have hbase : (1 : ℝ) < (B : ℝ) := by
    exact_mod_cast (show 1 < B by omega)
  have hpos : 0 < (B : ℝ) ^ i * ((B : ℝ) - 1) :=
    mul_pos (pow_pos (by positivity) _) (sub_pos.mpr hbase)
  exact hpos.ne' heq

private theorem packetPointList_succ (H C B K n : ℕ) :
    packetPointList H C B (K + 1) n =
      packetPointList H C B K n ++ packetBlock H C B K n := by
  simp [packetPointList, List.range_succ, packetBlock]

private theorem packetBlock_ne_nil {H C B j n : ℕ} (hn : 0 < n) :
    packetBlock H C B j n ≠ [] := by
  simp [packetBlock, hn.ne']

private theorem packetPointList_succ_ne_nil
    {H C B K n : ℕ} (hn : 0 < n) :
    packetPointList H C B (K + 1) n ≠ [] := by
  rw [packetPointList_succ]
  exact List.append_ne_nil_of_right_ne_nil _ (packetBlock_ne_nil hn)

private theorem getLast?_packetPointList_succ
    {H C B K n : ℕ} (hn : 0 < n) :
    (packetPointList H C B (K + 1) n).getLast? =
      some (packetPointR2 H C B K (n - 1)) := by
  rw [packetPointList_succ]
  rw [List.getLast?_append_of_ne_nil _ (packetBlock_ne_nil hn)]
  simp [packetBlock, List.getLast?_range, hn.ne']

private theorem getLast_packetPointList_succ
    {H C B K n : ℕ} (hn : 0 < n)
    (h : packetPointList H C B (K + 1) n ≠ []) :
    (packetPointList H C B (K + 1) n).getLast h =
      packetPointR2 H C B K (n - 1) := by
  have hopt := getLast?_packetPointList_succ
    (H := H) (C := C) (B := B) (K := K) hn
  rw [List.getLast?_eq_some_getLast h] at hopt
  exact Option.some.inj hopt

private theorem head_packetBlock
    {H C B j n : ℕ} (h : packetBlock H C B j n ≠ []) :
    (packetBlock H C B j n).head h = packetPointR2 H C B j 0 := by
  simp [packetBlock]

/-- With `C=B^(n-1)-1`, every joining slope between two consecutive packets
is exactly zero. -/
private theorem packetBoundarySlope_zero
    {B n j : ℕ} (hB : 2 ≤ B) :
    (secondCoordinate
          (packetPointR2 (3 * n) (B ^ (n - 1) - 1) B (j + 1) 0) -
        secondCoordinate
          (packetPointR2 (3 * n) (B ^ (n - 1) - 1) B j (n - 1))) /
      (firstCoordinate
          (packetPointR2 (3 * n) (B ^ (n - 1) - 1) B (j + 1) 0) -
        firstCoordinate
          (packetPointR2 (3 * n) (B ^ (n - 1) - 1) B j (n - 1))) = 0 := by
  have hpow : 0 < B ^ (n - 1) := pow_pos (by omega) _
  have hyNat :
      (B ^ (n - 1) - 1) * (j + 1) + B ^ 0 =
        (B ^ (n - 1) - 1) * j + B ^ (n - 1) := by
    rw [pow_zero, Nat.mul_add]
    omega
  have hy :
      secondCoordinate
          (packetPointR2 (3 * n) (B ^ (n - 1) - 1) B (j + 1) 0) =
        secondCoordinate
          (packetPointR2 (3 * n) (B ^ (n - 1) - 1) B j (n - 1)) := by
    change
      (((B ^ (n - 1) - 1) * (j + 1) + B ^ 0 : ℕ) : ℝ) =
        (((B ^ (n - 1) - 1) * j + B ^ (n - 1) : ℕ) : ℝ)
    exact_mod_cast hyNat
  rw [hy]
  simp

private theorem count_zero_adjacentSlopes_packetPointList_add_two
    {B K n : ℕ} (hB : 2 ≤ B) (hn : 0 < n) :
    (adjacentSlopes firstCoordinate secondCoordinate
        (packetPointList (3 * n) (B ^ (n - 1) - 1) B (K + 2) n)).count 0 =
      (adjacentSlopes firstCoordinate secondCoordinate
        (packetPointList (3 * n) (B ^ (n - 1) - 1) B (K + 1) n)).count 0 + 1 := by
  rw [show K + 2 = (K + 1) + 1 by omega, packetPointList_succ]
  rw [adjacentSlopes_append_of_ne_nil _ _ _ _
    (packetPointList_succ_ne_nil hn) (packetBlock_ne_nil hn)]
  rw [getLast_packetPointList_succ hn (packetPointList_succ_ne_nil hn),
    head_packetBlock (packetBlock_ne_nil hn), packetBoundarySlope_zero hB]
  simp [count_zero_adjacentSlopes_packetBlock hB]

/-- For the strict-reset packet `C=B^(n-1)-1`, the full ordered slope list
contains exactly one zero at every boundary between consecutive packets. -/
theorem count_zero_adjacentSlopes_resetPacket
    {B K n : ℕ} (hB : 2 ≤ B) (hn : 0 < n) :
    (adjacentSlopes firstCoordinate secondCoordinate
      (packetPointList (3 * n) (B ^ (n - 1) - 1) B K n)).count 0 = K - 1 := by
  induction K with
  | zero => simp [packetPointList, adjacentSlopes]
  | succ K ih =>
      cases K with
      | zero =>
          rw [packetPointList_succ]
          simpa [packetPointList] using
            (count_zero_adjacentSlopes_packetBlock
              (H := 3 * n) (C := B ^ (n - 1) - 1)
              (B := B) (j := 0) (n := n) hB)
      | succ K =>
          rw [count_zero_adjacentSlopes_packetPointList_add_two hB hn, ih]
          omega

/-- When nonempty consecutive blocks are flattened, the only slopes absent
from the internal block lists are the at most `m-1` joining slopes. -/
private theorem count_zero_adjacentSlopes_flatten_le
    (ell transverse : R2 →ₗ[ℝ] ℝ) (blocks : List (List R2))
    (hne : blocks.Forall fun block => block ≠ []) :
    (adjacentSlopes ell transverse blocks.flatten).count 0 ≤
      (blocks.map fun block =>
          (adjacentSlopes ell transverse block).count 0).sum +
        (blocks.length - 1) := by
  induction blocks with
  | nil => simp [adjacentSlopes]
  | cons block blocks ih =>
      cases blocks with
      | nil => simp
      | cons next rest =>
          have hblock : block ≠ [] := hne.1
          have htail : (next :: rest).Forall fun b => b ≠ [] := hne.2
          have htail' : next ≠ [] ∧ rest.Forall (fun b => b ≠ []) := by
            simpa using htail
          have hnext : next ≠ [] := htail'.1
          have hflatTail : (next :: rest).flatten ≠ [] := by
            simpa only [List.flatten_cons] using
              List.append_ne_nil_of_left_ne_nil hnext rest.flatten
          have hih := ih htail
          change
            (adjacentSlopes ell transverse
              (block ++ (next :: rest).flatten)).count 0 ≤ _
          rw [adjacentSlopes_append_of_ne_nil _ _ _ _ hblock hflatTail,
            List.count_append, List.count_append]
          have hjoin :
              [
            ((transverse ((next :: rest).flatten.head hflatTail) -
                  transverse (block.getLast hblock)) /
                (ell ((next :: rest).flatten.head hflatTail) -
                  ell (block.getLast hblock)))].count 0 ≤ 1 := by
            exact List.count_le_length
          simp only [List.map_cons, List.sum_cons, List.length_cons] at hih ⊢
          omega

/-- A strictly monotone list cannot contain the same slope (in particular
zero) more than once. -/
private theorem count_zero_adjacentSlopes_le_one_of_signedConvex
    (ell transverse : R2 →ₗ[ℝ] ℝ) (block : List R2)
    (hsigned : IsSignedConvexBlock ell transverse block) :
    (adjacentSlopes ell transverse block).count 0 ≤ 1 := by
  apply (List.nodup_iff_count_le_one.mp ?_) 0
  rcases hsigned with hinc | hdec
  · exact hinc.imp fun hlt => ne_of_lt hlt
  · exact hdec.imp fun hgt => ne_of_gt hgt

private theorem sum_count_zero_adjacentSlopes_le_length
    (ell transverse : R2 →ₗ[ℝ] ℝ) (blocks : List (List R2))
    (hsigned : blocks.Forall fun block =>
      IsSignedConvexBlock ell transverse block) :
    (blocks.map fun block =>
        (adjacentSlopes ell transverse block).count 0).sum ≤ blocks.length := by
  induction blocks with
  | nil => simp
  | cons block blocks ih =>
      have hsigned' :
          IsSignedConvexBlock ell transverse block ∧
            blocks.Forall (fun b => IsSignedConvexBlock ell transverse b) := by
        simpa using hsigned
      have hblock := count_zero_adjacentSlopes_le_one_of_signedConvex
        ell transverse block hsigned'.1
      have htail := ih hsigned'.2
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- The list construction and the two-stage finite-set image define exactly
the same real packet. -/
theorem packetPointList_toFinset (H C B K n : ℕ) :
    (packetPointList H C B K n).toFinset = packetR2Set H C B K n := by
  classical
  ext p
  constructor
  · intro hp
    rw [List.mem_toFinset, packetPointList, List.mem_flatMap] at hp
    rcases hp with ⟨j, hj, hp⟩
    rw [packetBlock] at hp
    rcases List.mem_map.mp hp with ⟨i, hi, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨packetEncode H C (j, (i, B ^ i)), ?_, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(j, (i, B ^ i)), ?_, rfl⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (List.mem_range.mp hj),
        mem_powerCurve_iff.mpr
          ⟨i, List.mem_range.mp hi, rfl⟩⟩
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    rcases Finset.mem_image.mp hq with
      ⟨⟨j, ⟨i, y⟩⟩, hsource, rfl⟩
    rcases Finset.mem_product.mp hsource with ⟨hj, hiy⟩
    rcases mem_powerCurve_iff.mp hiy with ⟨a, ha, hpair⟩
    have hi : i = a := congrArg Prod.fst hpair
    have hy : y = B ^ a := congrArg Prod.snd hpair
    subst i
    subst y
    rw [List.mem_toFinset, packetPointList, List.mem_flatMap]
    refine ⟨j, List.mem_range.mpr (Finset.mem_range.mp hj), ?_⟩
    rw [packetBlock]
    exact List.mem_map.mpr
      ⟨a, List.mem_range.mpr ha, rfl⟩

/-- The paper packet packaged as an `OrderedConfiguration`, ordered first by
packet number `j` and then by its internal index `i`. -/
noncomputable def packetConfiguration
    (H C B K n : ℕ) (hnH : n ≤ H) : OrderedConfiguration where
  points := packetPointList H C B K n
  nodup := packetPointList_nodup hnH
  ell := firstCoordinate
  transverse := secondCoordinate
  coordinates_injective := coordinatePair_injective
  ell_strict := packetPointList_ell_strict hnH

@[simp]
theorem pointSet_packetConfiguration
    (H C B K n : ℕ) (hnH : n ≤ H) :
    pointSet (packetConfiguration H C B K n hnH) =
      packetR2Set H C B K n := by
  classical
  exact packetPointList_toFinset H C B K n

@[simp]
theorem card_pointSet_packetConfiguration
    (H C B K n : ℕ) (hnH : n ≤ H) :
    (pointSet (packetConfiguration H C B K n hnH)).card = K * n := by
  rw [card_pointSet]
  simp [packetConfiguration, packetPointList]

/-- The displayed packets themselves form a signed-convex partition with at
most `K` blocks. -/
theorem packetConfiguration_hasSignedConvexPartitionAtMost
    {H C B K n : ℕ} (hB : 2 ≤ B) (hn : 0 < n) (hnH : n ≤ H) :
    HasSignedConvexPartitionAtMost
      (packetConfiguration H C B K n hnH) K := by
  refine ⟨packetBlocks H C B K n, ?_, by simp⟩
  constructor
  · simp [packetConfiguration]
  · rw [packetBlocks, List.forall_map_iff, List.forall_iff_forall_mem]
    intro j hj
    constructor
    · intro hempty
      have hlen := congrArg List.length hempty
      simp at hlen
      omega
    · simpa [packetConfiguration] using
        (packetBlock_signedConvex (H := H) (C := C) (j := j)
          (n := n) hB)

/-- The full combinatorial sharpness estimate transferred to the point set of
the ordered configuration. -/
theorem J3_packetConfiguration_scale
    {H C B K n : ℕ} (hB : 4 ≤ B) (hn : 0 < n)
    (hsep : 3 * n ≤ H) :
    let hnH : n ≤ H := by omega
    K ^ 2 * (K * n) ^ 3 ≤
        3125 * J3 (pointSet (packetConfiguration H C B K n hnH)) ∧
      J3 (pointSet (packetConfiguration H C B K n hnH)) ≤
        6 * (K ^ 2 * (K * n) ^ 3) := by
  dsimp only
  rw [pointSet_packetConfiguration]
  exact J3_packetR2Set_scale hB hn hsep

/-- A canonical choice of the horizontal separation parameter.  The vertical
packet offset `C` is deliberately arbitrary: after the first coordinate has
separated packet-index sums, it cancels from the second coordinate. -/
noncomputable def canonicalPacketConfiguration (C B K n : ℕ) :
    OrderedConfiguration :=
  packetConfiguration (3 * n) C B K n (by omega)

/-- Canonical packet with the vertical offset that makes every inter-packet
slope equal to zero. -/
noncomputable def resetPacketConfiguration (B K n : ℕ) :
    OrderedConfiguration :=
  canonicalPacketConfiguration (B ^ (n - 1) - 1) B K n

/-- Strict reset lower bound: every consecutive signed-convex partition of
the reset packet has at least half as many blocks as packets. -/
theorem resetPacket_forces_linear_block_count
    {B K n : ℕ} (hB : 2 ≤ B) (hn : 0 < n)
    {blocks : List (List R2)}
    (hpart : IsSignedConvexPartition
      (resetPacketConfiguration B K n) blocks) :
    K ≤ 2 * blocks.length := by
  rcases hpart with ⟨hflatten, hblocks⟩
  have hne : blocks.Forall fun block => block ≠ [] := by
    rw [List.forall_iff_forall_mem]
    intro block hblock
    exact (List.forall_iff_forall_mem.mp hblocks block hblock).1
  have hsigned : blocks.Forall fun block =>
      IsSignedConvexBlock firstCoordinate secondCoordinate block := by
    rw [List.forall_iff_forall_mem]
    intro block hblock
    have hb := (List.forall_iff_forall_mem.mp hblocks block hblock).2
    simpa [resetPacketConfiguration, canonicalPacketConfiguration,
      packetConfiguration] using hb
  have hflat := count_zero_adjacentSlopes_flatten_le
    firstCoordinate secondCoordinate blocks hne
  rw [hflatten] at hflat
  change
    (adjacentSlopes firstCoordinate secondCoordinate
      (packetPointList (3 * n) (B ^ (n - 1) - 1) B K n)).count 0 ≤ _
    at hflat
  rw [count_zero_adjacentSlopes_resetPacket hB hn] at hflat
  have hsum := sum_count_zero_adjacentSlopes_le_length
    firstCoordinate secondCoordinate blocks hsigned
  by_cases hK : K = 0
  · omega
  have hpoints :
      packetPointList (3 * n) (B ^ (n - 1) - 1) B K n ≠ [] := by
    cases K with
    | zero => contradiction
    | succ K => exact packetPointList_succ_ne_nil hn
  have hflatten' :
      blocks.flatten =
        packetPointList (3 * n) (B ^ (n - 1) - 1) B K n := by
    simpa [resetPacketConfiguration, canonicalPacketConfiguration,
      packetConfiguration] using hflatten
  have hblocks : blocks ≠ [] := by
    intro hempty
    subst blocks
    simp only [List.flatten_nil] at hflatten'
    exact hpoints hflatten'.symm
  have hlength : 0 < blocks.length := List.length_pos_of_ne_nil hblocks
  omega

/-- One-stop internal construction of the paper example with `H=3n`:
cardinality `Kn`, a signed-convex partition into at most `K` packets, and the
sharp `K²N³` energy scale. -/
theorem canonicalPacketConfiguration_properties
    {C B K n : ℕ} (hB : 4 ≤ B) (hn : 0 < n) :
    (pointSet (canonicalPacketConfiguration C B K n)).card = K * n ∧
      HasSignedConvexPartitionAtMost
        (canonicalPacketConfiguration C B K n) K ∧
      K ^ 2 * (K * n) ^ 3 ≤
          3125 * J3 (pointSet (canonicalPacketConfiguration C B K n)) ∧
        J3 (pointSet (canonicalPacketConfiguration C B K n)) ≤
          6 * (K ^ 2 * (K * n) ^ 3) := by
  have hnH : n ≤ 3 * n := by omega
  constructor
  · simpa [canonicalPacketConfiguration] using
      card_pointSet_packetConfiguration (3 * n) C B K n hnH
  constructor
  · simpa [canonicalPacketConfiguration] using
      packetConfiguration_hasSignedConvexPartitionAtMost
        (H := 3 * n) (C := C) (K := K) (n := n)
        (by omega : 2 ≤ B) hn hnH
  · simpa [canonicalPacketConfiguration] using
      (J3_packetConfiguration_scale
        (H := 3 * n) (C := C) (K := K) (n := n) hB hn (by omega))

/-- General proof-carrying interface for a lower bound on the number of
consecutive signed-convex blocks.  The explicit reset packet below supplies
such a certificate internally. -/
structure SignedSlopeResetCertificate (P : OrderedConfiguration) (L : ℕ) : Prop where
  forces_block_count : ∀ blocks : List (List R2),
    IsSignedConvexPartition P blocks → L ≤ blocks.length

/-- The explicit reset packet supplies a fully internal linear lower-bound
certificate. -/
theorem resetPacket_signedSlopeResetCertificate
    {B K n : ℕ} (hB : 2 ≤ B) (hn : 0 < n) :
    SignedSlopeResetCertificate
      (resetPacketConfiguration B K n) (K / 2) where
  forces_block_count _blocks hpart :=
    Nat.div_le_of_le_mul (resetPacket_forces_linear_block_count hB hn hpart)

/-- Every finite upper bound on signed-convex partitions has a least
attained value, hence an exact turning complexity. -/
theorem exists_minimal_turningComplexity
    {P : OrderedConfiguration} {K : ℕ}
    (hupper : HasSignedConvexPartitionAtMost P K) :
    ∃ k ≤ K, HasTurningComplexity P k := by
  classical
  let hex : ∃ k : ℕ, HasSignedConvexPartitionAtMost P k := ⟨K, hupper⟩
  let k := Nat.find hex
  refine ⟨k, Nat.find_min' hex hupper, Nat.find_spec hex, ?_⟩
  intro j hj
  exact Nat.find_min hex hj

/-- The reset packet has an exact turning complexity between `K/2` and
`K`; in particular its turning complexity is of order `K`. -/
theorem resetPacket_exists_turningComplexity_linear
    {B K n : ℕ} (hB : 2 ≤ B) (hn : 0 < n) :
    ∃ k : ℕ,
      HasTurningComplexity (resetPacketConfiguration B K n) k ∧
        K / 2 ≤ k ∧ K ≤ 2 * k ∧ k ≤ K := by
  have hnH : n ≤ 3 * n := by omega
  have hupper : HasSignedConvexPartitionAtMost
      (resetPacketConfiguration B K n) K := by
    simpa [resetPacketConfiguration, canonicalPacketConfiguration] using
      (packetConfiguration_hasSignedConvexPartitionAtMost
        (H := 3 * n) (C := B ^ (n - 1) - 1) (B := B)
        (K := K) (n := n) hB hn hnH)
  rcases exists_minimal_turningComplexity hupper with ⟨k, hkK, hk⟩
  rcases hk.1 with ⟨blocks, hpart, hlength⟩
  have hreset := resetPacket_forces_linear_block_count hB hn hpart
  have hKtwo : K ≤ 2 * k :=
    hreset.trans (Nat.mul_le_mul_left 2 hlength)
  exact ⟨k, hk, Nat.div_le_of_le_mul hKtwo, hKtwo, hkK⟩

/-- One-stop sharpness data for the reset packet: cardinality `Kn`, an exact
turning complexity comparable with `K`, and the two explicit `J₃` bounds. -/
theorem resetPacketConfiguration_sharpness_data
    {B K n : ℕ} (hB : 4 ≤ B) (hn : 0 < n) :
    (pointSet (resetPacketConfiguration B K n)).card = K * n ∧
      (∃ k : ℕ,
        HasTurningComplexity (resetPacketConfiguration B K n) k ∧
          K / 2 ≤ k ∧ K ≤ 2 * k ∧ k ≤ K) ∧
      K ^ 2 * (K * n) ^ 3 ≤
        3125 * J3 (pointSet (resetPacketConfiguration B K n)) ∧
      J3 (pointSet (resetPacketConfiguration B K n)) ≤
        6 * (K ^ 2 * (K * n) ^ 3) := by
  have hcanonical := canonicalPacketConfiguration_properties
    (C := B ^ (n - 1) - 1) (B := B) (K := K) (n := n) hB hn
  rcases hcanonical with ⟨hcard, _hpartition, hlower, hupper⟩
  refine ⟨?_, resetPacket_exists_turningComplexity_linear (by omega) hn,
    ?_, ?_⟩
  · simpa [resetPacketConfiguration] using hcard
  · simpa [resetPacketConfiguration] using hlower
  · simpa [resetPacketConfiguration] using hupper

theorem not_hasSignedConvexPartitionAtMost_of_resetCertificate
    {P : OrderedConfiguration} {L k : ℕ}
    (cert : SignedSlopeResetCertificate P L) (hkL : k < L) :
    ¬ HasSignedConvexPartitionAtMost P k := by
  rintro ⟨blocks, hblocks, hlen⟩
  exact (not_le_of_gt hkL) ((cert.forces_block_count blocks hblocks).trans hlen)

/-- Matching upper and strict-reset lower certificates identify the turning
complexity exactly. -/
theorem hasTurningComplexity_of_upper_and_resetCertificate
    {P : OrderedConfiguration} {K : ℕ}
    (hupper : HasSignedConvexPartitionAtMost P K)
    (cert : SignedSlopeResetCertificate P K) :
    HasTurningComplexity P K := by
  refine ⟨hupper, ?_⟩
  intro k hk
  exact not_hasSignedConvexPartitionAtMost_of_resetCertificate cert hk

/-- A stronger block-count certificate can identify the exact complexity of
any packet configuration, supplementing the explicit factor-two result for
the canonical reset packet. -/
theorem packetConfiguration_hasTurningComplexity_of_resetCertificate
    {H C B K n : ℕ} (hB : 2 ≤ B) (hn : 0 < n) (hnH : n ≤ H)
    (cert : SignedSlopeResetCertificate
      (packetConfiguration H C B K n hnH) K) :
    HasTurningComplexity (packetConfiguration H C B K n hnH) K :=
  hasTurningComplexity_of_upper_and_resetCertificate
    (packetConfiguration_hasSignedConvexPartitionAtMost hB hn hnH) cert

/-- Any weaker reset certificate still gives the advertised linear lower
bound for whichever exact turning complexity is later established. -/
theorem resetCertificate_lower_bound
    {P : OrderedConfiguration} {L k : ℕ}
    (cert : SignedSlopeResetCertificate P L)
    (hk : HasTurningComplexity P k) :
    L ≤ k := by
  rcases hk.1 with ⟨blocks, hblocks, hlen⟩
  exact (cert.forces_block_count blocks hblocks).trans hlen

end Turning
end ComplexitySensitiveEnergy
