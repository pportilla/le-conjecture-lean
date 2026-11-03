/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRectilinearRounding
public import OnLeConjecture.KnotTheory.PositiveBraidGridRectilinearWord

/-! # Slab bounds for smooth relative rounding

If the rounding is supported in the middle parameter interval and has error
less than one eighth, the moving strands remain in their original horizontal
slab and reach its boundary only at their source endpoints. This supplies the
geometric separation needed when the rounded letters are joined into a word.
-/

@[expose] public noncomputable section

open Set
open scoped Topology ContDiff

namespace OnLeConjecture.KnotTheory

private theorem lower_horizontal_middle {q : ℝ} (hq : q ∈ Icc (1 / 8 : ℝ) (7 / 8)) :
    2 * q - positiveGridRectilinearLowerRise q ∈ Icc (1 / 4 : ℝ) (3 / 4) := by
  by_cases h₀ : q ≤ 1 / 6
  · rw [positiveGridRectilinearLowerRise_first h₀]
    constructor <;> linarith [hq.1]
  by_cases h₁ : q ≤ 5 / 12
  · rw [positiveGridRectilinearLowerRise_second ⟨by linarith, h₁⟩]
    constructor <;> linarith
  by_cases h₂ : q ≤ 7 / 12
  · rw [positiveGridRectilinearLowerRise_third ⟨by linarith, h₂⟩]
    constructor <;> linarith
  by_cases h₃ : q ≤ 5 / 6
  · rw [positiveGridRectilinearLowerRise_fourth ⟨by linarith, h₃⟩]
    constructor <;> linarith
  · rw [positiveGridRectilinearLowerRise_fifth (by linarith)]
    constructor <;> linarith [hq.2]

private theorem upper_horizontal_middle {q : ℝ} (hq : q ∈ Icc (1 / 8 : ℝ) (7 / 8)) :
    2 * q - positiveGridRectilinearUpperDrop q ∈ Icc (1 / 4 : ℝ) (3 / 4) := by
  by_cases h₀ : q ≤ 1 / 4
  · rw [positiveGridRectilinearUpperDrop_first h₀]
    constructor <;> linarith [hq.1]
  by_cases h₁ : q ≤ 3 / 4
  · rw [positiveGridRectilinearUpperDrop_second ⟨by linarith, h₁⟩]
    constructor <;> linarith
  · rw [positiveGridRectilinearUpperDrop_third (by linarith)]
    constructor <;> linarith [hq.2]

private theorem progress_half_unit {t : ℝ} (ht : t ∈ Icc 0 1) :
    positiveGridRoundingProgress t / 2 ∈ Icc 0 1 ∧
      (positiveGridRoundingProgress t / 2 = 0 ↔ t = 0) ∧
      (positiveGridRoundingProgress t / 2 = 1 ↔ t = 1) := by
  have h₀ : positiveGridRoundingProgress 0 = 0 := by simp [positiveGridRoundingProgress]
  have h₁ : positiveGridRoundingProgress 1 = 2 := by norm_num [positiveGridRoundingProgress]
  have hlo := positiveGridRoundingProgress_strictMono.monotone ht.1
  have hhi := positiveGridRoundingProgress_strictMono.monotone ht.2
  rw [h₀] at hlo
  rw [h₁] at hhi
  refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
  · constructor
    · intro h
      apply positiveGridRoundingProgress_strictMono.injective
      rw [h₀]
      linarith
    · rintro rfl
      rw [h₀]
      norm_num
  · constructor
    · intro h
      apply positiveGridRoundingProgress_strictMono.injective
      rw [h₁]
      linarith
    · rintro rfl
      rw [h₁]
      norm_num

private theorem smoothed_horizontal_slab {f R : ℝ → ℝ} {U : Set ℝ}
    (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (heq : EqOn f R Uᶜ) (happrox : ∀ q, dist (f q) (R q) < 1 / 8)
    (hslab : ∀ q ∈ Icc (0 : ℝ) 1, 2 * q - R q ∈ Icc 0 1 ∧
      (2 * q - R q = 0 ↔ q = 0) ∧ (2 * q - R q = 1 ↔ q = 1))
    (hmid : ∀ q ∈ Icc (1 / 8 : ℝ) (7 / 8),
      2 * q - R q ∈ Icc (1 / 4 : ℝ) (3 / 4))
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    positiveGridRoundingProgress t - f (positiveGridRoundingProgress t / 2) ∈ Icc 0 1 ∧
      (positiveGridRoundingProgress t - f (positiveGridRoundingProgress t / 2) = 0 ↔ t = 0) ∧
      (positiveGridRoundingProgress t - f (positiveGridRoundingProgress t / 2) = 1 ↔ t = 1) := by
  have hq := progress_half_unit ht
  by_cases hmem : positiveGridRoundingProgress t / 2 ∈ U
  · have hb := hU hmem
    have hx := hmid _ ⟨hb.1.le, hb.2.le⟩
    have hd := abs_lt.mp (show |f (positiveGridRoundingProgress t / 2) -
        R (positiveGridRoundingProgress t / 2)| < 1 / 8 by
      simpa only [Real.dist_eq] using happrox (positiveGridRoundingProgress t / 2))
    have hpos : 0 < positiveGridRoundingProgress t - f (positiveGridRoundingProgress t / 2) :=
      by linarith [hx.1, hd.2]
    have hlt : positiveGridRoundingProgress t - f (positiveGridRoundingProgress t / 2) < 1 :=
      by linarith [hx.2, hd.1]
    have ht₀ : t ≠ 0 := by intro h; have := hq.2.1.mpr h; linarith [hb.1]
    have ht₁ : t ≠ 1 := by intro h; have := hq.2.2.mpr h; linarith [hb.2]
    exact ⟨⟨hpos.le, hlt.le⟩, iff_of_false (ne_of_gt hpos) ht₀,
      iff_of_false (ne_of_lt hlt) ht₁⟩
  · rw [heq hmem]
    have he : 2 * (positiveGridRoundingProgress t / 2) = positiveGridRoundingProgress t := by ring
    have hb := hslab _ hq.1
    rw [he] at hb
    exact ⟨hb.1, hb.2.1.trans hq.2.1, hb.2.2.trans hq.2.2⟩

/-- The rounded terminal moving strands stay inside the letter slab with the exact
boundary parameter characterization. -/
theorem positiveGridRoundedDeformation_one_slab {m : ℕ} (i : Fin (m - 1))
    {l u : ℝ → ℝ} {U : Set ℝ} (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hle : EqOn l positiveGridRectilinearLowerRise Uᶜ)
    (hue : EqOn u positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ q, dist (l q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ q, dist (u q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (k : Fin m) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (positiveGridRoundedDeformation i l u k 1 t).1 ∈ Icc 0 1 ∧
      ((positiveGridRoundedDeformation i l u k 1 t).1 = 0 ↔ t = 0) ∧
      ((positiveGridRoundedDeformation i l u k 1 t).1 = 1 ↔ t = 1) := by
  by_cases hk₀ : k = adjacentLower i
  · subst k
    simp only [positiveGridRoundedDeformation, ite_true, positiveGridRoundingRise,
      sub_self, zero_mul, one_mul, zero_add]
    apply smoothed_horizontal_slab hU hle hla _ (fun _ => lower_horizontal_middle) ht
    intro q hq
    simpa [positiveGridRectilinear, positiveGridRectilinearHorizontal] using
      positiveRectilinearWord_local_slab i (adjacentLower i) hq
  by_cases hk₁ : k = adjacentUpper i
  · subst k
    simp only [positiveGridRoundedDeformation, if_neg hk₀, ite_true, positiveGridRoundingRise,
      sub_self, zero_mul, one_mul, zero_add]
    apply smoothed_horizontal_slab hU hue hua _ (fun _ => upper_horizontal_middle) ht
    intro q hq
    simpa [positiveGridRectilinear, positiveGridRectilinearHorizontal, hk₀] using
      positiveRectilinearWord_local_slab i (adjacentUpper i) hq
  · rw [positiveGridRoundedDeformation_fixed i l u k hk₀ hk₁]
    exact ⟨ht, Iff.rfl, Iff.rfl⟩

private theorem rounding_convex_unit_slab {s t x : ℝ} (hs : s ∈ Icc 0 1)
    (ht : t ∈ Icc 0 1) (hx : x ∈ Icc 0 1) (hx₀ : x = 0 ↔ t = 0)
    (hx₁ : x = 1 ↔ t = 1) :
    (1 - s) * t + s * x ∈ Icc 0 1 ∧
      ((1 - s) * t + s * x = 0 ↔ t = 0) ∧
      ((1 - s) * t + s * x = 1 ↔ t = 1) := by
  have hst : 0 ≤ (1 - s) * t := mul_nonneg (by linarith [hs.2]) ht.1
  have hsx : 0 ≤ s * x := mul_nonneg hs.1 hx.1
  have hsT : 0 ≤ (1 - s) * (1 - t) := mul_nonneg (by linarith [hs.2]) (by linarith [ht.2])
  have hsX : 0 ≤ s * (1 - x) := mul_nonneg hs.1 (by linarith [hx.2])
  refine ⟨⟨by linarith, by nlinarith⟩, ?_, ?_⟩
  · constructor
    · intro h
      by_cases he : s = 1
      · simp only [he, sub_self, zero_mul, one_mul, zero_add] at h
        exact hx₀.mp h
      · have hp : 0 < 1 - s := sub_pos.mpr (lt_of_le_of_ne hs.2 he)
        have hz : (1 - s) * t = 0 := by linarith
        exact (mul_eq_zero.mp hz).resolve_left hp.ne'
    · intro h
      rw [h, hx₀.mpr h]
      ring
  · constructor
    · intro h
      by_cases he : s = 1
      · simp only [he, sub_self, zero_mul, one_mul, zero_add] at h
        exact hx₁.mp h
      · have hp : 0 < 1 - s := sub_pos.mpr (lt_of_le_of_ne hs.2 he)
        have hz : (1 - s) * (1 - t) = 0 := by nlinarith
        have ht' := (mul_eq_zero.mp hz).resolve_left hp.ne'
        linarith
    · intro h
      rw [h, hx₁.mpr h]
      ring

/-- The horizontal coordinate of every slice is a convex interpolation between
the unchanged source parameter and the rounded terminal coordinate. -/
theorem positiveGridRoundedDeformation_fst_affine {m : ℕ} (i : Fin (m - 1))
    (l u : ℝ → ℝ) (k : Fin m) (s t : ℝ) :
    (positiveGridRoundedDeformation i l u k s t).1 =
      (1 - s) * t + s * (positiveGridRoundedDeformation i l u k 1 t).1 := by
  unfold positiveGridRoundedDeformation positiveGridRoundingRise positiveGridRoundingProgress
  split_ifs <;> simp only [sub_self, zero_mul, one_mul, zero_add] <;> ring

/-- All smooth deformation slices have the same exact unit-slab separation as the polygon. -/
theorem positiveGridRoundedDeformation_slab {m : ℕ} (i : Fin (m - 1))
    {l u : ℝ → ℝ} {U : Set ℝ} (hU : U ⊆ Ioo (1 / 8 : ℝ) (7 / 8))
    (hle : EqOn l positiveGridRectilinearLowerRise Uᶜ)
    (hue : EqOn u positiveGridRectilinearUpperDrop Uᶜ)
    (hla : ∀ q, dist (l q) (positiveGridRectilinearLowerRise q) < 1 / 8)
    (hua : ∀ q, dist (u q) (positiveGridRectilinearUpperDrop q) < 1 / 8)
    (k : Fin m) {s t : ℝ} (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    (positiveGridRoundedDeformation i l u k s t).1 ∈ Icc 0 1 ∧
      ((positiveGridRoundedDeformation i l u k s t).1 = 0 ↔ t = 0) ∧
      ((positiveGridRoundedDeformation i l u k s t).1 = 1 ↔ t = 1) := by
  have h := positiveGridRoundedDeformation_one_slab i hU hle hue hla hua k ht
  rw [positiveGridRoundedDeformation_fst_affine]
  exact rounding_convex_unit_slab hs ht h.1 h.2.1 h.2.2

/-- An open union of small intervals centered at the six actual corners. -/
def positiveGridRoundingCornerNeighborhood (δ : ℝ) : Set ℝ :=
  {t | ∃ c ∈ positiveGridRectilinearCornerTimes, |t - c| < δ}

theorem positiveGridRoundingCornerNeighborhood_isOpen (δ : ℝ) :
    IsOpen (positiveGridRoundingCornerNeighborhood δ) := by
  have he : positiveGridRoundingCornerNeighborhood δ =
      ⋃ c ∈ positiveGridRectilinearCornerTimes, {t : ℝ | |t - c| < δ} := by
    ext t
    simp [positiveGridRoundingCornerNeighborhood]
  rw [he]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
    isOpen_lt (continuous_id.sub continuous_const).abs continuous_const

theorem positiveGridRoundingCornerNeighborhood_contains {δ : ℝ} (hδ : 0 < δ) :
    positiveGridRectilinearCornerTimes ⊆ positiveGridRoundingCornerNeighborhood δ := by
  intro t ht
  exact ⟨t, ht, by simpa using hδ⟩

/-- With radius at most one forty-eighth, all rounding intervals stay in the middle slab. -/
theorem positiveGridRoundingCornerNeighborhood_subset {δ : ℝ} (hδ : δ ≤ 1 / 48) :
    positiveGridRoundingCornerNeighborhood δ ⊆ Ioo (1 / 8 : ℝ) (7 / 8) := by
  rintro t ⟨c, hc, ht⟩
  have hc' : c ∈ Icc (1 / 6 : ℝ) (5 / 6) := by
    simp only [positiveGridRectilinearCornerTimes, mem_insert_iff, mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hh := abs_lt.mp ht
  constructor <;> linarith [hh.1, hh.2, hc'.1, hc'.2]

/-- In particular the crossing parameter itself is outside all the rounding intervals. -/
theorem half_notMem_positiveGridRoundingCornerNeighborhood {δ : ℝ} (hδ : δ ≤ 1 / 48) :
    (1 / 2 : ℝ) ∉ positiveGridRoundingCornerNeighborhood δ := by
  rintro ⟨c, hc, ht⟩
  simp only [positiveGridRectilinearCornerTimes, mem_insert_iff, mem_singleton_iff] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at ht <;> linarith

/-- A regular rounding inside arbitrarily small prescribed corner intervals, with exact
unit-slab bounds. All geometric separation and regularity conclusions are derived. -/
theorem exists_positiveGridRectilinear_rounding_in_slabs {m : ℕ} (i : Fin (m - 1))
    {δ ε : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 48) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) :
    ∃ l u : ℝ → ℝ, ContDiff ℝ ∞ l ∧ ContDiff ℝ ∞ u ∧
      (∀ q, dist (l q) (positiveGridRectilinearLowerRise q) < ε) ∧
      (∀ q, dist (u q) (positiveGridRectilinearUpperDrop q) < ε) ∧
      EqOn l positiveGridRectilinearLowerRise (positiveGridRoundingCornerNeighborhood δ)ᶜ ∧
      EqOn u positiveGridRectilinearUpperDrop (positiveGridRoundingCornerNeighborhood δ)ᶜ ∧
      (∀ k, ContDiff ℝ ∞ (fun st : ℝ × ℝ =>
        positiveGridRoundedDeformation i l u k st.1 st.2)) ∧
      (∀ s, Function.Injective (fun p : Fin m × ℝ =>
        positiveGridRoundedDeformation i l u p.1 s p.2)) ∧
      (∀ k s t, deriv (positiveGridRoundedDeformation i l u k s) t ≠ 0) ∧
      (∀ k s t, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
        (positiveGridRoundedDeformation i l u k s t).1 ∈ Icc 0 1 ∧
        ((positiveGridRoundedDeformation i l u k s t).1 = 0 ↔ t = 0) ∧
        ((positiveGridRoundedDeformation i l u k s t).1 = 1 ↔ t = 1)) := by
  obtain ⟨l, u, hl, hu, hla, hua, hle, hue⟩ :=
    exists_positiveGridRectilinear_smooth_rises hε
      (positiveGridRoundingCornerNeighborhood_isOpen δ)
      (positiveGridRoundingCornerNeighborhood_contains hδ)
  refine ⟨l, u, hl, hu, hla, hua, hle, hue,
    positiveGridRoundedDeformation_contDiff i hl hu,
    positiveGridRoundedDeformation_injective i l u,
    positiveGridRoundedDeformation_deriv_ne_zero i hl hu, ?_⟩
  exact fun k _ _ hs ht => positiveGridRoundedDeformation_slab i
    (positiveGridRoundingCornerNeighborhood_subset hδ') hle hue
    (fun q => (hla q).trans_le hε') (fun q => (hua q).trans_le hε') k hs ht

end OnLeConjecture.KnotTheory
