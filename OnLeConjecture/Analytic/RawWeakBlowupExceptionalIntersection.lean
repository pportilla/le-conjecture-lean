/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RawWeakBlowupExceptionalAxes
public import OnLeConjecture.Analytic.RawWeakBlowupSiblingSeparation

/-!
# Intersection recurrences on the exceptional axes of a weak-blowup tree

An exact-order linear combination has finite intersection with every
recorded exceptional axis. The actual transform identities give its
intersection order after following that axis through another blowup.
The finite path formula retains the final intersection order, so it
does not require an unproved assertion about termination on the axis.
-/

public section

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ
open scoped BigOperators

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

/-- Intersection order with the newest exceptional axis `y = 0`.
Its restriction is nonzero at a nonroot vertex for an exact-order member. -/
@[expose] noncomputable def newestAxisOrder
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ) (p : T.Vertex) : ℕ :=
  (vanishingOrder (lineRestriction (firstCoordinateVector 1)
    (germLinearCombination (T.generators p) q))).toNat

/-- Intersection order with the coordinate axis `x = 0`.
This axis is an older exceptional divisor when `xAncestor` is present. -/
@[expose] noncomputable def oldAxisOrder
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ) (p : T.Vertex) : ℕ :=
  (vanishingOrder (hyperplaneRestriction 1
    (germLinearCombination (T.generators p) q))).toNat

theorem multiplicity_le_oldAxisOrder
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    {p a : T.Vertex} (haxis : T.rootedChartData.xAncestor p = some a) :
    T.multiplicity p ≤ T.oldAxisOrder q p := by
  have hmem := (hyperplaneInclusionGerm 1).pullback_mem_maximalIdeal_pow
    (germLinearCombination_mem _ _ (T.generator_mem p) q)
  change hyperplaneRestriction 1 (germLinearCombination (T.generators p) q) ∈
    maximalIdeal 1 ^ T.multiplicity p at hmem
  have horder := mem_maximalIdeal_one_pow_iff.mp hmem
  have hfinite := vanishingOrder_eq_top_iff.not.mpr
    (T.member_oldAxisRestriction_ne_zero q hq haxis)
  simpa only [ENat.toNat_natCast, oldAxisOrder] using ENat.toNat_le_toNat horder hfinite

theorem multiplicity_le_newestAxisOrder
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (p : T.Vertex) (hp : p ≠ T.root) :
    T.multiplicity p ≤ T.newestAxisOrder q p := by
  have hmem := (lineGerm (firstCoordinateVector 1)).pullback_mem_maximalIdeal_pow
    (germLinearCombination_mem _ _ (T.generator_mem p) q)
  change lineRestriction (firstCoordinateVector 1) (germLinearCombination (T.generators p) q) ∈
    maximalIdeal 1 ^ T.multiplicity p at hmem
  have horder := mem_maximalIdeal_one_pow_iff.mp hmem
  have hfinite := vanishingOrder_eq_top_iff.not.mpr
    (T.member_firstAxisRestriction_ne_zero q hq p hp)
  simpa only [ENat.toNat_natCast, newestAxisOrder] using ENat.toNat_le_toNat horder hfinite

/-- Following an older exceptional divisor in the zero-centered chart
subtracts exactly the parent's multiplicity from its intersection order. -/
theorem oldAxisOrder_zero_chart
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    {p a : T.Vertex} (haxis : T.rootedChartData.xAncestor p = some a)
    (hchart : T.chartPoint p = some 0) :
    T.oldAxisOrder q (T.predecessor p) =
      T.multiplicity (T.predecessor p) + T.oldAxisOrder q p := by
  have hp := (T.rootedChartData.xAncestor_predecessor_cases haxis).1
  have hne := T.member_oldAxisRestriction_ne_zero q hq haxis
  unfold oldAxisOrder
  rw [T.member_zero_chart_axis_identity q p hp hchart, vanishingOrder_mul,
    vanishingOrder_coordinate_pow,
    ENat.toNat_add (ENat.natCast_ne_top _) (vanishingOrder_eq_top_iff.not.mpr hne),
    ENat.toNat_natCast]

/-- Following the newest exceptional divisor uses the complementary
chart, where that divisor becomes the older axis. -/
theorem newestAxisOrder_complementary_chart
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (p : T.Vertex) (hp : p ≠ T.root)
    (hparent : T.predecessor p ≠ T.root) (hchart : T.chartPoint p = none) :
    T.newestAxisOrder q (T.predecessor p) =
      T.multiplicity (T.predecessor p) + T.oldAxisOrder q p := by
  have haxis : T.rootedChartData.xAncestor p =
      some (T.predecessor (T.predecessor p)) := by
    rw [T.rootedChartData.xAncestor_complementary p hp hchart]
    change (if T.predecessor p = T.root then none
      else some (T.predecessor (T.predecessor p))) = _
    rw [if_neg hparent]
  have hne := T.member_oldAxisRestriction_ne_zero q hq haxis
  unfold newestAxisOrder oldAxisOrder
  rw [T.member_complementary_chart_axis_identity q p hp hchart, vanishingOrder_mul,
    vanishingOrder_coordinate_pow,
    ENat.toNat_add (ENat.natCast_ne_top _) (vanishingOrder_eq_top_iff.not.mpr hne),
    ENat.toNat_natCast]

/-- The sum along a recorded zero-chart path equals the initial
intersection order minus the final intersection order. -/
theorem oldAxisOrder_path_eq_sum_add
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (L : ℕ) (path : ℕ → T.Vertex) (a : T.Vertex)
    (haxis : ∀ j ≤ L, T.rootedChartData.xAncestor (path j) = some a)
    (hparent : ∀ j < L, T.predecessor (path (j + 1)) = path j)
    (hchart : ∀ j < L, T.chartPoint (path (j + 1)) = some 0) :
    T.oldAxisOrder q (path 0) =
      (∑ j ∈ Finset.range L, T.multiplicity (path j)) + T.oldAxisOrder q (path L) := by
  induction L with
  | zero => simp
  | succ L ih =>
      have hinit := ih (fun j hj => haxis j (by omega))
        (fun j hj => hparent j (by omega)) (fun j hj => hchart j (by omega))
      have hstep := T.oldAxisOrder_zero_chart q hq (haxis (L + 1) (by omega))
        (hchart L (by omega))
      rw [hparent L (by omega)] at hstep
      rw [hinit, hstep, Finset.sum_range_succ, Nat.add_assoc]

/-- A finite path on an older exceptional divisor consumes at most its
initial intersection order, including the last recorded multiplicity. -/
theorem sum_path_multiplicities_le_oldAxisOrder
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (L : ℕ) (path : ℕ → T.Vertex) (a : T.Vertex)
    (haxis : ∀ j ≤ L, T.rootedChartData.xAncestor (path j) = some a)
    (hparent : ∀ j < L, T.predecessor (path (j + 1)) = path j)
    (hchart : ∀ j < L, T.chartPoint (path (j + 1)) = some 0) :
    (∑ j ∈ Finset.range (L + 1), T.multiplicity (path j)) ≤
      T.oldAxisOrder q (path 0) := by
  rw [T.oldAxisOrder_path_eq_sum_add q hq L path a haxis hparent hchart,
    Finset.sum_range_succ]
  exact Nat.add_le_add_left (T.multiplicity_le_oldAxisOrder q hq (haxis L le_rfl)) _

omit [Fintype ι] in
/-- A vertex on an older exceptional divisor follows either the
complementary point of the preceding newest divisor or the zero point
of the same older divisor. -/
theorem oldAxis_predecessor_chart_cases
    (T : RawProjectiveWeakBlowupTree F) {p a : T.Vertex}
    (haxis : T.rootedChartData.xAncestor p = some a) :
    (T.chartPoint p = none ∧ T.predecessor (T.predecessor p) = a) ∨
      (T.chartPoint p = some 0 ∧
        T.rootedChartData.xAncestor (T.predecessor p) = some a) := by
  obtain ⟨hp, hparent, _⟩ := T.rootedChartData.xAncestor_predecessor_cases haxis
  cases hc : T.chartPoint p with
  | none =>
      left
      rw [T.rootedChartData.xAncestor_complementary p hp hc, if_neg hparent] at haxis
      exact ⟨rfl, Option.some.inj haxis⟩
  | some ζ =>
      by_cases hζ : ζ = 0
      · subst ζ
        right
        rw [T.rootedChartData.xAncestor_zero p hp hc] at haxis
        exact ⟨rfl, haxis⟩
      · rw [T.rootedChartData.xAncestor_nonzero p hp ζ hζ hc] at haxis
        cases haxis

omit [Fintype ι] in
/-- Each exceptional divisor has at most one continuing child at a
specified recorded center. Both projective chart possibilities are included. -/
theorem predecessor_injective_on_oldAxis
    (T : RawProjectiveWeakBlowupTree F) (a : T.Vertex) :
    Set.InjOn T.predecessor {p | T.rootedChartData.xAncestor p = some a} := by
  intro p hp r hr hpred
  have hpne := (T.rootedChartData.xAncestor_predecessor_cases hp).1
  have hrne := (T.rootedChartData.xAncestor_predecessor_cases hr).1
  apply T.eq_of_predecessor_eq_chartPoint_eq p r hpne hrne hpred
  rcases T.oldAxis_predecessor_chart_cases hp with ⟨hpc, hpa⟩ | ⟨hpc, hpa⟩
  · rcases T.oldAxis_predecessor_chart_cases hr with ⟨hrc, _⟩ | ⟨hrc, hra⟩
    · exact hpc.trans hrc.symm
    · have hne := T.rootedChartData.xAncestor_ne_predecessor hra
      exact False.elim (hne (by rw [← hpred]; exact hpa.symm))
  · rcases T.oldAxis_predecessor_chart_cases hr with ⟨hrc, hra⟩ | ⟨hrc, _⟩
    · have hne := T.rootedChartData.xAncestor_ne_predecessor hpa
      exact False.elim (hne (by rw [hpred]; exact hra.symm))
    · exact hpc.trans hrc.symm

/-- All multiplicities at points proximate to a fixed center are bounded
by the intersection orders on its newly created exceptional divisor.
The sum includes later satellite points. The proof cancels the
intersection orders along the finite tree. -/
theorem sum_proximate_multiplicities_le_child_newestAxisOrders
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (a : T.Vertex) :
    (∑ p ∈ Finset.univ.filter (fun p => a ∈ T.rootedChartData.parents p),
      T.multiplicity p) ≤ ∑ p ∈ T.childFinset a, T.newestAxisOrder q p := by
  classical
  let S := Finset.univ.filter fun p => T.rootedChartData.xAncestor p = some a
  let D := T.childFinset a
  let B : T.Vertex → ℕ := fun p => if p ∈ S then T.oldAxisOrder q p
    else T.newestAxisOrder q p
  have hS (p : T.Vertex) : p ∈ S ↔ T.rootedChartData.xAncestor p = some a := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hD (p : T.Vertex) : p ∈ D ↔ p ≠ T.root ∧ T.predecessor p = a :=
    T.mem_childFinset a p
  have hdisjoint : Disjoint S D := by
    apply Finset.disjoint_left.mpr
    intro p hp hd
    exact T.rootedChartData.xAncestor_ne_predecessor ((hS p).mp hp) ((hD p).mp hd).2.symm
  have hset : Finset.univ.filter (fun p => a ∈ T.rootedChartData.parents p) = S ∪ D := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hS, hD,
      T.rootedChartData.mem_parents_iff]
    constructor
    · rintro ⟨hp, h | h⟩
      · exact Or.inr ⟨hp, h.symm⟩
      · exact Or.inl h
    · rintro (h | ⟨hp, h⟩)
      · exact ⟨(T.rootedChartData.xAncestor_predecessor_cases h).1, Or.inr h⟩
      · exact ⟨hp, Or.inl h.symm⟩
  have hBge (p : T.Vertex) (hp : p ∈ S ∪ D) : T.multiplicity p ≤ B p := by
    by_cases hs : p ∈ S
    · simpa only [B, if_pos hs] using T.multiplicity_le_oldAxisOrder q hq ((hS p).mp hs)
    · have hd : p ∈ D := (Finset.mem_union.mp hp).resolve_left hs
      simpa only [B, if_neg hs] using
        T.multiplicity_le_newestAxisOrder q hq p ((hD p).mp hd).1
  have hpred (p : T.Vertex) (hp : p ∈ S) : T.predecessor p ∈ S ∪ D := by
    have haxis := (hS p).mp hp
    obtain ⟨_, hparent, _⟩ := T.rootedChartData.xAncestor_predecessor_cases haxis
    rcases T.oldAxis_predecessor_chart_cases haxis with ⟨_, ha⟩ | ⟨_, ha⟩
    · exact Finset.mem_union_right _ ((hD _).mpr ⟨hparent, ha⟩)
    · exact Finset.mem_union_left _ ((hS _).mpr ha)
  have hstep (p : T.Vertex) (hp : p ∈ S) :
      B (T.predecessor p) = T.multiplicity (T.predecessor p) + T.oldAxisOrder q p := by
    have haxis := (hS p).mp hp
    obtain ⟨hpne, hparent, _⟩ := T.rootedChartData.xAncestor_predecessor_cases haxis
    rcases T.oldAxis_predecessor_chart_cases haxis with ⟨hc, ha⟩ | ⟨hc, ha⟩
    · have hnot : T.predecessor p ∉ S := by
        intro hs
        exact T.rootedChartData.xAncestor_ne_predecessor ((hS _).mp hs) ha.symm
      simpa only [B, if_neg hnot] using
        T.newestAxisOrder_complementary_chart q hq p hpne hparent hc
    · simpa only [B, if_pos ((hS _).mpr ha)] using T.oldAxisOrder_zero_chart q hq haxis hc
  have hsum : (∑ p ∈ S, T.oldAxisOrder q p) ≤
      ∑ p ∈ S ∪ D, (B p - T.multiplicity p) := by
    calc
      (∑ p ∈ S, T.oldAxisOrder q p) =
          ∑ p ∈ S.image T.predecessor, (B p - T.multiplicity p) := by
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro p hp
          rw [hstep p hp, Nat.add_sub_cancel_left]
        · intro p hp r hr hpr
          exact T.predecessor_injective_on_oldAxis a ((hS p).mp hp) ((hS r).mp hr) hpr
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (by rintro p hp; obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp; exact hpred r hr)
        (by intros; omega)
  have hsumB : (∑ p ∈ S ∪ D, B p) =
      (∑ p ∈ S, T.oldAxisOrder q p) + ∑ p ∈ D, T.newestAxisOrder q p := by
    rw [Finset.sum_union hdisjoint]
    congr 1
    · exact Finset.sum_congr rfl (fun p hp => by simp only [B, if_pos hp])
    · apply Finset.sum_congr rfl
      intro p hp
      have hs : p ∉ S := fun hs => Finset.disjoint_left.mp hdisjoint hs hp
      simp only [B, if_neg hs]
  have hsplit : (∑ p ∈ S ∪ D, B p) = (∑ p ∈ S ∪ D, T.multiplicity p) +
      ∑ p ∈ S ∪ D, (B p - T.multiplicity p) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p hp => (Nat.add_sub_of_le (hBge p hp)).symm)
  rw [hset]
  change (∑ p ∈ S ∪ D, T.multiplicity p) ≤ ∑ p ∈ D, T.newestAxisOrder q p
  omega

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
