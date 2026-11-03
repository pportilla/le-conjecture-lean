/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RawWeakBlowupCornerAvoidance

/-!
# Exact exceptional intersection accounting for proximity

Avoidance of unrecorded exceptional-axis continuations makes the finite
intersection recurrence exact after summation. The initial intersection
on an exceptional divisor is the sum of the multiplicities of all points
proximate to its center, including satellite points.
-/

public section

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ
open scoped BigOperators

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

/-- With exact terminal axis orders, all the exceptional intersection
is consumed by the recorded proximate points. -/
theorem sum_proximate_multiplicities_eq_child_newestAxisOrders
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (hend : ∀ p : T.Vertex,
      (some 0 ∉ (T.childFinset p).image T.chartPoint →
        T.oldAxisOrder q p = T.multiplicity p) ∧
      (none ∉ (T.childFinset p).image T.chartPoint →
        T.newestAxisOrder q p = T.multiplicity p))
    (a : T.Vertex) :
    (∑ p ∈ Finset.univ.filter (fun p => a ∈ T.rootedChartData.parents p),
      T.multiplicity p) = ∑ p ∈ T.childFinset a, T.newestAxisOrder q p := by
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
  have hpredset : S.image T.predecessor ⊆ S ∪ D := by
    rintro p hp
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
    exact hpred r hr
  have hterminal (p : T.Vertex) (hp : p ∈ S ∪ D)
      (hmissing : p ∉ S.image T.predecessor) : B p - T.multiplicity p = 0 := by
    by_cases hs : p ∈ S
    · have hnozero : some 0 ∉ (T.childFinset p).image T.chartPoint := by
        intro hz
        obtain ⟨r, hr, hchart⟩ := Finset.mem_image.mp hz
        obtain ⟨hrne, hrpred⟩ := (T.mem_childFinset p r).mp hr
        have haxis : T.rootedChartData.xAncestor r = some a := by
          rw [T.rootedChartData.xAncestor_zero r hrne hchart]
          change T.rootedChartData.xAncestor (T.predecessor r) = some a
          rw [hrpred]
          exact (hS p).mp hs
        exact hmissing (Finset.mem_image.mpr ⟨r, (hS r).mpr haxis, hrpred⟩)
      simp only [B, if_pos hs, (hend p).1 hnozero, Nat.sub_self]
    · have hd := (hD p).mp ((Finset.mem_union.mp hp).resolve_left hs)
      have hnonone : none ∉ (T.childFinset p).image T.chartPoint := by
        intro hz
        obtain ⟨r, hr, hchart⟩ := Finset.mem_image.mp hz
        obtain ⟨hrne, hrpred⟩ := (T.mem_childFinset p r).mp hr
        have haxis : T.rootedChartData.xAncestor r = some a := by
          rw [T.rootedChartData.xAncestor_complementary r hrne hchart]
          change (if T.predecessor r = T.root then none
            else some (T.predecessor (T.predecessor r))) = some a
          rw [hrpred, if_neg hd.1, hd.2]
        exact hmissing (Finset.mem_image.mpr ⟨r, (hS r).mpr haxis, hrpred⟩)
      simp only [B, if_neg hs, (hend p).2 hnonone, Nat.sub_self]
  have hsum : (∑ p ∈ S, T.oldAxisOrder q p) =
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
      _ = _ := Finset.sum_subset hpredset hterminal
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
  change (∑ p ∈ S ∪ D, T.multiplicity p) = ∑ p ∈ D, T.newestAxisOrder q p
  omega

/-- Exact exceptional intersection accounting holds for every member
of a constructed nonempty open subset of any prescribed nonempty open
coefficient set. -/
theorem exists_open_exact_proximity_intersections
    (T : RawProjectiveWeakBlowupTree F)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V,
        (∀ p, germLinearCombination (T.generators p) q ∉
          maximalIdeal 2 ^ (T.multiplicity p + 1)) ∧
        ∀ a : T.Vertex,
          (∑ p ∈ Finset.univ.filter (fun p => a ∈ T.rootedChartData.parents p),
            T.multiplicity p) = ∑ p ∈ T.childFinset a, T.newestAxisOrder q p := by
  obtain ⟨W, hWopen, hWne, hWU, hW⟩ := T.exists_open_member_singular_complete U hU hUne
  obtain ⟨V, hVopen, hVne, hVW, hV⟩ := T.exists_open_exact_axis_endpoints W hWopen hWne
  refine ⟨V, hVopen, hVne, hVW.trans hWU, fun q hq => ?_⟩
  have hqexact := (hW q (hVW hq)).1
  exact ⟨hqexact, T.sum_proximate_multiplicities_eq_child_newestAxisOrders q hqexact (hV q hq)⟩

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
