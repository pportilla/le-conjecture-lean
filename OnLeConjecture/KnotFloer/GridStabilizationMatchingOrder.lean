/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationFullMatching

/-!
# Decrease along full noncritical matching paths

A full rectangle between noncritical matching pairs either has positive O count or
strictly lowers the outer-square level, unless it is the matching rectangle itself.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti Finsupp
variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

private theorem transpose_eq_of_no_corner {x y : GridState (n + 1)}
    (r : GridRectangleBetween x y) (q : Fin (n + 1))
    (hb : r.bottom ≠ q) (ht : r.top ≠ q) : y.transpose q = x.transpose q := by
  have hv := x.apply_transpose_apply q
  have hl : x.transpose q ≠ r.left := fun h => hb ((congrArg x h).symm.trans hv)
  have hr : x.transpose q ≠ r.right := fun h => ht ((congrArg x h).symm.trans hv)
  have h := (r.map_of_ne _ hl hr).trans hv
  exact (congrArg y.transpose h.symm).trans (y.transpose_apply_apply _)

/-- An O-free full edge between noncritical matching pairs lowers the outer level,
unless it is the designated matching edge. -/
theorem stabilization_level_lt_or_matching_of_OColumns_empty
    {x y : GridState (n + 1)} (r : GridRectangleBetween x y)
    (hx : RowMatchingSource s (G.X s) x) (hy : ¬RowMatchingSource s (G.X s) y)
    (hxc : x s.succ ≠ (G.X s).castSucc) (hyc : y s.succ ≠ (G.X s).succ)
    (hO : (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle = ∅) :
    G.stabilizeXLevel s y < G.stabilizeXLevel s x ∨
      y = x.swapRows (G.X s).castSucc (G.X s).succ := by
  classical
  have hdisj : Disjoint r.toGridRectangle.coveredSquares
      (G.stabilizeX s.castSucc (G.X s).castSucc s).OSet := by
    apply Finset.disjoint_left.mpr
    rintro ⟨c, q⟩ hc hq
    rw [GridDiagram.mem_OSet] at hq
    have hm : c ∈ (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle := by
      rw [GridDiagram.mem_OColumns, hq]
      exact hc
    rw [hO] at hm
    exact Finset.notMem_empty _ hm
  rcases G.stabilizeXLevel_lt_or_disjoint s r hdisj with hlt | hout
  · exact Or.inl hlt
  rcases G.coveredRows_eq_or_coveredColumns_eq_of_disjoint_stabilizeXOuterSquares s r hout
    with hrows | hcols
  · obtain ⟨hb, ht, _⟩ := Grid.cIco_eq_singleton_iff.mp hrows
    simp only [GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top, finRotate_apply, Fin.coeSucc_eq_succ] at hb ht
    exact Or.inr (r.target_eq_swapRows.trans (by rw [← r.bottom_def, ← r.top_def, hb, ht]))
  · obtain ⟨hl, hr, _⟩ := Grid.cIco_eq_singleton_iff.mp hcols
    simp only [GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, finRotate_apply, Fin.coeSucc_eq_succ] at hl hr
    have hnot : (G.X s).castSucc ∉ Grid.cIco r.bottom r.top := by
      intro hrow
      have hmark : (s.castSucc, (G.X s).castSucc) ∈
          (G.stabilizeX s.castSucc (G.X s).castSucc s).OSet := by simp
      apply Finset.disjoint_left.mp hdisj _ hmark
      exact (GridRectangle.mem_coveredSquares _ _).mpr
        ⟨by rw [hcols]; exact Finset.mem_singleton_self _, hrow⟩
    have hb0 : r.bottom ≠ (G.X s).castSucc := by
      intro h
      exact hnot (h ▸ Grid.left_mem_cIco r.bottom_ne_top)
    have ht0 : r.top ≠ (G.X s).castSucc := by
      change x r.right ≠ _
      rw [hr]
      exact hxc
    have hb1 : r.bottom ≠ (G.X s).succ := by
      intro h
      apply hyc
      rw [← hr, r.map_right]
      exact h
    have ht1 : r.top ≠ (G.X s).succ := by
      intro h
      apply hnot
      rw [h]
      exact Grid.castSucc_mem_cIco_succ hb1
    have hs : RowMatchingSource s (G.X s) y := by
      simpa only [RowMatchingSource, transpose_eq_of_no_corner r (G.X s).castSucc hb0 ht0,
        transpose_eq_of_no_corner r (G.X s).succ hb1 ht1] using hx
    exact False.elim (hy hs)

/-- Swapping the two adjacent matching rows exchanges source and nonsource status. -/
theorem rowMatchingSource_swapRows (x : GridState (n + 1)) :
    RowMatchingSource s (G.X s) (x.swapRows (G.X s).castSucc (G.X s).succ) ↔
      ¬RowMatchingSource s (G.X s) x := by
  have heq : x.swapRows (G.X s).castSucc (G.X s).succ =
      x.relabelRows (Equiv.swap (G.X s).castSucc (G.X s).succ) := by
    ext c
    simp only [GridState.swapRows_apply, GridState.relabelRows_apply]
  rw [heq]
  exact rowMatchingSource_relabel_swap s (G.X s) x

/-- On a nonmatching full edge between source pairs, O count or outer level strictly increases
or decreases, respectively. -/
theorem stabilization_matching_step_decreases
    (x z : GridState (n + 1)) (hx : RowMatchingSource s (G.X s) x)
    (hz : RowMatchingSource s (G.X s) z)
    (hxc : x s.succ ≠ (G.X s).castSucc) (hzc : z s.succ ≠ (G.X s).castSucc)
    (hxz : x ≠ z)
    (r : GridRectangleBetween x (z.swapRows (G.X s).castSucc (G.X s).succ)) (he : r.IsEmpty) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ x <
        (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ z ∨
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ x =
          (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ z ∧
        G.stabilizeXLevel s z < G.stabilizeXLevel s x) := by
  let H := G.stabilizeX s.castSucc (G.X s).castSucc s
  have hthin := H.maslovO_sub_two_mul_card_OColumns_eq_maslovO_sub_one
    (G.isEmpty_stabilizeXRowSwapRectangle s z)
  rw [stabilizationRowRectangle_source_OColumns G s z hz, Finset.card_empty,
    Nat.cast_zero, mul_zero, sub_zero, H.maslovO_eq_intCast, H.maslovO_eq_intCast] at hthin
  have hr := H.maslovO_sub_two_mul_card_OColumns_eq_maslovO_sub_one he
  rw [H.maslovO_eq_intCast, H.maslovO_eq_intCast] at hr
  have hdegree : H.maslovOℤ z = H.maslovOℤ x + 2 * (H.OColumns r.toGridRectangle).card := by
    have hq : (H.maslovOℤ z : ℚ) = (H.maslovOℤ x : ℚ) +
        2 * ((H.OColumns r.toGridRectangle).card : ℚ) := by linarith
    exact_mod_cast hq
  by_cases hO : H.OColumns r.toGridRectangle = ∅
  · right
    have hdeg : H.maslovOℤ x = H.maslovOℤ z := by
      rw [hO, Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] at hdegree
      exact hdegree.symm
    refine ⟨hdeg, ?_⟩
    have hns : ¬RowMatchingSource s (G.X s)
        (z.swapRows (G.X s).castSucc (G.X s).succ) := by
      intro h
      exact (rowMatchingSource_swapRows G s z).mp h hz
    have hnc : (z.swapRows (G.X s).castSucc (G.X s).succ) s.succ ≠ (G.X s).succ := by
      rw [GridState.swapRows_apply, ne_eq, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
      exact hzc
    rcases stabilization_level_lt_or_matching_of_OColumns_empty G s r hx hns hxc hnc hO
      with hlt | heq
    · simpa only [G.stabilizeXLevel_swapRows] using hlt
    · have hh := congrArg (fun u : GridState (n + 1) =>
        u.swapRows (G.X s).castSucc (G.X s).succ) heq
      simp only [GridState.swapRows_swapRows] at hh
      exact False.elim (hxz hh.symm)
  · left
    have hp : 0 < (H.OColumns r.toGridRectangle).card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hO)
    change H.maslovOℤ x < H.maslovOℤ z
    omega


/-- The noncritical sources indexing the internal matching paths. -/
def StabilizationMatchingNode :=
  {x : GridState (n + 1) // RowMatchingSource s (G.X s) x ∧ x s.succ ≠ (G.X s).castSucc}

instance : Finite (StabilizationMatchingNode G s) := by
  unfold StabilizationMatchingNode
  infer_instance

/-- First compare negative Maslov degree, then the outer-square level. -/
noncomputable def stabilizationMatchingNodeWeight (x : StabilizationMatchingNode G s) : ℤ ×ₗ ℚ :=
  toLex (-(G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ x.val,
    G.stabilizeXLevel s x.val)

/-- A nonzero nonmatching coefficient strictly lowers the matching-node weight. -/
theorem stabilizationMatchingNodeWeight_lt_of_coefficient_ne_zero
    (R : Type*) [CommSemiring R] (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (hc : laurentCoefficient (G.stabilizeX s.castSucc (G.X s).castSucc s) R x.val
      (z.val.swapRows (G.X s).castSucc (G.X s).succ) ≠ 0) :
    stabilizationMatchingNodeWeight G s z < stabilizationMatchingNodeWeight G s x := by
  classical
  have hn : (GridRectangleBetween.emptyRectangles x.val
      (z.val.swapRows (G.X s).castSucc (G.X s).succ)).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    exact hc (by rw [laurentCoefficient_eq, hn, Finset.sum_empty])
  obtain ⟨r, hr⟩ := hn
  have h := stabilization_matching_step_decreases G s x.val z.val x.property.1 z.property.1
    x.property.2 z.property.2 (fun hv => hxz (Subtype.ext hv)) r
    ((GridRectangleBetween.mem_emptyRectangles r).mp hr)
  simp only [stabilizationMatchingNodeWeight, Prod.Lex.toLex_lt_toLex]
  rcases h with h | ⟨hm, hl⟩
  · exact Or.inl (neg_lt_neg h)
  · exact Or.inr ⟨congrArg Neg.neg hm.symm, hl⟩

/-- The strict matching-node order is well founded because the state set is finite. -/
theorem stabilizationMatchingNodeWeight_wellFounded :
    WellFounded (InvImage (· < ·) (stabilizationMatchingNodeWeight G s)) := by
  exact Finite.wellFounded_of_trans_of_irrefl _

end OnLeConjecture.KnotFloer.GridFull
