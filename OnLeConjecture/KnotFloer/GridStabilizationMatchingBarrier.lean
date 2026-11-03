/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingAlternation
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingCenterEdges

/-!
# Fixed intervals along internal matching paths

An initial interval with no point below the new-column point remains unchanged
along a matching path whose two matching-row points lie beyond that interval.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti

private theorem earlier_point_ne {n : ℕ} {b L p c : Fin n}
    (hL : L ∈ Grid.cIoo b p) (hc : c = L ∨ c ∈ Grid.cIoo b L) : c ≠ p := by
  rcases hc with rfl | hc
  · exact Grid.ne_right_of_mem_cIoo hL
  · exact Grid.ne_right_of_mem_cIoo (Grid.cIoo_subset_cIoo_right_of_mem_cIoo hL hc)

private theorem after_initial_interval {n : ℕ} {b L k p : Fin n}
    (hL : L ∈ Grid.cIoo b p) (hk : k ∈ Grid.cIoo b p)
    (hkL : k ≠ L) (hkn : k ∉ Grid.cIoo b L) : L ∈ Grid.cIoo b k := by
  simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff] at *
  split_ifs at * <;> omega

private theorem outside_upper_interval {n : ℕ} {b L p R k : Fin n}
    (hL : L ∈ Grid.cIoo b p) (hp : p ∈ Grid.cIoo b R)
    (hk : k = R ∨ k ∈ Grid.cIoo R b) : L ∈ Grid.cIoo k p := by
  simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff] at *
  split_ifs at * <;> omega

private theorem later_point_ne {n : ℕ} {b R p c : Fin n}
    (hp : p ∈ Grid.cIoo b R) (hc : c = R ∨ c ∈ Grid.cIoo R b) : c ≠ p := by
  simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff] at *
  split_ifs at * <;> omega

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- A low-point-free initial interval stays to the left of both matching-row positions. -/
theorem stabilizationMatchingTransition_preserves_lower_barrier
    (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (he : r.IsEmpty) (L : Fin (n + 1))
    (hL : L ∈ Grid.cIoo s.succ (x.val.transpose (G.X s).castSucc))
    (hclear : ∀ c, c = L ∨ c ∈ Grid.cIoo s.succ L →
      x.val c ∉ Grid.cIoo (G.X s).succ (x.val s.succ)) :
    L ∈ Grid.cIoo s.succ (z.val.transpose (G.X s).castSucc) := by
  rcases stabilizationMatchingTransition_oriented_row_edge G s x z hxz r he with ht | hb
  · have hcols := stabilizationMatchingTransition_advancing_columns G s x z hxz r ht
    rw [hcols.2.2]
    exact Grid.cIoo_subset_cIoo_right_of_mem_cIoo
      (stabilizationMatchingNode_row_columns_interior G s x).1 hL
  · have hcols := stabilizationMatchingTransition_retreating_columns G s x z hxz r hb
    have hlow := stabilizationMatchingTransition_retreating_height G s x z hxz r he hb
    have hk : z.val.transpose (G.X s).castSucc ∈
        Grid.cIoo s.succ (x.val.transpose (G.X s).castSucc) := by
      simpa only [hcols.2.2] using (stabilizationMatchingNode_row_columns_interior G s z).1
    have hv : x.val (z.val.transpose (G.X s).castSucc) = r.top := by
      rw [← hcols.2.1]
      rfl
    apply after_initial_interval hL hk
    · intro h
      exact hclear _ (Or.inl h) (hv ▸ hlow)
    · intro h
      exact hclear _ (Or.inr h) (hv ▸ hlow)

/-- Every point of that initial interval, including its final endpoint, is fixed. -/
theorem stabilizationMatchingTransition_fixed_initial_interval
    (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (he : r.IsEmpty) (L : Fin (n + 1))
    (hL : L ∈ Grid.cIoo s.succ (x.val.transpose (G.X s).castSucc))
    (hclear : ∀ c, c = L ∨ c ∈ Grid.cIoo s.succ L →
      x.val c ∉ Grid.cIoo (G.X s).succ (x.val s.succ))
    (c : Fin (n + 1)) (hc : c = L ∨ c ∈ Grid.cIoo s.succ L) : z.val c = x.val c := by
  have hzL := stabilizationMatchingTransition_preserves_lower_barrier G s x z hxz r he L hL hclear
  have hxL1 := Grid.cIoo_subset_cIoo_right_of_mem_cIoo
    (stabilizationMatchingNode_row_columns_interior G s x).1 hL
  have hzL1 := Grid.cIoo_subset_cIoo_right_of_mem_cIoo
    (stabilizationMatchingNode_row_columns_interior G s z).1 hzL
  have h0 := earlier_point_ne hL hc
  have h1 := earlier_point_ne hxL1 hc
  have hcl : c ≠ r.left := by
    rcases stabilizationMatchingTransition_oriented_row_edge G s x z hxz r he with ht | hb
    · rw [(stabilizationMatchingTransition_advancing_columns G s x z hxz r ht).2.1]
      exact earlier_point_ne hzL1 hc
    · rw [(stabilizationMatchingTransition_retreating_columns G s x z hxz r hb).1]
      exact h1
  have hcr : c ≠ r.right := by
    rcases stabilizationMatchingTransition_oriented_row_edge G s x z hxz r he with ht | hb
    · rw [(stabilizationMatchingTransition_advancing_columns G s x z hxz r ht).1]
      exact h0
    · rw [(stabilizationMatchingTransition_retreating_columns G s x z hxz r hb).2.1]
      exact earlier_point_ne hzL hc
  have hv0 : x.val c ≠ (G.X s).castSucc := by
    intro h
    exact h0 ((x.val.transpose_apply_apply c).symm.trans (congrArg x.val.transpose h))
  have hv1 : x.val c ≠ (G.X s).succ := by
    intro h
    exact h1 ((x.val.transpose_apply_apply c).symm.trans (congrArg x.val.transpose h))
  have h := r.map_of_ne c hcl hcr
  change Equiv.swap (G.X s).castSucc (G.X s).succ (z.val c) = x.val c at h
  rwa [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne hv0 hv1] at h

/-- A high-point-free final interval stays beyond both matching-row positions. -/
theorem stabilizationMatchingTransition_preserves_upper_barrier
    (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (he : r.IsEmpty) (L R : Fin (n + 1))
    (hL : L ∈ Grid.cIoo s.succ (x.val.transpose (G.X s).castSucc))
    (hR : x.val.transpose (G.X s).succ ∈ Grid.cIoo s.succ R)
    (hclear : ∀ c, c = R ∨ c ∈ Grid.cIoo R s.succ →
      x.val c ∉ Grid.cIoo (x.val L) (G.X s).castSucc) :
    z.val.transpose (G.X s).succ ∈ Grid.cIoo s.succ R := by
  have hp := Grid.cIoo_subset_cIoo_right_of_mem_cIoo hR
    (stabilizationMatchingNode_row_columns_interior G s x).1
  rcases stabilizationMatchingTransition_oriented_row_edge G s x z hxz r he with ht | hb
  · have hcols := stabilizationMatchingTransition_advancing_columns G s x z hxz r ht
    by_contra hn
    have hk : z.val.transpose (G.X s).succ = R ∨
        z.val.transpose (G.X s).succ ∈ Grid.cIoo R s.succ := by
      by_cases hk : z.val.transpose (G.X s).succ = R
      · exact Or.inl hk
      · exact Or.inr (Grid.mem_cIoo_swap_of_notMem
          ((Grid.mem_cIoo _ _ _).mp hR).1
          (stabilizationMatchingNode_row_columns_ne_newColumn G s z).2 hk hn)
    have hc : L ∈ Grid.cIoo r.left r.right := by
      rw [hcols.1, hcols.2.1]
      exact outside_upper_interval hL hp hk
    have hL0 : x.val L ≠ (G.X s).castSucc := by
      intro h
      exact Grid.ne_right_of_mem_cIoo hL
        ((x.val.transpose_apply_apply L).symm.trans (congrArg x.val.transpose h))
    have hb0 : r.bottom ≠ (G.X s).castSucc := fun h => r.bottom_ne_top (h.trans ht.symm)
    have hLb : x.val L ≠ r.bottom := fun h =>
      Grid.ne_left_of_mem_cIoo hc (x.val.toPerm.injective h)
    have hnotL : x.val L ∉ Grid.cIoo r.bottom (G.X s).castSucc := by
      simpa only [← r.bottom_def, ← r.top_def, ht] using
        (r.isEmpty_iff_forall_notMem_cIoo.mp he) L hc
    have hnotb : r.bottom ∉ Grid.cIoo (x.val L) (G.X s).castSucc := by
      have h := hclear _ hk
      simpa only [← hcols.2.1, ← r.bottom_def] using h
    exact hnotb (Grid.mem_cIoo_cyclic_left
      (Grid.mem_cIoo_swap_of_notMem hb0 hLb hL0 hnotL))
  · rw [(stabilizationMatchingTransition_retreating_columns G s x z hxz r hb).2.2]
    exact hp

/-- Every point of that final interval, including its first endpoint, is fixed. -/
theorem stabilizationMatchingTransition_fixed_final_interval
    (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (he : r.IsEmpty) (L R : Fin (n + 1))
    (hL : L ∈ Grid.cIoo s.succ (x.val.transpose (G.X s).castSucc))
    (hR : x.val.transpose (G.X s).succ ∈ Grid.cIoo s.succ R)
    (hclear : ∀ c, c = R ∨ c ∈ Grid.cIoo R s.succ →
      x.val c ∉ Grid.cIoo (x.val L) (G.X s).castSucc)
    (c : Fin (n + 1)) (hc : c = R ∨ c ∈ Grid.cIoo R s.succ) : z.val c = x.val c := by
  have hzR := stabilizationMatchingTransition_preserves_upper_barrier
    G s x z hxz r he L R hL hR hclear
  have hxR0 := Grid.cIoo_subset_cIoo_right_of_mem_cIoo hR
    (stabilizationMatchingNode_row_columns_interior G s x).1
  have hzR0 := Grid.cIoo_subset_cIoo_right_of_mem_cIoo hzR
    (stabilizationMatchingNode_row_columns_interior G s z).1
  have h0 := later_point_ne hxR0 hc
  have h1 := later_point_ne hR hc
  have hcl : c ≠ r.left := by
    rcases stabilizationMatchingTransition_oriented_row_edge G s x z hxz r he with ht | hb
    · rw [(stabilizationMatchingTransition_advancing_columns G s x z hxz r ht).2.1]
      exact later_point_ne hzR hc
    · rw [(stabilizationMatchingTransition_retreating_columns G s x z hxz r hb).1]
      exact h1
  have hcr : c ≠ r.right := by
    rcases stabilizationMatchingTransition_oriented_row_edge G s x z hxz r he with ht | hb
    · rw [(stabilizationMatchingTransition_advancing_columns G s x z hxz r ht).1]
      exact h0
    · rw [(stabilizationMatchingTransition_retreating_columns G s x z hxz r hb).2.1]
      exact later_point_ne hzR0 hc
  have hv0 : x.val c ≠ (G.X s).castSucc := by
    intro h
    exact h0 ((x.val.transpose_apply_apply c).symm.trans (congrArg x.val.transpose h))
  have hv1 : x.val c ≠ (G.X s).succ := by
    intro h
    exact h1 ((x.val.transpose_apply_apply c).symm.trans (congrArg x.val.transpose h))
  have h := r.map_of_ne c hcl hcr
  change Equiv.swap (G.X s).castSucc (G.X s).succ (z.val c) = x.val c at h
  rwa [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne hv0 hv1] at h

/-- Two fixed points and empty outer intervals that exclude every subsequent center exit. -/
structure StabilizationMatchingBarrier (L R : Fin (n + 1))
    (x : StabilizationMatchingNode G s) : Prop where
  lower_position : L ∈ Grid.cIoo s.succ (x.val.transpose (G.X s).castSucc)
  upper_position : x.val.transpose (G.X s).succ ∈ Grid.cIoo s.succ R
  lower_clear : ∀ c, c = L ∨ c ∈ Grid.cIoo s.succ L →
    x.val c ∉ Grid.cIoo (G.X s).succ (x.val s.succ)
  upper_clear : ∀ c, c = R ∨ c ∈ Grid.cIoo R s.succ →
    x.val c ∉ Grid.cIoo (x.val L) (G.X s).castSucc
  exit_point : x.val R ∈ Grid.cIoo (G.X s).succ (x.val s.succ)

/-- The concrete barrier conditions persist under every empty internal matching transition. -/
theorem StabilizationMatchingBarrier.transition {L R : Fin (n + 1)}
    {x z : StabilizationMatchingNode G s} (h : StabilizationMatchingBarrier G s L R x)
    (hxz : x ≠ z)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (he : r.IsEmpty) : StabilizationMatchingBarrier G s L R z := by
  have hu := stabilizationMatchingTransition_newColumn G s x z r
  have hleft := stabilizationMatchingTransition_fixed_initial_interval
    G s x z hxz r he L h.lower_position h.lower_clear
  have hright := stabilizationMatchingTransition_fixed_final_interval
    G s x z hxz r he L R h.lower_position h.upper_position h.upper_clear
  refine ⟨stabilizationMatchingTransition_preserves_lower_barrier
      G s x z hxz r he L h.lower_position h.lower_clear,
    stabilizationMatchingTransition_preserves_upper_barrier
      G s x z hxz r he L R h.lower_position h.upper_position h.upper_clear,
    ?_, ?_, ?_⟩
  · intro c hc
    simpa only [hleft c hc, ← hu] using h.lower_clear c hc
  · intro c hc
    simpa only [hright c hc, hleft L (Or.inl rfl)] using h.upper_clear c hc
  · simpa only [hright R (Or.inl rfl), ← hu] using h.exit_point

/-- A node carrying these barriers admits no empty rectangle to any center state. -/
theorem StabilizationMatchingBarrier.no_exit {L R : Fin (n + 1)}
    {x : StabilizationMatchingNode G s} (h : StabilizationMatchingBarrier G s L R x)
    (y : GridState n)
    (r : GridRectangleBetween x.val (y.insertPoint s.succ (G.X s).succ)) : ¬r.IsEmpty := by
  intro he
  exact stabilizationMatchingExit_empty_region G s x y r he R
    (Grid.mem_cIoo_cyclic_left h.upper_position) h.exit_point

end OnLeConjecture.KnotFloer.GridFull
