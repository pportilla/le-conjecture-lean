/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingCenterEdges
public import OnLeConjecture.KnotFloer.GridStabilizationMatchingHeight

/-! # The orientations of internal transitions adjacent to center rectangles -/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- An empty entry rectangle cannot be followed by a retreating internal rectangle. -/
theorem stabilizationMatchingEntry_not_retreating
    (a : GridState n) (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (e : GridRectangleBetween (a.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s x))
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (he : e.IsEmpty) (hr : r.IsEmpty) (hb : r.bottom = (G.X s).succ) : False := by
  have rc := stabilizationMatchingTransition_retreating_columns G s x z hxz r hb
  have hlow := stabilizationMatchingTransition_retreating_height G s x z hxz r hr hb
  have hc : r.right ∈ Grid.cIoo s.succ (x.val.transpose (G.X s).castSucc) := by
    simpa only [rc.2.1, rc.2.2] using
      (stabilizationMatchingNode_row_columns_interior G s z).1
  exact stabilizationMatchingEntry_empty_region G s a x e he r.right hc hlow

/-- A retreating internal rectangle cannot be followed by an empty center exit. -/
theorem stabilizationMatchingRetreating_not_exit
    (x z : StabilizationMatchingNode G s) (hxz : x ≠ z) (a : GridState n)
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (e : GridRectangleBetween z.val (a.insertPoint s.succ (G.X s).succ))
    (hr : r.IsEmpty) (he : e.IsEmpty) (hb : r.bottom = (G.X s).succ) : False := by
  have rc := stabilizationMatchingTransition_retreating_columns G s x z hxz r hb
  have hlow := stabilizationMatchingTransition_retreating_height G s x z hxz r hr hb
  have hc : r.left ∈ Grid.cIoo (z.val.transpose (G.X s).succ) s.succ := by
    simpa only [rc.1, rc.2.2] using
      (stabilizationMatchingNode_row_columns_interior G s x).2
  have h0 : r.top ≠ (G.X s).castSucc := fun h =>
    stabilizationMatchingTransition_not_both_rows G s x z hxz r (Or.inr h) (Or.inl hb)
  have h1 : r.top ≠ (G.X s).succ := fun h => r.bottom_ne_top (hb.trans h.symm)
  have hz : z.val r.left = r.top := by
    have h := r.map_left
    change Equiv.swap (G.X s).castSucc (G.X s).succ (z.val r.left) = r.top at h
    rwa [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne h0 h1] at h
  apply stabilizationMatchingExit_empty_region G s z a e he r.left hc
  simpa only [hz, ← stabilizationMatchingTransition_newColumn G s x z r] using hlow

/-- The first internal rectangle after an empty center entry must advance. -/
theorem stabilizationMatchingEntry_advancing
    (a : GridState n) (x z : StabilizationMatchingNode G s) (hxz : x ≠ z)
    (e : GridRectangleBetween (a.insertPoint s.succ (G.X s).succ)
      (stabilizationMatchingTargetState G s x))
    (r : GridRectangleBetween x.val (stabilizationMatchingTargetState G s z))
    (he : e.IsEmpty) (hr : r.IsEmpty) : r.top = (G.X s).castSucc := by
  rcases stabilizationMatchingTransition_oriented_row_edge G s x z hxz r hr with h | h
  · exact h
  · exact False.elim (stabilizationMatchingEntry_not_retreating G s a x z hxz e r he hr h)

end OnLeConjecture.KnotFloer.GridFull
