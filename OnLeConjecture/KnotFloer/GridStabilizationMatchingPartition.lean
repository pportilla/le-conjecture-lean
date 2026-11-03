/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationStandardDecomposition

/-!
# Partition of the admissible stabilization rectangles

The admissible rectangles split into empty rectangles, rectangles containing the
inserted center with bottom on the lower matching row, and those with another
bottom row. These are precisely the three terms of the matching path formula.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- An empty rectangle between center states cannot contain their common center. -/
theorem stabilizationCenter_not_mem_interior_of_isEmpty {x y : GridState n}
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ)) (he : r.IsEmpty) :
    (s.succ, (G.X s).succ) ∉ r.toGridRectangle.interior := by
  intro hi
  obtain ⟨hc, hv⟩ := (GridRectangleBetween.mem_toGridRectangle_interior r).mp hi
  rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo] at he
  exact he s.succ hc (by
    simpa only [GridState.insertPoint_apply_newColumn, r.bottom_def, r.top_def] using hv)

open Classical in
/-- The sum over all admissible rectangles is the sum of its three matching-path portions. -/
theorem sum_stabilizationStandardWeight_partition
    (R : Type*) [CommSemiring R] (x y : GridState n) :
    ∑ r ∈ stabilizationAdmissibleRectangles G s x y,
        stabilizationStandardWeight G s R r =
      (∑ r ∈ (stabilizationAdmissibleRectangles G s x y).filter (fun r => r.IsEmpty),
        stabilizationStandardWeight G s R r) +
      (∑ r ∈ (stabilizationAdmissibleRectangles G s x y).filter (fun r =>
          (s.succ, (G.X s).succ) ∈ r.toGridRectangle.interior ∧
            r.bottom = (G.X s).castSucc), stabilizationStandardWeight G s R r) +
      (∑ r ∈ (stabilizationAdmissibleRectangles G s x y).filter (fun r =>
          (s.succ, (G.X s).succ) ∈ r.toGridRectangle.interior ∧
            r.bottom ≠ (G.X s).castSucc), stabilizationStandardWeight G s R r) := by
  classical
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have ha := (mem_stabilizationAdmissibleRectangles G s r).mp hr
  by_cases he : r.IsEmpty
  · have hi := stabilizationCenter_not_mem_interior_of_isEmpty G s r he
    simp only [he, hi, false_and, ↓reduceIte, add_zero]
  · have hi := stabilizationAdmissibleRectangle_center_mem_of_not_isEmpty G s r ha he
    by_cases hb : r.bottom = (G.X s).castSucc <;> simp [he, hi, hb]

end OnLeConjecture.KnotFloer.GridFull
