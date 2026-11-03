/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingSchur
public import OnLeConjecture.KnotFloer.GridStabilizationStandardDecomposition

/-!
# The direct matching coefficient

The direct term of the transferred differential counts empty rectangles between
center states. Every such rectangle is admissible, and its full O weight equals
the standard weight with the new marking omitted.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- An empty rectangle has no interior point that could violate admissibility. -/
theorem stabilizationAdmissibleRectangle_of_isEmpty {x y : GridState n}
    (r : GridRectangleBetween (x.insertPoint s.succ (G.X s).succ)
      (y.insertPoint s.succ (G.X s).succ)) (hr : r.IsEmpty) :
    StabilizationAdmissibleRectangle G s r := by
  intro c hc hp
  exact False.elim ((r.isEmpty_iff_forall_notMem_cIoo.mp hr) c hc hp)

open Classical in
/-- Filtering the admissible rectangles by emptiness recovers all empty rectangles. -/
theorem stabilizationAdmissibleRectangles_filter_isEmpty (x y : GridState n) :
    (stabilizationAdmissibleRectangles G s x y).filter (fun r => r.IsEmpty) =
      GridRectangleBetween.emptyRectangles
        (x.insertPoint s.succ (G.X s).succ) (y.insertPoint s.succ (G.X s).succ) := by
  classical
  ext r
  simp only [Finset.mem_filter, mem_stabilizationAdmissibleRectangles,
    GridRectangleBetween.mem_emptyRectangles]
  exact ⟨And.right, fun hr => ⟨stabilizationAdmissibleRectangle_of_isEmpty G s r hr, hr⟩⟩

variable (R : Type*) [CommRing R]

/-- The direct matrix entry is the full Laurent coefficient between the two centers. -/
theorem stabilizationMatchingDirect_single_apply (x y : GridState n) :
    stabilizationMatchingDirect G s R (single x 1) y =
      laurentCoefficient (G.stabilizeX s.castSucc (G.X s).castSucc s) R
        (x.insertPoint s.succ (G.X s).succ) (y.insertPoint s.succ (G.X s).succ) := by
  simp only [stabilizationMatchingDirect, LinearMap.comp_apply,
    laurentStabilizationCenterInclusion_single, laurentStabilizationCenterProjection_apply,
    laurentDifferential_single, laurentOnGenerator_apply]

open Classical in
/-- The direct matrix entry is the standard weighted sum over empty admissible rectangles. -/
theorem stabilizationMatchingDirect_single_apply_eq_sum (x y : GridState n) :
    stabilizationMatchingDirect G s R (single x 1) y =
      ∑ r ∈ (stabilizationAdmissibleRectangles G s x y).filter (fun r => r.IsEmpty),
        stabilizationStandardWeight G s R r := by
  classical
  rw [stabilizationMatchingDirect_single_apply, laurentCoefficient_eq,
    stabilizationAdmissibleRectangles_filter_isEmpty]
  apply Finset.sum_congr rfl
  intro r hr
  exact (stabilizationStandardWeight_of_isEmpty G s R r
    ((GridRectangleBetween.mem_emptyRectangles r).mp hr)).symm

end OnLeConjecture.KnotFloer.GridFull
