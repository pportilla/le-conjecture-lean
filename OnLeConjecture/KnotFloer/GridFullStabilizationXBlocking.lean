/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullStabilizationBasic
public import OnLeConjecture.KnotFloer.GridFullLaurentXBlocking

/-!
# Blocking the two new X markings of a stabilization

After blocking only the two new X squares, the differential has zero coefficient
from an off-center state to a center state. Its center quotient is the old differential
with only the split X square blocked. Every other X marking remains unrestricted.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti GridRectangleBetween

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- A rectangle entering the center from an off-center state covers one of the two new X's. -/
theorem stabilizationIncomingRectangle_crosses_newX {y z : GridState (n + 1)}
    (hy : y s.succ ≠ (G.X s).succ) (hz : z s.succ = (G.X s).succ)
    (r : GridRectangleBetween y z) :
    ∃ a ∈ ({s.castSucc, s.succ} : Finset (Fin (n + 1))),
      (a, (G.stabilizeX s.castSucc (G.X s).castSucc s).X a) ∈
        r.toGridRectangle.coveredSquares := by
  classical
  have hbt : r.bottom ≠ r.top := fun h => r.left_ne_right (y.toPerm.injective h)
  by_cases hl : s.succ = r.left
  · have htop : r.top = (G.X s).succ := by rw [top_def, ← r.map_left, ← hl, hz]
    refine ⟨s.succ, by simp, ?_⟩
    have hcov : (s.succ, (G.X s).castSucc) ∈ r.toGridRectangle.coveredSquares := by
      simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
        GridRectangle.mem_coveredRows, toGridRectangle_left, toGridRectangle_right,
        toGridRectangle_bottom, toGridRectangle_top]
      rw [← hl, htop]
      exact ⟨hl ▸ Grid.left_mem_cIco r.left_ne_right,
        Grid.castSucc_mem_cIco_succ fun h => hbt (h.trans htop.symm)⟩
    simpa using hcov
  by_cases hr : s.succ = r.right
  · have hbot : r.bottom = (G.X s).succ := by rw [bottom_def, ← r.map_right, ← hr, hz]
    refine ⟨s.castSucc, by simp, ?_⟩
    have hcov : (s.castSucc, (G.X s).succ) ∈ r.toGridRectangle.coveredSquares := by
      simp only [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
        GridRectangle.mem_coveredRows, toGridRectangle_left, toGridRectangle_right,
        toGridRectangle_bottom, toGridRectangle_top]
      rw [← hr, hbot]
      exact ⟨Grid.castSucc_mem_cIco_succ fun h => r.left_ne_right (h.trans hr),
        hbot ▸ Grid.left_mem_cIco hbt⟩
    simpa using hcov
  exact False.elim (hy ((r.map_of_ne s.succ hl hr).symm.trans hz))

/-- Empty rectangles between two center states avoid both of the new X markings. -/
theorem stabilizationCenterRectangle_avoids_newX {x y : GridState n}
    (r : GridRectangleBetween
      (x.insertPoint s.succ (G.X s).succ) (y.insertPoint s.succ (G.X s).succ))
    (hre : r.IsEmpty) :
    ¬∃ a ∈ ({s.castSucc, s.succ} : Finset (Fin (n + 1))),
      (a, (G.stabilizeX s.castSucc (G.X s).castSucc s).X a) ∈
        r.toGridRectangle.coveredSquares := by
  obtain ⟨r, rfl⟩ := exists_insertPoint_eq r
  have hr := (isEmpty_insertStabilizationCenter_iff G s r).mp hre
  rintro ⟨a, ha, hcov⟩
  rw [mem_coveredSquares_insertPoint_succ_succ] at hcov
  simp only [G.predAbove_X_stabilizeX] at hcov
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact hr.2 (by simpa using hcov)
  · have ha' := Finset.mem_singleton.mp ha
    subst a
    exact hr.2 (by simpa using hcov)

variable (R : Type*) [CommSemiring R]

/-- Blocking the new X's removes the entire off-center to center coefficient block. -/
theorem laurentXBlocked_stabilization_offCenter_to_center
    {y z : GridState (n + 1)} (hy : y s.succ ≠ (G.X s).succ)
    (hz : z s.succ = (G.X s).succ) :
    laurentXBlockedDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
      R {s.castSucc, s.succ} (Finsupp.single y 1) z = 0 := by
  classical
  rw [laurentXBlockedDifferential_apply_apply, Finsupp.sum_single_index]
  · simp only [one_mul]
    apply Finset.sum_eq_zero
    intro r hr
    exact False.elim ((Finset.mem_filter.mp hr).2
      (stabilizationIncomingRectangle_crosses_newX G s hy hz r))
  · simp

/-- Blocking the two new X's leaves the center-to-center block unchanged. -/
theorem laurentXBlocked_stabilization_center_coefficient (x y : GridState n) :
    laurentXBlockedDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
      R {s.castSucc, s.succ}
        (Finsupp.single (x.insertPoint s.succ (G.X s).succ) 1)
        (y.insertPoint s.succ (G.X s).succ) =
      laurentCoefficient (G.stabilizeX s.castSucc (G.X s).castSucc s) R
        (x.insertPoint s.succ (G.X s).succ) (y.insertPoint s.succ (G.X s).succ) := by
  classical
  simp only [laurentXBlockedDifferential_apply_apply, Finsupp.sum_single_index,
    zero_mul, one_mul, laurentCoefficient_eq, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  rw [if_pos (stabilizationCenterRectangle_avoids_newX G s r
    ((mem_emptyRectangles r).mp hr))]

/-- The center quotient has exactly the old differential with the split X square blocked. -/
theorem laurentXBlocked_stabilization_center_eq_old (x y : GridState n) :
    laurentXBlockedDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
      R {s.castSucc, s.succ}
        (Finsupp.single (x.insertPoint s.succ (G.X s).succ) 1)
        (y.insertPoint s.succ (G.X s).succ) =
      laurentXBlockedDifferential G R {s} (Finsupp.single x 1) y := by
  classical
  rw [laurentXBlocked_stabilization_center_coefficient,
    laurentCoefficient_stabilizeX_insertPoint, laurentXBlockedDifferential_apply_apply]
  simp

/-- Center projection is a chain map for the locally blocked differentials. -/
theorem laurentStabilizationCenterProjection_xBlocked_chain :
    laurentStabilizationCenterProjection G s R ∘ₗ
        laurentXBlockedDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
          R {s.castSucc, s.succ} =
      laurentXBlockedDifferential G R {s} ∘ₗ laurentStabilizationCenterProjection G s R := by
  classical
  apply Finsupp.lhom_ext'
  intro y
  apply LinearMap.ext_ring
  apply Finsupp.ext
  intro x
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply,
    laurentStabilizationCenterProjection_apply]
  by_cases hy : y s.succ = (G.X s).succ
  · obtain ⟨y, rfl⟩ := GridState.exists_insertPoint_eq hy
    rw [laurentXBlocked_stabilization_center_eq_old]
    have hproj : laurentStabilizationCenterProjection G s R
        (Finsupp.single (y.insertPoint s.succ (G.X s).succ) 1) = Finsupp.single y 1 := by
      apply Finsupp.ext
      intro z
      simp only [laurentStabilizationCenterProjection_apply, Finsupp.single_apply,
        (GridState.insertPoint_injective s.succ (G.X s).succ).eq_iff]
    rw [hproj]
  · rw [laurentXBlocked_stabilization_offCenter_to_center G s R hy (by simp)]
    have hproj : laurentStabilizationCenterProjection G s R (Finsupp.single y 1) = 0 := by
      apply Finsupp.ext
      intro z
      rw [laurentStabilizationCenterProjection_apply, Finsupp.zero_apply]
      apply Finsupp.single_eq_of_ne
      intro heq
      apply hy
      rw [← heq]
      simp
    rw [hproj, map_zero, Finsupp.zero_apply]

end OnLeConjecture.KnotFloer.GridFull
