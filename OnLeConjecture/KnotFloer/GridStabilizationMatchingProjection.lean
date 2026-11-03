/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationMatchingGeometry
public import OnLeConjecture.KnotFloer.GridStabilizationTransferredCenter

/-!
# The actual full projection on matching targets

The second projection is the ordinary center projection plus its values on
the noncritical matching targets. This statewise identity connects the
constructed HPL projection to the finite matching-transition matrix.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-- Matching targets are nonsources. -/
theorem stabilizationMatchingTarget_not_source (z : StabilizationMatchingNode G s) :
    ¬RowMatchingSource s (G.X s) (stabilizationMatchingTargetState G s z) := by
  intro h
  exact (rowMatchingSource_swapRows G s z.val).mp h z.property.1

/-- Every nonsource outside the center is the target of a unique noncritical matching source. -/
theorem exists_stabilizationMatchingTarget_of_not_source
    (x : GridState (n + 1)) (hx : ¬RowMatchingSource s (G.X s) x)
    (hc : x s.succ ≠ (G.X s).succ) :
    ∃ z : StabilizationMatchingNode G s, stabilizationMatchingTargetState G s z = x := by
  let z := x.swapRows (G.X s).castSucc (G.X s).succ
  have hz : RowMatchingSource s (G.X s) z := (rowMatchingSource_swapRows G s x).mpr hx
  have hback : z.swapRows (G.X s).castSucc (G.X s).succ = x := by
    simp only [z, GridState.swapRows_swapRows]
  have hzc : z s.succ ≠ (G.X s).castSucc := by
    intro h
    have hh := congrArg (fun w : GridState (n + 1) => w s.succ) hback
    rw [GridState.swapRows_apply, h, Equiv.swap_apply_left] at hh
    exact hc hh.symm
  exact ⟨⟨z, hz, hzc⟩, hback⟩

variable (R : Type*) [CommRing R]

/-- Include the noncritical matching-target basis in the full state module. -/
def stabilizationMatchingTargetInclusion :
    (StabilizationMatchingNode G s →₀ LaurentPolynomial R) →ₗ[LaurentPolynomial R]
      LaurentChain R (n + 1) :=
  Finsupp.lmapDomain (LaurentPolynomial R) (LaurentPolynomial R)
    (stabilizationMatchingTargetState G s)

@[simp]
theorem stabilizationMatchingTargetInclusion_single (z : StabilizationMatchingNode G s)
    (a : LaurentPolynomial R) :
    stabilizationMatchingTargetInclusion G s R (single z a) =
      single (stabilizationMatchingTargetState G s z) a :=
  Finsupp.mapDomain_single

/-- Reading a matching-target generator recovers its node coefficient. -/
theorem stabilizationMatchingTargetProjection_single (z : StabilizationMatchingNode G s) :
    stabilizationMatchingTargetProjection G s R
      (single (stabilizationMatchingTargetState G s z) 1) = single z 1 := by
  classical
  apply Finsupp.ext
  intro w
  simp only [stabilizationMatchingTargetProjection_apply, Finsupp.single_apply,
    (stabilizationMatchingTargetState_injective G s).eq_iff]

/-- Matching targets do not contain the center point. -/
theorem stabilizationMatchingTarget_ne_center (z : StabilizationMatchingNode G s) :
    stabilizationMatchingTargetState G s z s.succ ≠ (G.X s).succ := by
  rw [stabilizationMatchingTargetState_newColumn]
  exact stabilizationMatchingNode_ne_newRow G s z

/-- A full basis state outside the center has zero ordinary center projection. -/
theorem laurentStabilizationCenterProjection_single_eq_zero
    (x : GridState (n + 1)) (hx : x s.succ ≠ (G.X s).succ) :
    laurentStabilizationCenterProjection G s R (single x 1) = 0 := by
  classical
  apply Finsupp.ext
  intro y
  rw [laurentStabilizationCenterProjection_apply, Finsupp.zero_apply]
  apply Finsupp.single_eq_of_ne
  intro h
  exact hx (by simpa using (congrArg (fun z : GridState (n + 1) => z s.succ) h).symm)

/-- A matching source is disjoint from the matching-target coefficient set. -/
theorem stabilizationMatchingTargetProjection_single_source
    (x : GridState (n + 1)) (hx : RowMatchingSource s (G.X s) x) :
    stabilizationMatchingTargetProjection G s R (single x 1) = 0 := by
  classical
  apply Finsupp.ext
  intro z
  rw [stabilizationMatchingTargetProjection_apply, Finsupp.zero_apply]
  apply Finsupp.single_eq_of_ne
  intro h
  exact stabilizationMatchingTarget_not_source G s z (h.symm ▸ hx)

/-- Center generators are disjoint from the noncritical matching targets. -/
theorem stabilizationMatchingTargetProjection_single_center (x : GridState n) :
    stabilizationMatchingTargetProjection G s R
      (single (x.insertPoint s.succ (G.X s).succ) 1) = 0 := by
  classical
  apply Finsupp.ext
  intro z
  rw [stabilizationMatchingTargetProjection_apply, Finsupp.zero_apply]
  apply Finsupp.single_eq_of_ne
  intro h
  exact stabilizationMatchingTarget_ne_center G s z
    (by simpa using congrArg (fun w : GridState (n + 1) => w s.succ) h)

variable [CharP R 2]

/-- The second component of the actual full comparison projection. -/
def stabilizationSecondProjection :
    LaurentChain R (n + 1) →ₗ[LaurentPolynomial R] LaurentChain R n :=
  LinearMap.snd (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
    (fullStabilizationTransferredRetraction G s R).proj

/-- Its values on the noncritical matching-target submodule. -/
def stabilizationMatchingSecondProjection :
    (StabilizationMatchingNode G s →₀ LaurentPolynomial R) →ₗ[LaurentPolynomial R]
      LaurentChain R n :=
  stabilizationSecondProjection G s R ∘ₗ stabilizationMatchingTargetInclusion G s R

/-- All matching sources have zero second full projection. -/
theorem stabilizationSecondProjection_single_source
    (x : GridState (n + 1)) (hx : RowMatchingSource s (G.X s) x) :
    stabilizationSecondProjection G s R (single x 1) = 0 := by
  let i : G.StabilizeXOffCenterState s := ⟨x, rowMatchingSource_ne_newRow s (G.X s) x hx⟩
  have hi : G.StabilizeXMatchingSource s (.inl i) :=
    (rowMatchingSource_coneState G s (.inl i)).mp (by simpa using hx)
  exact congrArg Prod.snd
    (fullStabilizationTransferredRetraction_proj_single_of_matching_source G s R i hi)

/-- The actual full second projection is its center part plus its matching-target part. -/
theorem stabilizationSecondProjection_decomposition :
    stabilizationSecondProjection G s R = laurentStabilizationCenterProjection G s R +
      stabilizationMatchingSecondProjection G s R ∘ₗ
        stabilizationMatchingTargetProjection G s R := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  change stabilizationSecondProjection G s R (single x 1) =
    laurentStabilizationCenterProjection G s R (single x 1) +
      stabilizationMatchingSecondProjection G s R
        (stabilizationMatchingTargetProjection G s R (single x 1))
  by_cases hc : x s.succ = (G.X s).succ
  · obtain ⟨y, rfl⟩ := GridState.exists_insertPoint_eq hc
    rw [stabilizationMatchingTargetProjection_single_center, map_zero, add_zero,
      ← laurentStabilizationCenterInclusion_single]
    change ((fullStabilizationTransferredRetraction G s R).proj
      (laurentStabilizationCenterInclusion G s R (single y 1))).2 = _
    rw [fullStabilizationTransferredRetraction_proj_centerInclusion]
    exact (LinearMap.congr_fun
      (laurentStabilizationCenterProjection_comp_inclusion G s R) (single y 1)).symm
  · by_cases hs : RowMatchingSource s (G.X s) x
    · rw [stabilizationSecondProjection_single_source G s R x hs,
        laurentStabilizationCenterProjection_single_eq_zero G s R x hc,
        stabilizationMatchingTargetProjection_single_source G s R x hs, map_zero, add_zero]
    · obtain ⟨z, rfl⟩ := exists_stabilizationMatchingTarget_of_not_source G s x hs hc
      rw [laurentStabilizationCenterProjection_single_eq_zero G s R _
        (stabilizationMatchingTarget_ne_center G s z),
        stabilizationMatchingTargetProjection_single, zero_add]
      change stabilizationSecondProjection G s R
          (single (stabilizationMatchingTargetState G s z) 1) =
        stabilizationSecondProjection G s R
          (stabilizationMatchingTargetInclusion G s R (single z 1))
      rw [stabilizationMatchingTargetInclusion_single]

end OnLeConjecture.KnotFloer.GridFull
