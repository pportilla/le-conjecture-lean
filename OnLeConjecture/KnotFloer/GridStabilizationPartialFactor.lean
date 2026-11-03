/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationLocalRetraction

/-!
# Splitting the partially blocked stabilization

The crossing comparison annihilates the connecting component of the differential.
This is the concrete block identity needed to split the stabilization before the
remaining two X crossings are restored.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R]

/-- The already defined center inclusion is the map of finitely supported functions on states. -/
theorem laurentStabilizationCenterInclusion_eq_lmapDomain :
    laurentStabilizationCenterInclusion G s R =
      Finsupp.lmapDomain (LaurentPolynomial R) (LaurentPolynomial R)
        (fun x : GridState n => x.insertPoint s.succ (G.X s).succ) := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  change laurentStabilizationCenterInclusion G s R (single x 1) =
    Finsupp.mapDomain (fun x => x.insertPoint s.succ (G.X s).succ) (single x 1)
  rw [laurentStabilizationCenterInclusion_single, Finsupp.mapDomain_single]

/-- A center inclusion has no off-center coefficients. -/
theorem laurentOffCenterProjection_centerInclusion (c : LaurentChain R n) :
    laurentOffCenterProjection G s R (laurentStabilizationCenterInclusion G s R c) = 0 := by
  rw [laurentStabilizationCenterInclusion_eq_lmapDomain]
  apply Finsupp.ext
  intro y
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨x, hx⟩
  exact y.2 (hx ▸ GridState.insertPoint_apply_newColumn _ _ _)

/-- An off-center inclusion has no center coefficients. -/
theorem laurentStabilizationCenterProjection_offCenterInclusion
    (c : G.StabilizeXOffCenterState s →₀ LaurentPolynomial R) :
    laurentStabilizationCenterProjection G s R (laurentOffCenterInclusion G s R c) = 0 := by
  apply Finsupp.ext
  intro x
  rw [laurentStabilizationCenterProjection_apply]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨y, hy⟩
  exact y.2 (hy ▸ GridState.insertPoint_apply_newColumn _ _ _)

/-- Every stabilized chain is the sum of its center and off-center parts. -/
theorem laurentStabilizationCenter_add_offCenter (c : LaurentChain R (n + 1)) :
    laurentStabilizationCenterInclusion G s R (laurentStabilizationCenterProjection G s R c) +
      laurentOffCenterInclusion G s R (laurentOffCenterProjection G s R c) = c := by
  classical
  apply Finsupp.ext
  intro y
  rw [Finsupp.add_apply]
  by_cases hy : y s.succ = (G.X s).succ
  · obtain ⟨x, rfl⟩ := GridState.exists_insertPoint_eq hy
    have hN := congrArg (fun v => v x)
      (laurentStabilizationCenterProjection_offCenterInclusion G s R
        (laurentOffCenterProjection G s R c))
    rw [laurentStabilizationCenterProjection_apply, Finsupp.zero_apply] at hN
    have hI := congrArg (fun v => v x) (LinearMap.congr_fun
      (laurentStabilizationCenterProjection_comp_inclusion G s R)
      (laurentStabilizationCenterProjection G s R c))
    simpa only [LinearMap.comp_apply, LinearMap.id_apply,
      laurentStabilizationCenterProjection_apply, hN, add_zero] using hI
  · have hI := congrArg (fun v => v ⟨y, hy⟩)
      (laurentOffCenterProjection_centerInclusion G s R
        (laurentStabilizationCenterProjection G s R c))
    rw [laurentOffCenterProjection_apply, Finsupp.zero_apply] at hI
    have hN := congrArg (fun v => v ⟨y, hy⟩)
      (laurentOffCenterProjection_inclusion G s R (laurentOffCenterProjection G s R c))
    simpa only [laurentOffCenterProjection_apply, hI, zero_add] using hN

/-- The connecting block from center chains to off-center chains. -/
noncomputable def localStabilizationConnecting : LaurentChain R n →ₗ[LaurentPolynomial R]
    (G.StabilizeXOffCenterState s →₀ LaurentPolynomial R) :=
  laurentOffCenterProjection G s R ∘ₗ
    laurentXBlockedDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
      R {s.castSucc, s.succ} ∘ₗ laurentStabilizationCenterInclusion G s R

/-- The differential of an included center chain has its stated two components. -/
theorem localStabilizationDifferential_centerInclusion (c : LaurentChain R n) :
    laurentXBlockedDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
        R {s.castSucc, s.succ} (laurentStabilizationCenterInclusion G s R c) =
      laurentStabilizationCenterInclusion G s R (laurentXBlockedDifferential G R {s} c) +
        laurentOffCenterInclusion G s R (localStabilizationConnecting G s R c) := by
  have hd := LinearMap.congr_fun (laurentStabilizationCenterProjection_xBlocked_chain G s R)
    (laurentStabilizationCenterInclusion G s R c)
  have hP := LinearMap.congr_fun (laurentStabilizationCenterProjection_comp_inclusion G s R) c
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hd hP
  rw [hP] at hd
  have h := (laurentStabilizationCenter_add_offCenter G s R
    (laurentXBlockedDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
      R {s.castSucc, s.succ} (laurentStabilizationCenterInclusion G s R c))).symm
  rw [hd] at h
  exact h

/-- The selected crossing has no center-to-center term. -/
theorem localComparisonCrossing_centerInclusion (c : LaurentChain R n) :
    laurentStabilizationCenterProjection G s R
      (localComparisonCrossing G s R (laurentStabilizationCenterInclusion G s R c)) = 0 := by
  classical
  have hmap : laurentStabilizationCenterProjection G s R ∘ₗ localComparisonCrossing G s R ∘ₗ
      laurentStabilizationCenterInclusion G s R = 0 := by
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    apply Finsupp.ext
    intro y
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply,
      Finsupp.zero_apply, laurentStabilizationCenterProjection_apply,
      laurentStabilizationCenterInclusion_single, localComparisonCrossing,
      xBlockedCrossingHomotopy_apply_apply, Finsupp.sum_single_index, zero_mul, one_mul]
    apply Finset.sum_eq_zero
    intro r hr
    obtain ⟨he, hb, _⟩ := Finset.mem_filter.mp hr
    exact False.elim (stabilizationCenterRectangle_avoids_newX G s r
      ((GridRectangleBetween.mem_emptyRectangles r).mp he) ⟨s.succ, by simp, hb⟩)
  exact LinearMap.congr_fun hmap c

variable [CharP R 2]

/-- The forward crossing comparison annihilates the actual connecting block. -/
theorem localComparisonForward_connecting :
    localComparisonOffCenterToCenter G s R ∘ₗ localStabilizationConnecting G s R = 0 := by
  apply LinearMap.ext
  intro c
  have h := congrArg (laurentStabilizationCenterProjection G s R)
    (LinearMap.congr_fun (localComparisonCrossing_chain G s R)
      (laurentStabilizationCenterInclusion G s R c))
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply,
    map_add, map_zero] at h
  have hD := LinearMap.congr_fun (laurentStabilizationCenterProjection_xBlocked_chain G s R)
    (localComparisonCrossing G s R (laurentStabilizationCenterInclusion G s R c))
  simp only [LinearMap.comp_apply] at hD
  rw [hD, localComparisonCrossing_centerInclusion, map_zero, zero_add,
    localStabilizationDifferential_centerInclusion, map_add, map_add,
    localComparisonCrossing_centerInclusion, zero_add] at h
  exact h

end OnLeConjecture.KnotFloer.GridFull
