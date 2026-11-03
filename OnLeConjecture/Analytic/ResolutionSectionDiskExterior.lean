/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionCriticalDisks

/-! # Compact exterior of the chosen source coordinate disks

The complement of the open source disks is compact. It retains the outer
target boundary and intersects each removed closed disk exactly in its
coordinate circle. Its actual target-section map is a closed embedding
and has injective complex level tangent at every remaining point.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace ResolutionSectionLevel

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}

/-- The literal target cut with the open source coordinate disks removed. -/
def diskExterior (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (ε : ℝ) : Set CollarPlane :=
  targetSectionCut A.H L.radius ε L.parameter \ ⋃ j, (D j).openDisk

theorem diskExterior_eq_diff_open (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (ε : ℝ) :
    L.diskExterior D ε =
      targetSectionCut A.H L.radius ε L.parameter \ ⋃ j, (D j).ambientOpen := by
  ext z
  constructor
  · rintro ⟨hz, hnot⟩
    refine ⟨hz, ?_⟩
    intro hzU
    obtain ⟨j, hj⟩ := mem_iUnion.mp hzU
    apply hnot
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change z ∈ (D j).ψ '' ball 0 (D j).radius
    rw [(D j).open_image_eq]
    exact ⟨hj, hz.1.2⟩
  · rintro ⟨hz, hnot⟩
    refine ⟨hz, ?_⟩
    intro hmem
    obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
    apply hnot
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change z ∈ (D j).ψ '' ball 0 (D j).radius at hj
    rw [(D j).open_image_eq] at hj
    exact hj.1

theorem isCompact_diskExterior (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) {ε : ℝ}
    (hc : IsCompact (targetSectionCut A.H L.radius ε L.parameter)) :
    IsCompact (L.diskExterior D ε) := by
  rw [L.diskExterior_eq_diff_open D ε]
  exact hc.diff (isOpen_iUnion fun j => (D j).isOpen_ambientOpen)

/-- Removing these disks removes the complete enumerated critical set. -/
theorem not_mem_points_of_mem_diskExterior (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) {ε : ℝ} {z : CollarPlane}
    (hz : z ∈ L.diskExterior D ε) :
    (EuclideanSpace.equiv (Fin 2) ℂ) z ∉ L.points := by
  intro hj
  let j : L.points := ⟨(EuclideanSpace.equiv (Fin 2) ℂ) z, hj⟩
  apply hz.2
  apply mem_iUnion.mpr
  refine ⟨j, ?_⟩
  simpa only [j, ContinuousLinearEquiv.symm_apply_apply] using (D j).center_mem_openDisk

/-- Pairwise disjoint closed disks meet the exterior in exactly their
coordinate circles, provided they lie in the original target cut. -/
theorem diskExterior_inter_closedDisk (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) {ε : ℝ}
    (hdisj : Pairwise (fun j k => Disjoint (D j).closedDisk (D k).closedDisk))
    (hD : ∀ j, (D j).closedDisk ⊆ targetSectionCut A.H L.radius ε L.parameter)
    (j : L.points) : L.diskExterior D ε ∩ (D j).closedDisk = (D j).boundaryCircle := by
  rw [← (D j).closedDisk_diff_openDisk]
  ext z
  constructor
  · rintro ⟨hz, hzD⟩
    exact ⟨hzD, fun h => hz.2 (mem_iUnion.mpr ⟨j, h⟩)⟩
  · rintro ⟨hzD, hznot⟩
    refine ⟨⟨hD j hzD, ?_⟩, hzD⟩
    intro hzU
    obtain ⟨k, hk⟩ := mem_iUnion.mp hzU
    by_cases hkj : k = j
    · subst k
      exact hznot hk
    · exact Set.disjoint_left.mp (hdisj (Ne.symm hkj)) hzD
        ((D k).openDisk_subset_closedDisk hk)

/-- The chosen inner disks do not remove any point of the outer target boundary. -/
theorem targetSectionBoundary_subset_diskExterior (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) {ε η : ℝ} (hε : 0 ≤ ε) (hηε : η ≤ ε)
    (hD : ∀ j, ∀ z ∈ (D j).closedDisk,
      ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm
        (A.H ((EuclideanSpace.equiv (Fin 2) ℂ) z))‖ < η) :
    targetSectionBoundary A.H L.radius ε L.parameter ⊆ L.diskExterior D ε := by
  intro z hz
  refine ⟨(mem_targetSectionCut_iff hε).mpr ⟨hz.1, hz.2.le⟩, ?_⟩
  intro hzU
  obtain ⟨j, hj⟩ := mem_iUnion.mp hzU
  have hlt := hD j z ((D j).openDisk_subset_closedDisk hj)
  rw [hz.2] at hlt
  exact (not_lt_of_ge hηε) hlt

/-- The exterior retains the proved complex rank-one immersion into the
actual target section. Its source-domain condition is explicit. -/
theorem diskExterior_tangent_properties (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) {ε : ℝ}
    (ha : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius))
    (hinside : ∀ z ∈ targetSectionCut A.H L.radius ε L.parameter,
      (EuclideanSpace.equiv (Fin 2) ℂ) z ∈ ball 0 L.radius)
    {z : CollarPlane} (hz : z ∈ L.diskExterior D ε) :
    let x := (EuclideanSpace.equiv (Fin 2) ℂ) z
    AnalyticAt ℂ A.sectionMap x ∧
      fderiv ℂ (fun y => A.H y 0) x ≠ 0 ∧
      Injective (L.sectionTangentMap x) ∧
      Module.finrank ℂ (LinearMap.range (L.sectionTangentMap x)) = 1 := by
  exact L.exterior_tangent_properties ha (U := (L.points : Set (Source 2))) subset_rfl
    ⟨⟨hinside z hz.1, hz.1.1.2⟩, L.not_mem_points_of_mem_diskExterior D hz⟩

/-- The actual Euclidean target-section map is a closed embedding of the
compact exterior. This is a topological statement; immersion is supplied
separately by diskExterior_tangent_properties. -/
theorem diskExterior_closedEmbedding (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) {ε : ℝ}
    (ha : AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius))
    (hc : IsCompact (targetSectionCut A.H L.radius ε L.parameter)) :
    Topology.IsClosedEmbedding ((L.diskExterior D ε).domRestrict (euclideanSectionMap A.H)) := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  have : CompactSpace ↥(L.diskExterior D ε) :=
    isCompact_iff_compactSpace.mp (L.isCompact_diskExterior D hc)
  have hcont : Continuous ((L.diskExterior D ε).domRestrict (euclideanSectionMap A.H)) := by
    apply ContinuousOn.domRestrict
    intro z hz
    exact (((e.symm.analyticAt _).comp
      (((hyperplaneTail 2).analyticAt _).comp
        ((ha (e z) hz.1.1.1).comp (e.analyticAt z)))).continuousAt).continuousWithinAt
  apply hcont.isClosedEmbedding
  intro z w hzw
  apply Subtype.ext
  apply e.injective
  have hzL : e z ∈ L.sourceLevel := z.property.1.1
  have hwL : e w ∈ L.sourceLevel := w.property.1.1
  apply L.sectionMap_injOn hzL hwL
  have he := congrArg e hzw
  simpa only [e, Set.domRestrict_apply, euclideanSectionMap,
    ContinuousLinearEquiv.apply_symm_apply, ResolutionSectionAssembly.sectionMap] using he

end ResolutionSectionLevel

end OnLeConjecture.Analytic
