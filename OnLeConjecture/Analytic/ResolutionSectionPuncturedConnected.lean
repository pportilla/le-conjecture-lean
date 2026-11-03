/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionPuncturedCharts
public import OnLeConjecture.Analytic.PlaneMilnorFibrePath
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Normed.Module.Connected

/-! # Path connectedness of the punctured section

Under `L.ExteriorHypotheses D ε`, the punctured section `L.diskExterior D ε`
is path connected, and hence its rational homology in degree zero is
one-dimensional.

Connectedness follows from the path connectedness of the target cut. The cut
is the union of the punctured section and of the pairwise disjoint closed
disks, and each closed disk meets the punctured section exactly in its hole
circle, which is connected. Local path connectedness follows from the local
charts of `ResolutionSectionPuncturedCharts`: interior points have small
coordinate disks, and boundary points have small upper half-discs in oriented
radius charts.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ OnLeConjecture.DifferentialTopology

namespace SectionRadiusBoundaryChart

variable {f : CollarPlane → ℂ} {ρ : CollarPlane → ℝ} {O : Set CollarPlane} {z : CollarPlane}

/-- Suppose that a set `E` lies in the level `{w | f w = f z}` and meets the
image of a radius chart centered at `z` exactly in the image of the closed
upper half-plane. Then every neighbourhood `S` of `z` contains a path
connected subset of `E` that is a neighbourhood of `z` in `E`. -/
theorem exists_isPathConnected_mem_nhdsWithin (C : SectionRadiusBoundaryChart f ρ O z)
    (hO : IsOpen O) {E : Set CollarPlane} (hEf : ∀ w ∈ E, f w = f z)
    (hE : ∀ t ∈ C.W, C.φ t ∈ E ↔ 0 ≤ t.im) {S : Set CollarPlane} (hS : S ∈ 𝓝 z) :
    ∃ V ⊆ E ∩ S, V ∈ 𝓝[E] z ∧ IsPathConnected V := by
  have hφ : ContinuousAt C.φ 0 :=
    C.smooth.continuousOn.continuousAt (C.isOpen_W.mem_nhds C.zero_mem)
  have hW : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ C.W := C.isOpen_W.mem_nhds C.zero_mem
  have hφS : ∀ᶠ t in 𝓝 (0 : ℂ), C.φ t ∈ S :=
    hφ.preimage_mem_nhds (by rw [C.φ_zero]; exact hS)
  obtain ⟨τ, hτ, hball⟩ := Metric.eventually_nhds_iff.mp (hW.and hφS)
  let M : Set ℂ := ball 0 τ ∩ {t | 0 ≤ t.im}
  have hMW : M ⊆ C.W := fun t ht => (hball ht.1).1
  have hMpc : IsPathConnected M :=
    ((convex_ball 0 τ).inter (convex_halfSpace_im_ge 0)).isPathConnected
      ⟨0, mem_ball_self hτ, le_of_eq Complex.zero_im.symm⟩
  refine ⟨C.φ '' M, ?_, ?_, hMpc.image' (C.smooth.continuousOn.mono hMW)⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨(hE t (hMW ht)).mpr ht.2, (hball ht.1).2⟩
  · have hzO : z ∈ O := by
      rw [← C.φ_zero]
      exact C.mapsTo C.zero_mem
    have hχc : ContinuousAt C.χ z :=
      C.inverse_smooth.continuousOn.continuousAt (hO.mem_nhds hzO)
    have hχz : C.χ z = 0 := by
      have h := C.left_inverse 0 C.zero_mem
      rwa [C.φ_zero] at h
    have hχball : ∀ᶠ w in 𝓝 z, C.χ w ∈ ball (0 : ℂ) τ :=
      hχc.preimage_mem_nhds (by rw [hχz]; exact ball_mem_nhds 0 hτ)
    filter_upwards [(C.local_inverse.and hχball).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hw hwE
    obtain ⟨hwW, he⟩ := hw.1 (hEf w hwE)
    refine ⟨C.χ w, ⟨hw.2, (hE _ hwW).mp ?_⟩, he⟩
    rw [he]
    exact hwE

end SectionRadiusBoundaryChart

namespace PlaneLevelCoordinateDisk

variable {f : CollarPlane → ℂ} {s : ℂ} {z : CollarPlane}

theorem isConnected_boundaryCircle (D : PlaneLevelCoordinateDisk f s z) :
    IsConnected D.boundaryCircle :=
  (isConnected_sphere (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat) (0 : ℂ)
    D.radius_pos.le).image _
    (D.analytic.continuousOn.mono (sphere_subset_closedBall.trans D.closedBall_subset))

theorem isPathConnected_openDisk (D : PlaneLevelCoordinateDisk f s z) :
    IsPathConnected D.openDisk :=
  ((convex_ball (0 : ℂ) D.radius).isPathConnected ⟨0, mem_ball_self D.radius_pos⟩).image'
    (D.analytic.continuousOn.mono (ball_subset_closedBall.trans D.closedBall_subset))

end PlaneLevelCoordinateDisk

namespace ResolutionSectionLevel

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}

/-- The critical list of a nearby level is nonempty. -/
theorem nonempty_points (L : ResolutionSectionLevel A) : Nonempty L.points := by
  have hcard : 0 < L.points.card := L.card_eq ▸ A.count_pos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard
  exact ⟨⟨x, hx⟩⟩

namespace ExteriorHypotheses

variable {L : ResolutionSectionLevel A} {D : (j : L.points) → L.PointCoordinateDisk j}
  {ε : ℝ}

/-- **Connectedness of the punctured section.** -/
theorem isConnected_diskExterior (hL : L.ExteriorHypotheses D ε) :
    IsConnected (L.diskExterior D ε) := by
  obtain ⟨j₀⟩ := L.nonempty_points
  refine ⟨((D j₀).isConnected_boundaryCircle.nonempty).mono
    (hL.boundaryCircle_subset_diskExterior j₀), ?_⟩
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hcover hEt hEt'
  by_contra hempty
  have hno : ∀ w ∈ L.diskExterior D ε, w ∈ t → w ∉ t' :=
    fun w hw h1 h2 => hempty ⟨w, hw, h1, h2⟩
  have hcirc := hL.boundaryCircle_subset_diskExterior
  -- A hole circle meeting `t` lies in `t`.
  have hmix : ∀ k, ((D k).boundaryCircle ∩ t).Nonempty → (D k).boundaryCircle ⊆ t := by
    rintro k ⟨w, hwc, hwt⟩
    by_contra hns
    obtain ⟨v, hvc, hvt⟩ := not_subset.mp hns
    have hvt' : v ∈ t' := (hcover (hcirc k hvc)).resolve_left hvt
    obtain ⟨x, hxc, hxt, hxt'⟩ := isPreconnected_closed_iff.mp
      (D k).isConnected_boundaryCircle.isPreconnected t t' ht ht'
      ((hcirc k).trans hcover) ⟨w, hwc, hwt⟩ ⟨v, hvc, hvt'⟩
    exact hno x (hcirc k hxc) hxt hxt'
  let T : Set CollarPlane := (L.diskExterior D ε ∩ t) ∪
    ⋃ k ∈ {k | (D k).boundaryCircle ⊆ t}, (D k).closedDisk
  let T' : Set CollarPlane := (L.diskExterior D ε ∩ t') ∪
    ⋃ k ∈ {k | ¬ (D k).boundaryCircle ⊆ t}, (D k).closedDisk
  have hT : IsClosed T := (hL.isClosed_diskExterior.inter ht).union
    ((Set.toFinite _).isClosed_biUnion fun k _ => (D k).isCompact_closedDisk.isClosed)
  have hT' : IsClosed T' := (hL.isClosed_diskExterior.inter ht').union
    ((Set.toFinite _).isClosed_biUnion fun k _ => (D k).isCompact_closedDisk.isClosed)
  have hcutcover : targetSectionCut A.H L.radius ε L.parameter ⊆ T ∪ T' := by
    rw [hL.cut_eq_union]
    rintro w (hw | hw)
    · rcases hcover hw with hwt | hwt'
      · exact Or.inl (Or.inl ⟨hw, hwt⟩)
      · exact Or.inr (Or.inl ⟨hw, hwt'⟩)
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hw
      by_cases hkt : (D k).boundaryCircle ⊆ t
      · exact Or.inl (Or.inr (mem_biUnion (x := k) hkt hk))
      · exact Or.inr (Or.inr (mem_biUnion (x := k) hkt hk))
  obtain ⟨w, hw⟩ := hEt
  obtain ⟨w', hw'⟩ := hEt'
  obtain ⟨x, -, hxT, hxT'⟩ := isPreconnected_closed_iff.mp
    hL.cut_pathConnected.isConnected.isPreconnected T T' hT hT' hcutcover
    ⟨w, hw.1.1, Or.inl hw⟩ ⟨w', hw'.1.1, Or.inl hw'⟩
  rcases hxT with hxE | hxD <;> rcases hxT' with hxE' | hxD'
  · exact hno x hxE.1 hxE.2 hxE'.2
  · obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hxD'
    have hxc : x ∈ (D k).boundaryCircle := by
      rw [← hL.diskExterior_inter_closedDisk k]
      exact ⟨hxE.1, hxk⟩
    exact hk (hmix k ⟨x, hxc, hxE.2⟩)
  · obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hxD
    have hxc : x ∈ (D k).boundaryCircle := by
      rw [← hL.diskExterior_inter_closedDisk k]
      exact ⟨hxE'.1, hxk⟩
    exact hno x hxE'.1 (hk hxc) hxE'.2
  · obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hxD
    obtain ⟨k', hk', hxk'⟩ := mem_iUnion₂.mp hxD'
    have hkk : k ≠ k' := by
      rintro rfl
      exact hk' hk
    exact Set.disjoint_left.mp (hL.disjoint hkk) hxk hxk'

/-- Every neighbourhood `S` of a point `z` of the punctured section contains a
path connected subset of the punctured section that is a neighbourhood of `z`
in the punctured section. -/
theorem exists_isPathConnected_mem_nhdsWithin (hL : L.ExteriorHypotheses D ε)
    {z : CollarPlane} (hz : z ∈ L.diskExterior D ε) {S : Set CollarPlane} (hS : S ∈ 𝓝 z) :
    ∃ V ⊆ L.diskExterior D ε ∩ S, V ∈ 𝓝[L.diskExterior D ε] z ∧ IsPathConnected V := by
  have hEf : ∀ w ∈ L.diskExterior D ε, euclideanEquation (fun x => A.H x 0) w =
      euclideanEquation (fun x => A.H x 0) z :=
    fun w hw => hw.1.1.2.trans hz.1.1.2.symm
  by_cases hzb : z ∈ L.exteriorBoundary D ε
  · rcases hzb with hzb | hzb
    · obtain ⟨O, hO, -, C, hE, -⟩ := hL.exists_outerChart hzb
      exact C.exists_isPathConnected_mem_nhdsWithin hO hEf hE hS
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hzb
      obtain ⟨O, hO, -, C, hE, -⟩ := hL.exists_holeChart j hj
      exact C.exists_isPathConnected_mem_nhdsWithin hO hEf hE hS
  · obtain ⟨C, hCsub, hCn⟩ := hL.exists_interiorChart hz hzb hS
    exact ⟨C.openDisk, C.openDisk_subset_closedDisk.trans hCsub, hCn,
      C.isPathConnected_openDisk⟩

/-- **Local path connectedness of the punctured section.** -/
theorem locallyPathConnectedSpace (hL : L.ExteriorHypotheses D ε) :
    LocallyPathConnectedSpace ↥(L.diskExterior D ε) := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  rintro ⟨z, hz⟩ u hu hzu
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨V, hVsub, hVn, hVpc⟩ := hL.exists_isPathConnected_mem_nhdsWithin hz (hO.mem_nhds hzu)
  have hzV : z ∈ V := mem_of_mem_nhdsWithin hz hVn
  apply Filter.mem_of_superset (preimage_coe_mem_nhds_subtype.mpr hVn)
  exact (hVpc.preimage_coe fun w hw => (hVsub hw).1).subset_pathComponentIn hzV
    fun w hw => (hVsub hw).2

/-- **Path connectedness of the punctured section.** -/
theorem isPathConnected_diskExterior (hL : L.ExteriorHypotheses D ε) :
    IsPathConnected (L.diskExterior D ε) := by
  have := hL.locallyPathConnectedSpace
  have hc : ConnectedSpace ↥(L.diskExterior D ε) :=
    isConnected_iff_connectedSpace.mp hL.isConnected_diskExterior
  exact isPathConnected_iff_pathConnectedSpace.mpr (pathConnectedSpace_iff_connectedSpace.mpr hc)

/-- The rational homology of the punctured section in degree zero is
one-dimensional. -/
theorem finrank_ratH_zero_diskExterior (hL : L.ExteriorHypotheses D ε) :
    Module.Finite ℚ (ratH ↥(L.diskExterior D ε) 0) ∧
      Module.finrank ℚ (ratH ↥(L.diskExterior D ε) 0) = 1 := by
  have := isPathConnected_iff_pathConnectedSpace.mp hL.isPathConnected_diskExterior
  exact finrank_ratH_zero_of_pathConnected

end ExteriorHypotheses

end ResolutionSectionLevel

end OnLeConjecture.Analytic
