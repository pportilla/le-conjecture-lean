/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionTargetCommonLevel

/-! # Coordinate disks in a regular source level

These disks belong to the smooth source level. Their construction makes no
smooth embedding assertion for their images under the singular target map.
The disk interior is an explicit relatively open subset of the level.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff

namespace OnLeConjecture.Analytic

/-- A closed coordinate disk in a complex regular level, with its open
interior expressed using an ambient open set. -/
structure PlaneLevelCoordinateDisk (f : CollarPlane → ℂ) (s : ℂ) (z : CollarPlane) where
  radius : ℝ
  radius_pos : 0 < radius
  W : Set ℂ
  isOpen_W : IsOpen W
  closedBall_subset : closedBall 0 radius ⊆ W
  ψ : ℂ → CollarPlane
  coordinate : CollarPlane →L[ℂ] ℂ
  ψ_zero : ψ 0 = z
  analytic : AnalyticOnNhd ℂ ψ W
  level_eq : ∀ u ∈ W, f (ψ u) = s
  left_inverse : ∀ u ∈ W, coordinate (ψ u - z) = u
  ambientOpen : Set CollarPlane
  isOpen_ambientOpen : IsOpen ambientOpen
  open_image_eq : ψ '' ball 0 radius = ambientOpen ∩ {w | f w = s}

namespace PlaneLevelCoordinateDisk

variable {f : CollarPlane → ℂ} {s : ℂ} {z : CollarPlane}

def closedDisk (D : PlaneLevelCoordinateDisk f s z) : Set CollarPlane :=
  D.ψ '' closedBall 0 D.radius

def openDisk (D : PlaneLevelCoordinateDisk f s z) : Set CollarPlane :=
  D.ψ '' ball 0 D.radius

def boundaryCircle (D : PlaneLevelCoordinateDisk f s z) : Set CollarPlane :=
  D.ψ '' sphere 0 D.radius

theorem injOn (D : PlaneLevelCoordinateDisk f s z) : InjOn D.ψ D.W := by
  intro u hu v hv huv
  rw [← D.left_inverse u hu, ← D.left_inverse v hv, huv]

theorem center_mem_openDisk (D : PlaneLevelCoordinateDisk f s z) : z ∈ D.openDisk :=
  ⟨0, mem_ball_self D.radius_pos, D.ψ_zero⟩

theorem openDisk_subset_closedDisk (D : PlaneLevelCoordinateDisk f s z) :
    D.openDisk ⊆ D.closedDisk := image_mono ball_subset_closedBall

theorem closedDisk_subset_level (D : PlaneLevelCoordinateDisk f s z) :
    D.closedDisk ⊆ {w | f w = s} := by
  rintro w ⟨u, hu, rfl⟩
  exact D.level_eq u (D.closedBall_subset hu)

theorem isCompact_closedDisk (D : PlaneLevelCoordinateDisk f s z) : IsCompact D.closedDisk :=
  (isCompact_closedBall (0 : ℂ) D.radius).image_of_continuousOn
    (D.analytic.continuousOn.mono D.closedBall_subset)

/-- The closed disk is genuinely homeomorphic to a complex coordinate disk. -/
def closedDiskHomeomorph (D : PlaneLevelCoordinateDisk f s z) :
    closedBall (0 : ℂ) D.radius ≃ₜ D.closedDisk where
  toFun u := ⟨D.ψ u, mem_image_of_mem _ u.property⟩
  invFun w := ⟨D.coordinate (w - z), by
    obtain ⟨u, hu, he⟩ := w.property
    rw [← he, D.left_inverse u (D.closedBall_subset hu)]
    exact hu⟩
  left_inv u := Subtype.ext (D.left_inverse u (D.closedBall_subset u.property))
  right_inv w := by
    apply Subtype.ext
    obtain ⟨u, hu, he⟩ := w.property
    change D.ψ (D.coordinate (w - z)) = w
    rw [← he, D.left_inverse u (D.closedBall_subset hu)]
  continuous_toFun :=
    (D.analytic.continuousOn.mono D.closedBall_subset).domRestrict.subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact D.coordinate.continuous.comp (continuous_subtype_val.sub continuous_const)

theorem closedDisk_diff_openDisk (D : PlaneLevelCoordinateDisk f s z) :
    D.closedDisk \ D.openDisk = D.boundaryCircle := by
  ext w
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, hnot⟩
    have hnu : u ∉ ball (0 : ℂ) D.radius := fun h => hnot ⟨u, h, rfl⟩
    exact ⟨u, mem_sphere_zero_iff_norm.mpr
      (le_antisymm (mem_closedBall_zero_iff.mp hu) (not_lt.mp (by
        simpa only [mem_ball_zero_iff] using hnu))), rfl⟩
  · rintro ⟨u, hu, rfl⟩
    have huc : u ∈ closedBall (0 : ℂ) D.radius := sphere_subset_closedBall hu
    refine ⟨⟨u, huc, rfl⟩, ?_⟩
    rintro ⟨v, hv, he⟩
    have hvu := D.injOn (D.closedBall_subset (ball_subset_closedBall hv))
      (D.closedBall_subset huc) he
    have hlt := mem_ball_zero_iff.mp hv
    rw [hvu, mem_sphere_zero_iff_norm.mp hu] at hlt
    exact lt_irrefl _ hlt

/-- The holomorphic coordinate map is an immersion on a neighborhood of
the entire closed disk. -/
theorem immersion (D : PlaneLevelCoordinateDisk f s z) {u : ℂ} (hu : u ∈ D.W) :
    Injective (fderiv ℝ D.ψ u) := by
  refine injective_fderiv_of_leftInverse ((D.analytic u hu).differentiableAt.restrictScalars ℝ)
    (((D.coordinate.restrictScalars ℝ).differentiableAt.comp _
      (differentiableAt_id.sub_const z))) ?_
  filter_upwards [D.isOpen_W.mem_nhds hu] with v hv using D.left_inverse v hv

end PlaneLevelCoordinateDisk

/-- A regular holomorphic level has a coordinate disk inside every prescribed
ambient neighborhood of its center. -/
theorem exists_planeLevelCoordinateDisk (f : CollarPlane → ℂ) {s : ℂ} {z : CollarPlane}
    (hf : AnalyticAt ℂ f z) (hfs : f z = s) (hd : fderiv ℂ f z ≠ 0)
    {S : Set CollarPlane} (hS : S ∈ 𝓝 z) :
    ∃ D : PlaneLevelCoordinateDisk f s z, D.closedDisk ⊆ S := by
  obtain ⟨ℓ, ψ, U, N, hU, h0U, hN, hzN, hψ0, hψan, hψF, hψℓ, hloc, _⟩ :=
    exists_levelParametrization f hf hd
  have hnear : ∀ᶠ u in 𝓝 (0 : ℂ), u ∈ U ∧ ψ u ∈ N ∧ ψ u ∈ S := by
    have ht : Tendsto ψ (𝓝 0) (𝓝 z) := hψ0 ▸ (hψan 0 h0U).continuousAt.tendsto
    filter_upwards [hU.mem_nhds h0U, ht.eventually (hN.mem_nhds hzN), ht.eventually hS]
      with u hu hn hs using ⟨hu, hn, hs⟩
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnear
  let a := r / 2
  have ha : 0 < a := half_pos hr
  have hclosed : closedBall (0 : ℂ) a ⊆ ball 0 r := closedBall_subset_ball (half_lt_self hr)
  let O : Set CollarPlane := N ∩ (fun w => ℓ (w - z)) ⁻¹' ball 0 a
  have hO : IsOpen O := hN.inter (isOpen_ball.preimage (by fun_prop))
  have hopen : ψ '' ball (0 : ℂ) a = O ∩ {w | f w = s} := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hs := hrsub (hclosed (ball_subset_closedBall hu))
      refine ⟨⟨hs.2.1, ?_⟩, (hψF u hs.1).trans hfs⟩
      change ℓ (ψ u - z) ∈ ball 0 a
      rw [hψℓ u hs.1]
      exact hu
    · rintro ⟨⟨hwN, hwball⟩, hfw⟩
      obtain ⟨_, he⟩ := hloc w hwN (hfw.trans hfs.symm)
      exact ⟨ℓ (w - z), hwball, he⟩
  let D : PlaneLevelCoordinateDisk f s z :=
    ⟨a, ha, U, hU, fun u hu => (hrsub (hclosed hu)).1, ψ, ℓ, hψ0, hψan,
      fun u hu => (hψF u hu).trans hfs, hψℓ, O, hO, hopen⟩
  refine ⟨D, ?_⟩
  rintro w ⟨u, hu, rfl⟩
  exact (hrsub (hclosed hu)).2.2

end OnLeConjecture.Analytic
