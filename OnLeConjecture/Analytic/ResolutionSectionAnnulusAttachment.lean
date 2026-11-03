/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionLocalAnnuli

/-! # Attaching the local annuli to the disk exterior

For a family of local annuli `Λ` we attach to the compact disk exterior `E`
the source annuli `ψ_j({r u | ρ_j(u) ≤ r ≤ R_j})` inside the removed coordinate
disks. The attached surface lies in the target cut, is compact, and its section
image is the union of the section image of `E` with the local annuli. The
radial deformation pushing each source annulus onto its outer coordinate
circle is a strong deformation retraction onto `E`, so the inclusion of `E`
is a homotopy equivalence. Rational homology and path connectedness transfer
from `E` to the attached surface. Finally, a point of the attached surface has
a neighborhood in the level contained in the attached surface exactly when it
lies neither on the outer target boundary nor on one of the inner circles
`ψ_j(ρ_j(u) u)`, so the old hole circles become interior points.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff Manifold

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ OnLeConjecture.DifferentialTopology

/-- The parameter annulus `{r u | u ∈ S¹, ρ(u) ≤ r ≤ R}` in a disk coordinate,
parametrized by the linear interpolation `annulusRadius`. -/
def annulusParameters (R : ℝ) (ρ : Circle → ℝ) : Set ℂ :=
  range (fun p : unitInterval × Circle => annulusRadius R ρ ((p.1 : ℝ), p.2) • (p.2 : ℂ))

theorem circleExp_arg_smul {r : ℝ} (hr : 0 < r) (w : ℂ) :
    Circle.exp (Complex.arg (r • w)) = Circle.exp (Complex.arg w) := by
  rw [Complex.real_smul, Complex.arg_real_mul _ hr]

/-- A point lies in the parameter annulus if and only if its norm lies between
the value of `ρ` at its direction and `R`. -/
theorem mem_annulusParameters_iff {R : ℝ} {ρ : Circle → ℝ} (hρ : ∀ u, 0 < ρ u)
    (hρR : ∀ u, ρ u < R) {v : ℂ} :
    v ∈ annulusParameters R ρ ↔ ρ (Circle.exp (Complex.arg v)) ≤ ‖v‖ ∧ ‖v‖ ≤ R := by
  constructor
  · rintro ⟨⟨t, u⟩, rfl⟩
    have hr := annulusRadius_pos hρ hρR t.2 u
    rw [circleExp_arg_smul hr, Circle.exp_arg, norm_annulusRadius_smul hρ hρR t.2 u]
    exact annulusRadius_bounds hρR t.2 u
  · rintro ⟨h₁, h₂⟩
    have hgap : 0 < R - ρ (Circle.exp (Complex.arg v)) := sub_pos.mpr (hρR _)
    let t : ℝ := (R - ‖v‖) / (R - ρ (Circle.exp (Complex.arg v)))
    have ht : t ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (sub_nonneg.mpr h₂) hgap.le, (div_le_one hgap).mpr (by linarith)⟩
    refine ⟨(⟨t, ht⟩, Circle.exp (Complex.arg v)), ?_⟩
    have hrad : annulusRadius R ρ (t, Circle.exp (Complex.arg v)) = ‖v‖ := by
      simp only [annulusRadius, t]
      field_simp
      ring
    change annulusRadius R ρ (t, Circle.exp (Complex.arg v)) •
      (Circle.exp (Complex.arg v) : ℂ) = v
    rw [hrad]
    exact norm_smul_circleExp_arg v

theorem annulusParameters_subset_closedBall {R : ℝ} {ρ : Circle → ℝ} (hρ : ∀ u, 0 < ρ u)
    (hρR : ∀ u, ρ u < R) : annulusParameters R ρ ⊆ closedBall 0 R := by
  rintro _ ⟨⟨t, u⟩, rfl⟩
  exact annulusRadius_smul_mem_closedBall hρ hρR t.2 u

theorem ne_zero_of_mem_annulusParameters {R : ℝ} {ρ : Circle → ℝ} (hρ : ∀ u, 0 < ρ u)
    (hρR : ∀ u, ρ u < R) {v : ℂ} (hv : v ∈ annulusParameters R ρ) : v ≠ 0 := by
  rintro rfl
  have h := ((mem_annulusParameters_iff hρ hρR).mp hv).1
  rw [norm_zero] at h
  exact (hρ _).not_ge h

theorem isCompact_annulusParameters (R : ℝ) {ρ : Circle → ℝ} (hρ : Continuous ρ) :
    IsCompact (annulusParameters R ρ) := by
  have ht : Continuous (fun p : unitInterval × Circle => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  exact isCompact_range ((((continuous_const.sub ht).mul continuous_const).add
    (ht.mul (hρ.comp continuous_snd))).smul (continuous_subtype_val.comp continuous_snd))

/-- The radial push of `w` at time `s`, which moves the norm of `w` linearly to `R`
and keeps its direction. -/
def radialPush (R s : ℝ) (w : ℂ) : ℂ :=
  ((1 - s) + s * R / ‖w‖) • w

theorem radialPush_coeff_pos {R s : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ≠ 0)
    (hs : s ∈ Icc (0 : ℝ) 1) : 0 < (1 - s) + s * R / ‖w‖ := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rcases eq_or_lt_of_le hs.2 with h | h
  · subst h
    simp only [sub_self, one_mul, zero_add]
    exact div_pos hR hn
  · have : 0 ≤ s * R / ‖w‖ := div_nonneg (mul_nonneg hs.1 hR.le) hn.le
    linarith

theorem norm_radialPush {R s : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ≠ 0)
    (hs : s ∈ Icc (0 : ℝ) 1) : ‖radialPush R s w‖ = (1 - s) * ‖w‖ + s * R := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [radialPush, norm_smul, Real.norm_eq_abs, abs_of_pos (radialPush_coeff_pos hR hw hs)]
  field_simp

theorem radialPush_zero (R : ℝ) (w : ℂ) : radialPush R 0 w = w := by
  simp only [radialPush, sub_zero, zero_mul, zero_div, add_zero, one_smul]

theorem radialPush_of_norm_eq {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : ‖w‖ = R) (s : ℝ) :
    radialPush R s w = w := by
  rw [radialPush, hw, mul_div_assoc, div_self hR.ne', mul_one, sub_add_cancel, one_smul]

theorem circleExp_arg_radialPush {R s : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ≠ 0)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    Circle.exp (Complex.arg (radialPush R s w)) = Circle.exp (Complex.arg w) :=
  circleExp_arg_smul (radialPush_coeff_pos hR hw hs) w

theorem radialPush_mem_annulusParameters {R : ℝ} {ρ : Circle → ℝ} (hρ : ∀ u, 0 < ρ u)
    (hρR : ∀ u, ρ u < R) {v : ℂ} (hv : v ∈ annulusParameters R ρ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : radialPush R s v ∈ annulusParameters R ρ := by
  have hR : 0 < R := (hρ 1).trans (hρR 1)
  have hv0 := ne_zero_of_mem_annulusParameters hρ hρR hv
  obtain ⟨h₁, h₂⟩ := (mem_annulusParameters_iff hρ hρR).mp hv
  rw [mem_annulusParameters_iff hρ hρR, circleExp_arg_radialPush hR hv0 hs,
    norm_radialPush hR hv0 hs]
  constructor <;> nlinarith [hs.1, hs.2]

theorem norm_radialPush_one {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ≠ 0) :
    ‖radialPush R 1 w‖ = R := by
  rw [norm_radialPush hR hw ⟨zero_le_one, le_rfl⟩]
  ring

/-- The closed parameter disk `{s ρ(u) u | s ∈ [0, 1], u ∈ S¹}` bounded by the
radial graph of `ρ`. -/
def innerParameters (ρ : Circle → ℝ) : Set ℂ :=
  range (fun p : unitInterval × Circle => ((p.1 : ℝ) * ρ p.2) • (p.2 : ℂ))

theorem mem_innerParameters_of_norm_le {ρ : Circle → ℝ} (hρ : ∀ u, 0 < ρ u) {v : ℂ}
    (hv : ‖v‖ ≤ ρ (Circle.exp (Complex.arg v))) : v ∈ innerParameters ρ := by
  have hρv := hρ (Circle.exp (Complex.arg v))
  refine ⟨(⟨‖v‖ / ρ (Circle.exp (Complex.arg v)), div_nonneg (norm_nonneg _) hρv.le,
    (div_le_one hρv).mpr hv⟩, Circle.exp (Complex.arg v)), ?_⟩
  change ((‖v‖ / ρ (Circle.exp (Complex.arg v))) * ρ (Circle.exp (Complex.arg v))) •
    (Circle.exp (Complex.arg v) : ℂ) = v
  rw [div_mul_cancel₀ _ hρv.ne']
  exact norm_smul_circleExp_arg v

theorem norm_le_of_mem_innerParameters {ρ : Circle → ℝ} (hρ : ∀ u, 0 < ρ u) {v : ℂ}
    (hv : v ∈ innerParameters ρ) (hv0 : v ≠ 0) : ‖v‖ ≤ ρ (Circle.exp (Complex.arg v)) := by
  obtain ⟨⟨s, u⟩, rfl⟩ := hv
  have hs0 : 0 < (s : ℝ) * ρ u := by
    rcases eq_or_lt_of_le s.2.1 with h | h
    · exfalso
      apply hv0
      change ((s : ℝ) * ρ u) • (u : ℂ) = 0
      rw [← h, zero_mul, zero_smul]
    · exact mul_pos h (hρ u)
  change ‖((s : ℝ) * ρ u) • (u : ℂ)‖ ≤ ρ (Circle.exp (Complex.arg (((s : ℝ) * ρ u) • (u : ℂ))))
  rw [circleExp_arg_smul hs0, Circle.exp_arg, norm_smul, Real.norm_eq_abs,
    abs_of_pos hs0, Circle.norm_coe, mul_one]
  exact mul_le_of_le_one_left (hρ u).le s.2.2

theorem innerParameters_subset_ball {R : ℝ} {ρ : Circle → ℝ} (hρ : ∀ u, 0 < ρ u)
    (hρR : ∀ u, ρ u < R) : innerParameters ρ ⊆ ball 0 R := by
  rintro _ ⟨⟨s, u⟩, rfl⟩
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg s.2.1 (hρ u).le), Circle.norm_coe, mul_one]
  exact (mul_le_of_le_one_left (hρ u).le s.2.2).trans_lt (hρR u)

theorem isCompact_innerParameters {ρ : Circle → ℝ} (hρ : Continuous ρ) :
    IsCompact (innerParameters ρ) :=
  isCompact_range (((continuous_subtype_val.comp continuous_fst).mul
    (hρ.comp continuous_snd)).smul (continuous_subtype_val.comp continuous_snd))

namespace ResolutionSectionLevel

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}

/-- The source annulus `ψ_j({r u | ρ(u) ≤ r ≤ R_j})` inside the closed coordinate
disk at `j`. -/
def sourceAnnulus (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) (ρ : Circle → ℝ) :
    Set CollarPlane :=
  (D j).ψ '' annulusParameters (D j).radius ρ

/-- The disk exterior with the source annuli of the family `Λ` attached. -/
def attachedSurface (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (ε : ℝ)
    (Λ : (j : L.points) → L.LocalAnnulus D j) : Set CollarPlane :=
  L.diskExterior D ε ∪ ⋃ j, L.sourceAnnulus D j (Λ j).ρ

/-- The inner circle `ψ_j(ρ(u) u)`, whose section image is the translated
sphere link. -/
def innerCircle (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) (ρ : Circle → ℝ) :
    Set CollarPlane :=
  (D j).ψ '' range (fun u : Circle => ρ u • (u : ℂ))

/-- The closed disk inside the inner circle, removed when the annulus is
attached. -/
def innerDisk (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) (ρ : Circle → ℝ) :
    Set CollarPlane :=
  (D j).ψ '' innerParameters ρ

/-- The radial deformation of the closed coordinate disk at `j`, written in the
disk coordinate. -/
def annulusPush (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) (s : ℝ)
    (z : CollarPlane) : CollarPlane :=
  (D j).ψ (radialPush (D j).radius s
    ((D j).coordinate (z - (EuclideanSpace.equiv (Fin 2) ℂ).symm (j : Source 2))))

/-- The deformation of the attached surface onto the disk exterior. It is the
radial push on each source annulus and the identity elsewhere. -/
def attachedDeformation (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j)
    (Λ : (j : L.points) → L.LocalAnnulus D j) (s : ℝ) (z : CollarPlane) : CollarPlane := by
  classical
  exact if h : ∃ j, z ∈ L.sourceAnnulus D j (Λ j).ρ then L.annulusPush D h.choose s z else z

variable {L : ResolutionSectionLevel A} {D : (j : L.points) → L.PointCoordinateDisk j}
  {ε : ℝ}

/-! ### The source annuli -/

theorem sourceAnnulus_subset_closedDisk {j : L.points} (Λ : L.LocalAnnulus D j) :
    L.sourceAnnulus D j Λ.ρ ⊆ (D j).closedDisk :=
  image_mono (annulusParameters_subset_closedBall Λ.ρ_pos Λ.ρ_lt)

theorem boundaryCircle_subset_sourceAnnulus {j : L.points} (Λ : L.LocalAnnulus D j) :
    (D j).boundaryCircle ⊆ L.sourceAnnulus D j Λ.ρ := by
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨v, ?_, rfl⟩
  have hv' := mem_sphere_zero_iff_norm.mp hv
  rw [mem_annulusParameters_iff Λ.ρ_pos Λ.ρ_lt, hv']
  exact ⟨(Λ.ρ_lt _).le, le_rfl⟩

theorem isCompact_sourceAnnulus {j : L.points} (Λ : L.LocalAnnulus D j) :
    IsCompact (L.sourceAnnulus D j Λ.ρ) :=
  (isCompact_annulusParameters _ Λ.ρ_smooth.continuous).image_of_continuousOn
    ((D j).analytic.continuousOn.mono ((annulusParameters_subset_closedBall Λ.ρ_pos
      Λ.ρ_lt).trans (D j).closedBall_subset))

/-- Every point of the source annulus is the image of its own disk coordinate,
which lies in the parameter annulus. -/
theorem coordinate_of_mem_sourceAnnulus {j : L.points} (Λ : L.LocalAnnulus D j)
    {z : CollarPlane} (hz : z ∈ L.sourceAnnulus D j Λ.ρ) :
    (D j).ψ ((D j).coordinate (z - (EuclideanSpace.equiv (Fin 2) ℂ).symm (j : Source 2))) = z ∧
      (D j).coordinate (z - (EuclideanSpace.equiv (Fin 2) ℂ).symm (j : Source 2)) ∈
        annulusParameters (D j).radius Λ.ρ := by
  obtain ⟨v, hv, rfl⟩ := hz
  rw [(D j).left_inverse v ((D j).closedBall_subset
    (annulusParameters_subset_closedBall Λ.ρ_pos Λ.ρ_lt hv))]
  exact ⟨rfl, hv⟩

/-- The section image of the source annulus is the local annulus. -/
theorem image_sourceAnnulus (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points) (ρ : Circle → ℝ) :
    euclideanSectionMap A.H '' L.sourceAnnulus D j ρ = L.localAnnulus D j ρ := by
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨p, rfl⟩, rfl⟩, rfl⟩
    exact ⟨p, annulusMap_eq L D j ρ _⟩
  · rintro ⟨p, rfl⟩
    exact ⟨_, ⟨_, ⟨p, rfl⟩, rfl⟩, (annulusMap_eq L D j ρ _).symm⟩

/-! ### The attached surface and its section embedding -/

theorem diskExterior_subset_attachedSurface (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (ε : ℝ)
    (Λ : (j : L.points) → L.LocalAnnulus D j) :
    L.diskExterior D ε ⊆ L.attachedSurface D ε Λ :=
  subset_union_left

theorem sourceAnnulus_subset_attachedSurface (Λ : (j : L.points) → L.LocalAnnulus D j)
    (j : L.points) : L.sourceAnnulus D j (Λ j).ρ ⊆ L.attachedSurface D ε Λ :=
  (subset_iUnion (fun k => L.sourceAnnulus D k (Λ k).ρ) j).trans subset_union_right

/-- The attached surface lies in the target cut. -/
theorem attachedSurface_subset_cut (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) :
    L.attachedSurface D ε Λ ⊆ targetSectionCut A.H L.radius ε L.parameter := by
  rintro z (hz | hz)
  · exact hz.1
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    exact hL.closedDisk_subset_cut j (sourceAnnulus_subset_closedDisk (Λ j) hj)

theorem isClosed_sourceAnnulus {j : L.points} (Λ : L.LocalAnnulus D j) :
    IsClosed (L.sourceAnnulus D j Λ.ρ) :=
  (isCompact_sourceAnnulus Λ).isClosed

/-- The attached surface is compact. -/
theorem isCompact_attachedSurface (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) : IsCompact (L.attachedSurface D ε Λ) :=
  hL.isCompact_diskExterior.union (isCompact_iUnion fun j => isCompact_sourceAnnulus (Λ j))

theorem continuousOn_euclideanSectionMap_cut (hL : L.ExteriorHypotheses D ε) :
    ContinuousOn (euclideanSectionMap A.H) (targetSectionCut A.H L.radius ε L.parameter) := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  intro z hz
  exact (((e.symm.analyticAt _).comp (((hyperplaneTail 2).analyticAt _).comp
    ((hL.analytic (e z) hz.1.1).comp (e.analyticAt z)))).continuousAt).continuousWithinAt

/-- **Section embedding.** The section map is a closed embedding of the
attached surface. -/
theorem attachedSurface_closedEmbedding (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) :
    Topology.IsClosedEmbedding
      ((L.attachedSurface D ε Λ).domRestrict (euclideanSectionMap A.H)) := by
  have : CompactSpace ↥(L.attachedSurface D ε Λ) :=
    isCompact_iff_compactSpace.mp (isCompact_attachedSurface hL Λ)
  have hsub := attachedSurface_subset_cut hL Λ
  apply ((continuousOn_euclideanSectionMap_cut hL).mono hsub).domRestrict.isClosedEmbedding
  intro z w hzw
  exact Subtype.ext (L.euclideanSectionMap_injOn_cut ε (hsub z.2) (hsub w.2) hzw)

/-- **Section image.** The section image of the attached surface is the union
of the section image of the disk exterior with the local annuli. -/
theorem image_attachedSurface (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (ε : ℝ)
    (Λ : (j : L.points) → L.LocalAnnulus D j) :
    euclideanSectionMap A.H '' L.attachedSurface D ε Λ =
      euclideanSectionMap A.H '' L.diskExterior D ε ∪ ⋃ j, L.localAnnulus D j (Λ j).ρ := by
  rw [attachedSurface, image_union, image_iUnion]
  simp only [image_sourceAnnulus]

/-! ### The deformation retraction onto the disk exterior -/

theorem eq_of_mem_sourceAnnulus (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) {j k : L.points} {z : CollarPlane}
    (hj : z ∈ L.sourceAnnulus D j (Λ j).ρ) (hk : z ∈ L.sourceAnnulus D k (Λ k).ρ) : j = k := by
  by_contra hjk
  exact Set.disjoint_left.mp (hL.disjoint hjk) (sourceAnnulus_subset_closedDisk (Λ j) hj)
    (sourceAnnulus_subset_closedDisk (Λ k) hk)

theorem attachedDeformation_of_mem (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) {j : L.points} {z : CollarPlane}
    (hz : z ∈ L.sourceAnnulus D j (Λ j).ρ) (s : ℝ) :
    L.attachedDeformation D Λ s z = L.annulusPush D j s z := by
  have h : ∃ k, z ∈ L.sourceAnnulus D k (Λ k).ρ := ⟨j, hz⟩
  rw [attachedDeformation, dif_pos h, eq_of_mem_sourceAnnulus hL Λ h.choose_spec hz]

theorem annulusPush_of_mem_boundaryCircle {j : L.points} {z : CollarPlane}
    (hz : z ∈ (D j).boundaryCircle) (s : ℝ) : L.annulusPush D j s z = z := by
  obtain ⟨v, hv, rfl⟩ := hz
  rw [annulusPush, (D j).left_inverse v ((D j).closedBall_subset (sphere_subset_closedBall hv)),
    radialPush_of_norm_eq (D j).radius_pos (mem_sphere_zero_iff_norm.mp hv)]

/-- The deformation fixes every point of the disk exterior at every time. -/
theorem attachedDeformation_of_mem_diskExterior (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) {z : CollarPlane}
    (hz : z ∈ L.diskExterior D ε) (s : ℝ) : L.attachedDeformation D Λ s z = z := by
  by_cases h : ∃ j, z ∈ L.sourceAnnulus D j (Λ j).ρ
  · obtain ⟨j, hj⟩ := h
    rw [attachedDeformation_of_mem hL Λ hj]
    apply annulusPush_of_mem_boundaryCircle
    rw [← hL.diskExterior_inter_closedDisk j]
    exact ⟨hz, sourceAnnulus_subset_closedDisk (Λ j) hj⟩
  · rw [attachedDeformation, dif_neg h]

theorem annulusPush_mem {j : L.points} (Λ : L.LocalAnnulus D j) {z : CollarPlane}
    (hz : z ∈ L.sourceAnnulus D j Λ.ρ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    L.annulusPush D j s z ∈ L.sourceAnnulus D j Λ.ρ :=
  ⟨_, radialPush_mem_annulusParameters Λ.ρ_pos Λ.ρ_lt
    (coordinate_of_mem_sourceAnnulus Λ hz).2 hs, rfl⟩

theorem annulusPush_zero {j : L.points} (Λ : L.LocalAnnulus D j) {z : CollarPlane}
    (hz : z ∈ L.sourceAnnulus D j Λ.ρ) : L.annulusPush D j 0 z = z := by
  rw [annulusPush, radialPush_zero]
  exact (coordinate_of_mem_sourceAnnulus Λ hz).1

theorem annulusPush_one_mem {j : L.points} (Λ : L.LocalAnnulus D j) {z : CollarPlane}
    (hz : z ∈ L.sourceAnnulus D j Λ.ρ) : L.annulusPush D j 1 z ∈ (D j).boundaryCircle := by
  refine ⟨_, ?_, rfl⟩
  rw [mem_sphere_zero_iff_norm]
  exact norm_radialPush_one (D j).radius_pos (ne_zero_of_mem_annulusParameters Λ.ρ_pos Λ.ρ_lt
    (coordinate_of_mem_sourceAnnulus Λ hz).2)

theorem continuousOn_annulusPush {j : L.points} (Λ : L.LocalAnnulus D j) :
    ContinuousOn (fun p : ℝ × CollarPlane => L.annulusPush D j p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ L.sourceAnnulus D j Λ.ρ) := by
  let c := (EuclideanSpace.equiv (Fin 2) ℂ).symm (j : Source 2)
  let R := (D j).radius
  let S := Icc (0 : ℝ) 1 ×ˢ L.sourceAnnulus D j Λ.ρ
  have hw : Continuous (fun p : ℝ × CollarPlane => (D j).coordinate (p.2 - c)) :=
    (D j).coordinate.continuous.comp (continuous_snd.sub continuous_const)
  have hne : ∀ p ∈ S, ‖(D j).coordinate (p.2 - c)‖ ≠ 0 := fun p hp =>
    norm_ne_zero_iff.mpr (ne_zero_of_mem_annulusParameters Λ.ρ_pos Λ.ρ_lt
      (coordinate_of_mem_sourceAnnulus Λ hp.2).2)
  have hk : ContinuousOn (fun p : ℝ × CollarPlane =>
      (1 - p.1) + p.1 * R / ‖(D j).coordinate (p.2 - c)‖) S :=
    (continuous_const.sub continuous_fst).continuousOn.add
      ((continuous_fst.mul continuous_const).continuousOn.div
        (continuous_norm.comp hw).continuousOn hne)
  have hq : ContinuousOn (fun p : ℝ × CollarPlane =>
      radialPush R p.1 ((D j).coordinate (p.2 - c))) S :=
    hk.smul hw.continuousOn
  have hmaps : MapsTo (fun p : ℝ × CollarPlane => radialPush R p.1 ((D j).coordinate (p.2 - c)))
      S (D j).W := fun p hp => (D j).closedBall_subset
    (annulusParameters_subset_closedBall Λ.ρ_pos Λ.ρ_lt
      (radialPush_mem_annulusParameters Λ.ρ_pos Λ.ρ_lt
        (coordinate_of_mem_sourceAnnulus Λ hp.2).2 hp.1))
  exact (D j).analytic.continuousOn.comp hq hmaps

/-- The deformation is jointly continuous on `[0, 1]` times the attached
surface. -/
theorem continuousOn_attachedDeformation (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) :
    ContinuousOn (fun p : ℝ × CollarPlane => L.attachedDeformation D Λ p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ L.attachedSurface D ε Λ) := by
  have hE : ContinuousOn (fun p : ℝ × CollarPlane => L.attachedDeformation D Λ p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ L.diskExterior D ε) :=
    continuousOn_snd.congr fun p hp => attachedDeformation_of_mem_diskExterior hL Λ hp.2 p.1
  have hA : ContinuousOn (fun p : ℝ × CollarPlane => L.attachedDeformation D Λ p.1 p.2)
      (⋃ j, Icc (0 : ℝ) 1 ×ˢ L.sourceAnnulus D j (Λ j).ρ) :=
    (locallyFinite_of_finite _).continuousOn_iUnion
      (fun j => isClosed_Icc.prod (isClosed_sourceAnnulus (Λ j)))
      (fun j => (continuousOn_annulusPush (Λ j)).congr fun p hp =>
        attachedDeformation_of_mem hL Λ hp.2 p.1)
  have h := hE.union_of_isClosed hA (isClosed_Icc.prod hL.isClosed_diskExterior)
    (isClosed_iUnion_of_finite fun j => isClosed_Icc.prod (isClosed_sourceAnnulus (Λ j)))
  rwa [← prod_iUnion, ← prod_union] at h

theorem attachedDeformation_mem (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) {z : CollarPlane}
    (hz : z ∈ L.attachedSurface D ε Λ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    L.attachedDeformation D Λ s z ∈ L.attachedSurface D ε Λ := by
  rcases hz with hz | hz
  · rw [attachedDeformation_of_mem_diskExterior hL Λ hz]
    exact Or.inl hz
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    rw [attachedDeformation_of_mem hL Λ hj]
    exact sourceAnnulus_subset_attachedSurface Λ j (annulusPush_mem (Λ j) hj hs)

theorem attachedDeformation_zero (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) {z : CollarPlane}
    (hz : z ∈ L.attachedSurface D ε Λ) : L.attachedDeformation D Λ 0 z = z := by
  rcases hz with hz | hz
  · exact attachedDeformation_of_mem_diskExterior hL Λ hz 0
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    rw [attachedDeformation_of_mem hL Λ hj]
    exact annulusPush_zero (Λ j) hj

theorem attachedDeformation_one_mem (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) {z : CollarPlane}
    (hz : z ∈ L.attachedSurface D ε Λ) :
    L.attachedDeformation D Λ 1 z ∈ L.diskExterior D ε := by
  rcases hz with hz | hz
  · rw [attachedDeformation_of_mem_diskExterior hL Λ hz]
    exact hz
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    rw [attachedDeformation_of_mem hL Λ hj]
    exact hL.boundaryCircle_subset_diskExterior j (annulusPush_one_mem (Λ j) hj)

/-- **Attachment preserves the homotopy type.** The inclusion of the disk
exterior into the attached surface is a homotopy equivalence. -/
theorem exists_homotopyEquiv_attachedSurface (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) :
    ∃ φ : ContinuousMap.HomotopyEquiv ↥(L.diskExterior D ε) ↥(L.attachedSurface D ε Λ),
      ∀ x, (φ.toFun x : CollarPlane) = x := by
  have hEX := L.diskExterior_subset_attachedSurface D ε Λ
  have hc := continuousOn_attachedDeformation hL Λ
  have hcont : Continuous (fun p : unitInterval × ↥(L.attachedSurface D ε Λ) =>
      L.attachedDeformation D Λ p.1 p.2) :=
    hc.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)) (fun p => ⟨p.1.2, p.2.2⟩)
  let i : C(↥(L.diskExterior D ε), ↥(L.attachedSurface D ε Λ)) :=
    ⟨inclusion hEX, continuous_inclusion hEX⟩
  let r : C(↥(L.attachedSurface D ε Λ), ↥(L.diskExterior D ε)) :=
    ⟨fun x => ⟨L.attachedDeformation D Λ 1 x, attachedDeformation_one_mem hL Λ x.2⟩,
      (hc.comp_continuous (continuous_const.prodMk continuous_subtype_val)
        (fun x => ⟨⟨zero_le_one, le_rfl⟩, x.2⟩)).subtype_mk _⟩
  have hri : r.comp i = ContinuousMap.id _ :=
    ContinuousMap.ext fun y => Subtype.ext (attachedDeformation_of_mem_diskExterior hL Λ y.2 1)
  let F : ContinuousMap.Homotopy (ContinuousMap.id ↥(L.attachedSurface D ε Λ)) (i.comp r) :=
    { toFun := fun p => ⟨L.attachedDeformation D Λ p.1 p.2,
        attachedDeformation_mem hL Λ p.2.2 p.1.2⟩
      continuous_toFun := hcont.subtype_mk _
      map_zero_left := fun x => Subtype.ext (attachedDeformation_zero hL Λ x.2)
      map_one_left := fun _ => rfl }
  exact ⟨⟨i, r, by rw [hri], ⟨F.symm⟩⟩, fun _ => rfl⟩

/-- Curve rational homology transfers from the disk exterior to the attached
surface. -/
theorem hasCurveRatHomology_attachedSurface (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) {χ : ℤ}
    (h : HasCurveRatHomology ↥(L.diskExterior D ε) χ) :
    HasCurveRatHomology ↥(L.attachedSurface D ε Λ) χ := by
  obtain ⟨φ, -⟩ := exists_homotopyEquiv_attachedSurface hL Λ
  exact h.of_homotopyEquiv φ.symm

/-- The attached surface and the disk exterior have rational homology of the
same dimension in every degree. -/
theorem finrank_ratH_attachedSurface (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) (n : ℕ) :
    Module.finrank ℚ (ratH ↥(L.attachedSurface D ε Λ) n) =
      Module.finrank ℚ (ratH ↥(L.diskExterior D ε) n) := by
  obtain ⟨φ, -⟩ := exists_homotopyEquiv_attachedSurface hL Λ
  exact finrank_eq_of_iso (ratHIsoOfHomotopyEquiv φ.symm n)

/-- Path connectedness transfers from the disk exterior to the attached
surface. -/
theorem isPathConnected_attachedSurface (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) (hE : IsPathConnected (L.diskExterior D ε)) :
    IsPathConnected (L.attachedSurface D ε Λ) := by
  obtain ⟨x₀, hx₀, hjoin⟩ := hE
  have hEX := L.diskExterior_subset_attachedSurface D ε Λ
  refine ⟨x₀, hEX hx₀, fun y hy => ?_⟩
  have hc := continuousOn_attachedDeformation hL Λ
  let γ : Path y (L.attachedDeformation D Λ 1 y) :=
    { toFun := fun s => L.attachedDeformation D Λ s y
      continuous_toFun := hc.comp_continuous (continuous_subtype_val.prodMk continuous_const)
        (fun s => ⟨s.2, hy⟩)
      source' := attachedDeformation_zero hL Λ hy
      target' := rfl }
  have h₁ : JoinedIn (L.attachedSurface D ε Λ) y (L.attachedDeformation D Λ 1 y) :=
    ⟨γ, fun s => attachedDeformation_mem hL Λ hy s.2⟩
  exact ((hjoin (attachedDeformation_one_mem hL Λ hy)).mono hEX).trans h₁.symm

/-! ### The new boundary -/

/-- The section image of the inner circle is the translated sphere link of the
local equation `W`. -/
theorem image_innerCircle {j : L.points} (Λ : L.LocalAnnulus D j) :
    euclideanSectionMap A.H '' L.innerCircle D j Λ.ρ =
      (fun y => L.sectionPoint j + y) ''
        (sphere 0 Λ.sphereRadius ∩ {y | Λ.W ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0}) := by
  rw [← range_annulusMap_one Λ]
  have h (u : Circle) : L.annulusMap D j Λ.ρ (1, u) =
      euclideanSectionMap A.H ((D j).ψ (Λ.ρ u • (u : ℂ))) := by
    rw [annulusMap_eq, annulusRadius_one]
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨u, rfl⟩, rfl⟩, rfl⟩
    exact ⟨u, h u⟩
  · rintro ⟨u, rfl⟩
    exact ⟨_, ⟨_, ⟨u, rfl⟩, rfl⟩, (h u).symm⟩

theorem innerCircle_subset_sourceAnnulus {j : L.points} (Λ : L.LocalAnnulus D j) :
    L.innerCircle D j Λ.ρ ⊆ L.sourceAnnulus D j Λ.ρ := by
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  refine ⟨Λ.ρ u • (u : ℂ), ⟨(⟨1, unitInterval.one_mem⟩, u), ?_⟩, rfl⟩
  change annulusRadius (D j).radius Λ.ρ (1, u) • (u : ℂ) = Λ.ρ u • (u : ℂ)
  rw [annulusRadius_one]

theorem isClosed_innerDisk {j : L.points} (Λ : L.LocalAnnulus D j) :
    IsClosed (L.innerDisk D j Λ.ρ) :=
  ((isCompact_innerParameters Λ.ρ_smooth.continuous).image_of_continuousOn
    ((D j).analytic.continuousOn.mono ((innerParameters_subset_ball Λ.ρ_pos Λ.ρ_lt).trans
      (ball_subset_closedBall.trans (D j).closedBall_subset)))).isClosed

/-- A point of the attached surface in the inner disk at `j` lies on the inner
circle at `j`. -/
theorem mem_innerCircle_of_mem_innerDisk (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) {j : L.points} {z : CollarPlane}
    (hz : z ∈ L.attachedSurface D ε Λ) (hzi : z ∈ L.innerDisk D j (Λ j).ρ) :
    z ∈ L.innerCircle D j (Λ j).ρ := by
  obtain ⟨v, hv, rfl⟩ := hzi
  have hvW : v ∈ (D j).W := (D j).closedBall_subset (ball_subset_closedBall
    (innerParameters_subset_ball (Λ j).ρ_pos (Λ j).ρ_lt hv))
  have hzD : (D j).ψ v ∈ (D j).closedDisk :=
    ⟨v, ball_subset_closedBall (innerParameters_subset_ball (Λ j).ρ_pos (Λ j).ρ_lt hv), rfl⟩
  rcases hz with hz | hz
  · exfalso
    have hb : (D j).ψ v ∈ (D j).boundaryCircle := by
      rw [← hL.diskExterior_inter_closedDisk j]
      exact ⟨hz, hzD⟩
    obtain ⟨v', hv', he⟩ := hb
    have hvv : v' = v := (D j).injOn ((D j).closedBall_subset (sphere_subset_closedBall hv'))
      hvW he
    have hlt := mem_ball_zero_iff.mp (innerParameters_subset_ball (Λ j).ρ_pos (Λ j).ρ_lt hv)
    rw [← hvv, mem_sphere_zero_iff_norm.mp hv'] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    have hkj : k = j := by
      by_contra hne
      exact Set.disjoint_left.mp (hL.disjoint hne) (sourceAnnulus_subset_closedDisk (Λ k) hk)
        hzD
    subst hkj
    obtain ⟨v', hv', he⟩ := hk
    have hvv : v' = v := (D k).injOn ((D k).closedBall_subset
      (annulusParameters_subset_closedBall (Λ k).ρ_pos (Λ k).ρ_lt hv')) hvW he
    subst hvv
    have hv0 := ne_zero_of_mem_annulusParameters (Λ k).ρ_pos (Λ k).ρ_lt hv'
    have h₁ := ((mem_annulusParameters_iff (Λ k).ρ_pos (Λ k).ρ_lt).mp hv').1
    have h₂ := norm_le_of_mem_innerParameters (Λ k).ρ_pos hv hv0
    have hvv' : (Λ k).ρ (Circle.exp (Complex.arg v')) • (Circle.exp (Complex.arg v') : ℂ) =
        v' := by
      rw [← le_antisymm h₂ h₁]
      exact norm_smul_circleExp_arg v'
    exact ⟨_, ⟨Circle.exp (Complex.arg v'), rfl⟩, congrArg (D k).ψ hvv'⟩

/-- **New boundary.** A point of the attached surface has a neighborhood in the
level contained in the attached surface if and only if it lies neither on the
outer target boundary nor on an inner circle. In particular the old hole
circles become interior points. -/
theorem attachedSurface_relInterior_iff (hL : L.ExteriorHypotheses D ε)
    (Λ : (j : L.points) → L.LocalAnnulus D j) {z : CollarPlane}
    (hz : z ∈ L.attachedSurface D ε Λ) :
    (∃ O : Set CollarPlane, IsOpen O ∧ z ∈ O ∧
      O ∩ {w | euclideanEquation (fun x => A.H x 0) w = L.parameter} ⊆
        L.attachedSurface D ε Λ) ↔
      z ∉ targetSectionBoundary A.H L.radius ε L.parameter ∧
        ∀ j, z ∉ L.innerCircle D j (Λ j).ρ := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  have hzcut := attachedSurface_subset_cut hL Λ hz
  constructor
  · rintro ⟨O, hO, hzO, hsub⟩
    constructor
    · intro hzb
      have hinside := hL.mem_ball_of_mem_cut hzcut
      have hsurj := hL.submersion (e z) hzb.1.1 hzb.1.2 (by rw [hzb.2]; linarith [hL.pos])
      obtain ⟨C⟩ := nonempty_targetSectionBoundaryChart A.H hL.analytic hzb hinside hsurj
      have hφ : ContinuousAt C.φ 0 :=
        C.smooth.continuousOn.continuousAt (C.isOpen_W.mem_nhds C.zero_mem)
      have hev : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ C.W ∧ C.φ t ∈ O := by
        filter_upwards [C.isOpen_W.mem_nhds C.zero_mem,
          hφ.preimage_mem_nhds (hO.mem_nhds (C.φ_zero.symm ▸ hzO))] with t h₁ h₂
        exact ⟨h₁, h₂⟩
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
      let t : ℂ := -(((δ / 2 : ℝ)) : ℂ) * Complex.I
      have hδ2 : 0 < δ / 2 := half_pos hδ
      have ht : dist t 0 < δ := by
        rw [dist_zero_right, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hδ2]
        exact half_lt_self hδ
      obtain ⟨htW, htO⟩ := hball ht
      have hlevel : euclideanEquation (fun x => A.H x 0) (C.φ t) = L.parameter :=
        (C.level_eq t htW).trans hzb.1.2
      have hmem := attachedSurface_subset_cut hL Λ (hsub ⟨htO, hlevel⟩)
      have hrad := C.radius_eq t htW
      have hz2 : planeMapTargetRadiusSq A.H (e z) = ε ^ 2 := by
        unfold planeMapTargetRadiusSq
        rw [hzb.2]
      have htim : t.im = -(δ / 2) := by simp [t]
      have hle : planeMapTargetRadiusSq A.H (e (C.φ t)) ≤ ε ^ 2 := hmem.2
      change planeMapTargetRadiusSq A.H (e (C.φ t)) =
        planeMapTargetRadiusSq A.H (e z) - t.im at hrad
      rw [hrad, hz2, htim] at hle
      linarith
    · rintro j ⟨_, ⟨u, rfl⟩, rfl⟩
      let f : ℝ → CollarPlane := fun s => (D j).ψ ((s * (Λ j).ρ u) • (u : ℂ))
      have hρu := (Λ j).ρ_pos u
      have hmemW : (Λ j).ρ u • (u : ℂ) ∈ (D j).W := by
        apply (D j).closedBall_subset
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hρu,
          Circle.norm_coe, mul_one]
        exact ((Λ j).ρ_lt u).le
      have hf : ContinuousAt f 1 := by
        have hψ : ContinuousAt (D j).ψ (((1 : ℝ) * (Λ j).ρ u) • (u : ℂ)) := by
          rw [one_mul]
          exact ((D j).analytic _ hmemW).continuousAt
        have hlin : Continuous (fun s : ℝ => (s * (Λ j).ρ u) • (u : ℂ)) :=
          (continuous_id.mul continuous_const).smul continuous_const
        exact ContinuousAt.comp (g := (D j).ψ) (f := fun s : ℝ => (s * (Λ j).ρ u) • (u : ℂ))
          hψ hlin.continuousAt
      have hf1 : f 1 = (D j).ψ ((Λ j).ρ u • (u : ℂ)) := by simp only [f, one_mul]
      have hev : ∀ᶠ s in 𝓝 (1 : ℝ), f s ∈ O :=
        hf.preimage_mem_nhds (hO.mem_nhds (hf1.symm ▸ hzO))
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
      let s : ℝ := 1 - min δ 1 / 2
      have hmin : 0 < min δ 1 := lt_min hδ one_pos
      have hmin1 : min δ 1 ≤ 1 := min_le_right _ _
      have hs0 : 0 < s := by simp only [s]; linarith
      have hs1 : s < 1 := by simp only [s]; linarith
      have hsd : dist s 1 < δ := by
        rw [Real.dist_eq, show s - 1 = -(min δ 1 / 2) by simp only [s]; ring, abs_neg,
          abs_of_pos (half_pos hmin)]
        exact (half_lt_self hmin).trans_le (min_le_left _ _)
      have hfO := hball hsd
      let v : ℂ := (s * (Λ j).ρ u) • (u : ℂ)
      have hpos : 0 < s * (Λ j).ρ u := mul_pos hs0 hρu
      have hvnorm : ‖v‖ = s * (Λ j).ρ u := by
        simp only [v]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos, Circle.norm_coe, mul_one]
      have hvball : v ∈ ball (0 : ℂ) (D j).radius := by
        rw [mem_ball_zero_iff, hvnorm]
        exact (mul_lt_of_lt_one_left hρu hs1).trans ((Λ j).ρ_lt u)
      have hvW : v ∈ (D j).W := (D j).closedBall_subset (ball_subset_closedBall hvball)
      have hflevel : euclideanEquation (fun x => A.H x 0) (f s) = L.parameter :=
        (D j).level_eq v hvW
      rcases hsub ⟨hfO, hflevel⟩ with hE | hA
      · exact hE.2 (mem_iUnion.mpr ⟨j, ⟨v, hvball, rfl⟩⟩)
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hA
        have hkj : k = j := by
          by_contra hne
          exact Set.disjoint_left.mp (hL.disjoint hne)
            (sourceAnnulus_subset_closedDisk (Λ k) hk) ⟨v, ball_subset_closedBall hvball, rfl⟩
        rw [hkj] at hk
        obtain ⟨v', hv', he⟩ := hk
        have hvv : v' = v := (D j).injOn ((D j).closedBall_subset
          (annulusParameters_subset_closedBall (Λ j).ρ_pos (Λ j).ρ_lt hv')) hvW he
        rw [hvv] at hv'
        have h₁ := ((mem_annulusParameters_iff (Λ j).ρ_pos (Λ j).ρ_lt).mp hv').1
        have harg : Circle.exp (Complex.arg v) = u := by
          change Circle.exp (Complex.arg ((s * (Λ j).ρ u) • (u : ℂ))) = u
          rw [circleExp_arg_smul hpos, Circle.exp_arg]
        rw [harg, hvnorm] at h₁
        nlinarith
  · rintro ⟨hzb, hzi⟩
    let Q : CollarPlane → EuclideanSpace ℂ (Fin 3) :=
      fun w => (EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H (e w))
    have hQ : ContinuousOn Q (e ⁻¹' ball 0 L.radius) := fun w hw =>
      (((EuclideanSpace.equiv (Fin 3) ℂ).symm.analyticAt _).comp
        ((hL.analytic (e w) (ball_subset_closedBall hw)).comp
          (e.analyticAt w))).continuousAt.continuousWithinAt
    let O₀ : Set CollarPlane := e ⁻¹' ball 0 L.radius ∩ (fun w => ‖Q w‖) ⁻¹' Iio ε
    have hO₀ : IsOpen O₀ :=
      hQ.norm.isOpen_inter_preimage (isOpen_ball.preimage e.continuous) isOpen_Iio
    let O : Set CollarPlane := O₀ ∩ ⋂ k, (L.innerDisk D k (Λ k).ρ)ᶜ
    have hO : IsOpen O :=
      hO₀.inter (isOpen_iInter_of_finite fun k => (isClosed_innerDisk (Λ k)).isOpen_compl)
    refine ⟨O, hO, ⟨⟨hL.mem_ball_of_mem_cut hzcut, ?_⟩, ?_⟩, ?_⟩
    · have hle := ((mem_targetSectionCut_iff hL.pos.le).mp hzcut).2
      exact lt_of_le_of_ne hle fun heq => hzb ⟨hzcut.1, heq⟩
    · exact mem_iInter.mpr fun k hk => hzi k (mem_innerCircle_of_mem_innerDisk hL Λ hz hk)
    · rintro w ⟨⟨⟨hwball, hwQ⟩, hwI⟩, hwlevel⟩
      have hwcut : w ∈ targetSectionCut A.H L.radius ε L.parameter :=
        (mem_targetSectionCut_iff hL.pos.le).mpr ⟨⟨ball_subset_closedBall hwball, hwlevel⟩,
          (mem_Iio.mp hwQ).le⟩
      by_cases hw : w ∈ ⋃ k, (D k).openDisk
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hw
        obtain ⟨v, hv, rfl⟩ := hk
        have hvW : v ∈ (D k).W := (D k).closedBall_subset (ball_subset_closedBall hv)
        refine sourceAnnulus_subset_attachedSurface Λ k ⟨v, ?_, rfl⟩
        rw [mem_annulusParameters_iff (Λ k).ρ_pos (Λ k).ρ_lt]
        refine ⟨?_, (mem_ball_zero_iff.mp hv).le⟩
        by_contra hlt
        exact mem_iInter.mp hwI k
          ⟨v, mem_innerParameters_of_norm_le (Λ k).ρ_pos (not_le.mp hlt).le, rfl⟩
      · exact Or.inl ⟨hwcut, hw⟩

end ResolutionSectionLevel

end OnLeConjecture.Analytic
