/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionTargetBoundaryCharts

/-! # Orientation of charts at the literal target boundary

The real-axis tangent of the constructed upper-half-plane chart maps to a
positive tangent of the Euclidean target sphere. Both its tangency and its
sign follow from the exact inward radius coordinate and complex orientation.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff ComplexConjugate

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

theorem real_inner_euclidean_target (q v : EuclideanSpace ℂ (Fin 3)) :
    inner ℝ q v = (inner ℂ q v).re := by
  simp [PiLp.inner_apply, Complex.inner]

/-- For the squared norm of an analytic target map, the real-coordinate
boundary tangent maps to the positive Hermitian tangent ray of that sphere. -/
theorem SectionRadiusBoundaryChart.target_tangent_properties
    {f : CollarPlane → ℂ} {Q : CollarPlane → EuclideanSpace ℂ (Fin 3)}
    {O : Set CollarPlane} {z : CollarPlane}
    (C : SectionRadiusBoundaryChart f (fun w => ‖Q w‖ ^ 2) O z)
    (hf : DifferentiableAt ℂ f z) (hQ : DifferentiableAt ℂ Q z) :
    fderiv ℂ f z (fderiv ℝ C.φ 0 1) = 0 ∧
      (inner ℂ (Q z) (fderiv ℂ Q z (fderiv ℝ C.φ 0 1))).re = 0 ∧
      0 < (inner ℂ (Q z) (fderiv ℂ Q z (fderiv ℝ C.φ 0 1))).im := by
  have hr := (hQ.hasFDerivAt.restrictScalars ℝ).norm_sq
  obtain ⟨hker, hu, hv⟩ := C.tangent_properties hf hr.differentiableAt
  have hrder : ∀ v : CollarPlane,
      fderiv ℝ (fun w => ‖Q w‖ ^ 2) z v = 2 * (inner ℂ (Q z) (fderiv ℂ Q z v)).re := by
    intro v
    rw [hr.fderiv]
    simp only [ContinuousLinearMap.comp_apply, smul_apply, innerSL_apply_apply,
      ContinuousLinearMap.coe_restrictScalars', real_inner_euclidean_target,
      nsmul_eq_mul, Nat.cast_ofNat]
  rw [hrder] at hu hv
  obtain ⟨c, hc, hci⟩ := C.oriented 0 C.zero_mem
  have hre : (inner ℂ (Q z) (fderiv ℂ Q z (fderiv ℝ C.φ 0 1))).re = 0 := by linarith
  rw [hci, map_smul, inner_smul_right, Complex.mul_re, hre, mul_zero, zero_sub] at hv
  refine ⟨hker 1, hre, ?_⟩
  nlinarith

/-- The outer boundary retains the source domain and the literal Euclidean
three-coordinate target radius. -/
def targetSectionBoundary (H : Source 2 → Source 3) (R ε : ℝ) (s : ℂ) : Set CollarPlane :=
  {z | ((EuclideanSpace.equiv (Fin 2) ℂ) z ∈ closedBall 0 R ∧
    H ((EuclideanSpace.equiv (Fin 2) ℂ) z) 0 = s) ∧
    ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm
      (H ((EuclideanSpace.equiv (Fin 2) ℂ) z))‖ = ε}

/-- The local target boundary chart is obtained from the actual assembled
map wherever the proved joint transversivity and source confinement hold. -/
theorem nonempty_targetSectionBoundaryChart (H : Source 2 → Source 3)
    {R ε : ℝ} {s : ℂ} {z : CollarPlane}
    (ha : AnalyticOnNhd ℂ H (closedBall (0 : Source 2) R))
    (hz : z ∈ targetSectionBoundary H R ε s)
    (hinside : (EuclideanSpace.equiv (Fin 2) ℂ) z ∈ ball 0 R)
    (hsub : Surjective (fderiv ℝ (planeMapTargetRadialPair H)
      ((EuclideanSpace.equiv (Fin 2) ℂ) z))) :
    Nonempty (SectionRadiusBoundaryChart
      (euclideanEquation (fun x => H x 0))
      (fun w => planeMapTargetRadiusSq H ((EuclideanSpace.equiv (Fin 2) ℂ) w))
      ((EuclideanSpace.equiv (Fin 2) ℂ) ⁻¹' ball 0 R) z) := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  have hf : AnalyticAt ℂ (euclideanEquation (fun x => H x 0)) z :=
    ((analyticAt_pi_iff.mp (ha (e z) hz.1.1)) 0).comp (e.analyticAt z)
  apply nonempty_sectionRadiusBoundaryChart _ _ _ (isOpen_ball.preimage e.continuous) hinside hf
  · intro w hw
    have hQ := ((EuclideanSpace.equiv (Fin 3) ℂ).symm.analyticAt _).comp
      ((ha (e w) (ball_subset_closedBall hw)).comp (e.analyticAt w))
    exact ((hQ.restrictScalars (𝕜 := ℝ)).contDiffAt).norm_sq (𝕜 := ℂ)
  · have hd : fderiv ℝ (fun w => (euclideanEquation (fun x => H x 0) w,
        planeMapTargetRadiusSq H (e w))) z =
        (fderiv ℝ (planeMapTargetRadialPair H) (e z)).comp
          (e.toContinuousLinearMap.restrictScalars ℝ) :=
      (((contDiffAt_planeMapTargetRadialPair (ha (e z) hz.1.1)).differentiableAt
        (by simp)).hasFDerivAt.comp z (e.hasFDerivAt.restrictScalars ℝ)).fderiv
    rw [hd]
    exact hsub.comp e.surjective

/-- The chart's upper half-plane maps into the literal target cut. -/
theorem targetSectionBoundaryChart_mapsTo (H : Source 2 → Source 3)
    {R ε : ℝ} {s : ℂ} {z : CollarPlane}
    (hz : z ∈ targetSectionBoundary H R ε s)
    (C : SectionRadiusBoundaryChart (euclideanEquation (fun x => H x 0))
      (fun w => planeMapTargetRadiusSq H ((EuclideanSpace.equiv (Fin 2) ℂ) w))
      ((EuclideanSpace.equiv (Fin 2) ℂ) ⁻¹' ball 0 R) z) :
    MapsTo C.φ C.model (targetSectionCut H R ε s) := by
  intro t ht
  refine ⟨⟨ball_subset_closedBall (C.mapsTo ht.1), (C.level_eq t ht.1).trans hz.1.2⟩, ?_⟩
  have he : planeMapTargetRadiusSq H ((EuclideanSpace.equiv (Fin 2) ℂ) z) = ε ^ 2 := by
    unfold planeMapTargetRadiusSq
    rw [hz.2]
  rw [C.radius_eq t ht.1, he]
  exact sub_le_self _ ht.2

/-- Its real axis maps exactly to the literal target boundary. -/
theorem targetSectionBoundaryChart_boundary_iff (H : Source 2 → Source 3)
    {R ε : ℝ} {s : ℂ} {z : CollarPlane}
    (hz : z ∈ targetSectionBoundary H R ε s)
    (C : SectionRadiusBoundaryChart (euclideanEquation (fun x => H x 0))
      (fun w => planeMapTargetRadiusSq H ((EuclideanSpace.equiv (Fin 2) ℂ) w))
      ((EuclideanSpace.equiv (Fin 2) ℂ) ⁻¹' ball 0 R) z)
    {t : ℂ} (ht : t ∈ C.W) : C.φ t ∈ targetSectionBoundary H R ε s ↔ t.im = 0 := by
  have hε : 0 ≤ ε := hz.2 ▸ norm_nonneg _
  have he : planeMapTargetRadiusSq H ((EuclideanSpace.equiv (Fin 2) ℂ) z) = ε ^ 2 := by
    unfold planeMapTargetRadiusSq
    rw [hz.2]
  have hsource := ball_subset_closedBall (C.mapsTo ht)
  have hlevel := (C.level_eq t ht).trans hz.1.2
  change ( _ ∧ _) ∧ _ = ε ↔ _
  rw [and_iff_right ⟨hsource, hlevel⟩]
  rw [← pow_left_inj₀ (norm_nonneg _) hε two_ne_zero]
  change planeMapTargetRadiusSq H ((EuclideanSpace.equiv (Fin 2) ℂ) (C.φ t)) = ε ^ 2 ↔ _
  rw [← he]
  exact C.boundary_iff ht

/-- The chart parametrizes a relative neighborhood in the actual target cut. -/
theorem targetSectionBoundaryChart_image_nhds (H : Source 2 → Source 3)
    {R ε : ℝ} {s : ℂ} {z : CollarPlane}
    (hz : z ∈ targetSectionBoundary H R ε s)
    (C : SectionRadiusBoundaryChart (euclideanEquation (fun x => H x 0))
      (fun w => planeMapTargetRadiusSq H ((EuclideanSpace.equiv (Fin 2) ℂ) w))
      ((EuclideanSpace.equiv (Fin 2) ℂ) ⁻¹' ball 0 R) z) :
    C.φ '' C.model ∈ 𝓝[targetSectionCut H R ε s] z := by
  filter_upwards [C.local_inverse.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with w hw hwcut
  obtain ⟨hwW, he⟩ := hw (hwcut.1.2.trans hz.1.2.symm)
  refine ⟨C.χ w, ⟨hwW, ?_⟩, he⟩
  change 0 ≤ (C.χ w).im
  rw [C.inverse_im]
  apply sub_nonneg.mpr
  have he : planeMapTargetRadiusSq H ((EuclideanSpace.equiv (Fin 2) ℂ) z) = ε ^ 2 := by
    unfold planeMapTargetRadiusSq
    rw [hz.2]
  rw [he]
  exact hwcut.2

/-- The boundary tangent has positive target Hermitian sign for the actual
map, with its first target coordinate constant along the section. -/
theorem targetSectionBoundaryChart_tangent (H : Source 2 → Source 3)
    {R ε : ℝ} {s : ℂ} {z : CollarPlane}
    (ha : AnalyticOnNhd ℂ H (closedBall (0 : Source 2) R))
    (hz : z ∈ targetSectionBoundary H R ε s)
    (C : SectionRadiusBoundaryChart (euclideanEquation (fun x => H x 0))
      (fun w => planeMapTargetRadiusSq H ((EuclideanSpace.equiv (Fin 2) ℂ) w))
      ((EuclideanSpace.equiv (Fin 2) ℂ) ⁻¹' ball 0 R) z) :
    let Q : CollarPlane → EuclideanSpace ℂ (Fin 3) := fun w =>
      (EuclideanSpace.equiv (Fin 3) ℂ).symm (H ((EuclideanSpace.equiv (Fin 2) ℂ) w))
    fderiv ℂ (euclideanEquation (fun x => H x 0)) z (fderiv ℝ C.φ 0 1) = 0 ∧
      (inner ℂ (Q z) (fderiv ℂ Q z (fderiv ℝ C.φ 0 1))).re = 0 ∧
      0 < (inner ℂ (Q z) (fderiv ℂ Q z (fderiv ℝ C.φ 0 1))).im := by
  let e := EuclideanSpace.equiv (Fin 2) ℂ
  have hHe : AnalyticAt ℂ (fun w => H (e w)) z := (ha (e z) hz.1.1).comp (e.analyticAt z)
  exact C.target_tangent_properties ((analyticAt_pi_iff.mp hHe) 0).differentiableAt
    ((((EuclideanSpace.equiv (Fin 3) ℂ).symm.analyticAt _).comp hHe).differentiableAt)

namespace ResolutionSectionAssembly

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- Every sufficiently small target radius has an actual nearby assembled
section whose entire target boundary has the constructed oriented charts. -/
theorem exists_level_with_targetSectionBoundaryCharts (A : ResolutionSectionAssembly g hd hi) :
    ∃ R ε₀ : ℝ, 0 < R ∧ R < A.radius ∧ 0 < ε₀ ∧
      ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ L : ResolutionSectionLevel A,
        L.radius = R ∧ ‖L.parameter‖ < ε ∧
        AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) R) ∧
        ∀ z ∈ targetSectionBoundary A.H R ε L.parameter,
          Nonempty (SectionRadiusBoundaryChart (euclideanEquation (fun x => A.H x 0))
            (fun w => planeMapTargetRadiusSq A.H ((EuclideanSpace.equiv (Fin 2) ℂ) w))
            ((EuclideanSpace.equiv (Fin 2) ℂ) ⁻¹' ball 0 R) z) := by
  obtain ⟨R, r, ε₀, hr, hrR, hRA, hε₀, ha, _, _, hlevels⟩ :=
    A.exists_confined_target_boundary_levels
  refine ⟨R, ε₀, hr.trans hrR, hRA, hε₀, ?_⟩
  intro ε hε hεε₀
  obtain ⟨L, hLR, hLs, hconf, hsub⟩ := hlevels ε hε hεε₀
  refine ⟨L, hLR, hLs, ha, ?_⟩
  intro z hz
  have hzL : (EuclideanSpace.equiv (Fin 2) ℂ) z ∈ L.sourceLevel := by
    change (EuclideanSpace.equiv (Fin 2) ℂ) z ∈ closedBall 0 L.radius ∧
      A.H ((EuclideanSpace.equiv (Fin 2) ℂ) z) 0 = L.parameter
    rw [hLR]
    exact hz.1
  exact nonempty_targetSectionBoundaryChart A.H ha hz
    (ball_subset_ball hrR.le (hconf _ hzL hz.2.le)) (hsub _ hzL hz.2)

end ResolutionSectionAssembly

end OnLeConjecture.Analytic
