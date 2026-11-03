/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionExteriorImmersion
public import OnLeConjecture.Analytic.PlaneMilnorFibre
public import OnLeConjecture.Analytic.CurveInitialFactor

/-! # Boundary submersivity for the literal Euclidean target cutoff

Normalization branches provide tangent vectors along which the squared
Euclidean norm of the target map has nonzero derivative. Reducedness gives
the independent equation differential. Compactness then extends the resulting
central-level submersivity to nearby levels on target-radius annuli.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- The Euclidean target norm, rather than the norm on the coordinate function space. -/
def planeMapTargetRadiusSq (H : Source 2 → Source 3) (x : Source 2) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (H x)‖ ^ 2

/-- The first target coordinate together with the literal squared target radius. -/
def planeMapTargetRadialPair (H : Source 2 → Source 3) (x : Source 2) : ℂ × ℝ :=
  (H x 0, planeMapTargetRadiusSq H x)

theorem contDiffAt_planeMapTargetRadiusSq {H : Source 2 → Source 3} {x : Source 2}
    (hH : AnalyticAt ℂ H x) : ContDiffAt ℝ ∞ (planeMapTargetRadiusSq H) x := by
  have ha := (((EuclideanSpace.equiv (Fin 3) ℂ).symm.analyticAt _).comp hH).restrictScalars
    (𝕜 := ℝ)
  exact ha.contDiffAt.norm_sq (𝕜 := ℂ)

theorem contDiffAt_planeMapTargetRadialPair {H : Source 2 → Source 3} {x : Source 2}
    (hH : AnalyticAt ℂ H x) : ContDiffAt ℝ ∞ (planeMapTargetRadialPair H) x :=
  (((analyticAt_pi_iff.mp hH) 0).restrictScalars.contDiffAt).prodMk
    (contDiffAt_planeMapTargetRadiusSq hH)

/-- On a normalization branch, the analytic target norm changes in a
source-level tangent direction. The branch covers its entire local zero set. -/
theorem eventually_targetRadius_tangent_of_irreducible
    (H : Source 2 → Source 3) (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (S : Set (Source 2)) (hS : S ∈ 𝓝 0) (hinj : InjOn H S)
    (V P : Source 2 → ℂ) (hV : AnalyticAt ℂ V 0) (hP : AnalyticAt ℂ P 0)
    (hirr : Irreducible (ofFunction P hP))
    (hPV : ∀ᶠ x in 𝓝 (0 : Source 2), P x = 0 → V x = 0) :
    ∀ᶠ x in 𝓝 (0 : Source 2), x ≠ 0 → P x = 0 →
      ∃ v : Source 2, fderiv ℝ V x v = 0 ∧
        fderiv ℝ (planeMapTargetRadiusSq H) x v ≠ 0 := by
  obtain ⟨β, hβ, hn, hker⟩ :=
    exists_injective_parametrization_with_kernel_of_irreducible (ofFunction P hP) hirr
  obtain ⟨G, hG, hG0, rfl, T, hT, hGin⟩ := hβ
  let C : ℂ → Source 2 := fun z => G (curveParameterEquiv.symm z)
  have hC : AnalyticAt ℂ C 0 :=
    hG.comp_of_eq (curveParameterEquiv.symm.analyticAt 0) (map_zero _)
  have hC0 : C 0 = 0 := by simp only [C, map_zero, hG0]
  have htC : Tendsto C (𝓝 0) (𝓝 (0 : Source 2)) :=
    hC0 ▸ hC.continuousAt.tendsto
  have htpar : Tendsto curveParameterEquiv.symm (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa only [map_zero] using curveParameterEquiv.symm.continuous.continuousAt.tendsto (x := 0)
  let B : ℂ → EuclideanSpace ℂ (Fin 3) := fun z =>
    (EuclideanSpace.equiv (Fin 3) ℂ).symm (H (C z))
  have hB : AnalyticAt ℂ B 0 :=
    ((EuclideanSpace.equiv (Fin 3) ℂ).symm.analyticAt _).comp (hH.comp_of_eq hC hC0)
  have hB0 : B 0 = 0 := by simp only [B, hC0, hH0, map_zero]
  have hBn : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), B z = 0 := by
    intro hb
    have he := hb.and ((htC.eventually hS).and (htpar.eventually hT))
    obtain ⟨z, ⟨hz, hzS, hzT⟩, hz0⟩ :=
      ((he.filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ({0} : Set ℂ)ᶜ)).exists
    have hHC : H (C z) = 0 :=
      (EuclideanSpace.equiv (Fin 3) ℂ).symm.injective (hz.trans (map_zero _).symm)
    have hCz : C z = 0 := hinj hzS (mem_of_mem_nhds hS) (hHC.trans hH0.symm)
    have hp : curveParameterEquiv.symm z = 0 :=
      hGin hzT (mem_of_mem_nhds hT) (hCz.trans hG0.symm)
    exact hz0 (curveParameterEquiv.symm.injective (hp.trans (map_zero _).symm))
  have hrad := eventually_nonconstant_curve_norm_radial_derivative_pos hB hB0 hBn
  have hpull : (PointedMapGerm.ofFunction G hG hG0).pullbackRingHom (ofFunction P hP) = 0 :=
    (hker _).mpr dvd_rfl
  have hPG : ∀ᶠ z in 𝓝 (0 : Source 1), P (G z) = 0 :=
    Filter.Germ.coe_eq.mp (congrArg (fun q : Germ 1 => q.1) hpull)
  have hVC : ∀ᶠ z in 𝓝 (0 : ℂ), V (C z) = 0 := by
    filter_upwards [htC.eventually hPV, htpar.eventually hPG] with z hz hp
    exact hz hp
  have hVCd : ∀ᶠ z in 𝓝 (0 : ℂ), fderiv ℝ (fun z => V (C z)) z = 0 := by
    have heq : (fun z => V (C z)) =ᶠ[𝓝 (0 : ℂ)] (fun _ => (0 : ℂ)) := hVC
    filter_upwards [heq.fderiv (𝕜 := ℝ)] with z hz
    simpa only [fderiv_const_apply] using hz
  have htan : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 →
      ∃ v : Source 2, fderiv ℝ V (C z) v = 0 ∧
        fderiv ℝ (planeMapTargetRadiusSq H) (C z) v ≠ 0 := by
    filter_upwards [hC.eventually_analyticAt, htC.eventually hV.eventually_analyticAt,
      htC.eventually hH.eventually_analyticAt, hVCd, hrad] with z hc hv hh hz hpos hzn
    have hcr := hc.differentiableAt.restrictScalars ℝ
    have hvr := hv.differentiableAt.restrictScalars ℝ
    have hrr := (contDiffAt_planeMapTargetRadiusSq hh).differentiableAt (by simp)
    refine ⟨fderiv ℝ C z z, ?_, ?_⟩
    · have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L z) hz
      change (fderiv ℝ (V ∘ C) z) z = 0 at he
      rw [fderiv_comp z hvr hcr] at he
      exact he
    · have hd : fderiv ℝ (fun w => ‖B w‖ ^ 2) z =
          (fderiv ℝ (planeMapTargetRadiusSq H) (C z)).comp (fderiv ℝ C z) :=
        (hrr.hasFDerivAt.comp z hcr.hasFDerivAt).fderiv
      have he := hpos hzn
      rw [hd] at he
      exact (ne_of_gt he)
  have htanG : ∀ᶠ z in 𝓝 (0 : Source 1), z ≠ 0 →
      ∃ v : Source 2, fderiv ℝ V (G z) v = 0 ∧
        fderiv ℝ (planeMapTargetRadiusSq H) (G z) v ≠ 0 := by
    have he : Tendsto curveParameterEquiv (𝓝 (0 : Source 1)) (𝓝 0) := by
      simpa only [map_zero] using curveParameterEquiv.continuous.continuousAt.tendsto (x := 0)
    filter_upwards [he.eventually htan] with z hz hzn
    have hne : curveParameterEquiv z ≠ 0 := fun h =>
      hzn (curveParameterEquiv.injective (h.trans (map_zero _).symm))
    simpa only [C, ContinuousLinearEquiv.symm_apply_apply] using hz hne
  obtain ⟨r, hr, hrT, _, _, _, hcover⟩ :=
    exists_curve_closedBall_image_eq_zero_set G hG hG0 hn P hP hker
      (T ∩ {z | z ≠ 0 → ∃ v : Source 2, fderiv ℝ V (G z) v = 0 ∧
        fderiv ℝ (planeMapTargetRadiusSq H) (G z) v ≠ 0})
      (inter_mem hT htanG) (hGin.mono inter_subset_left)
  filter_upwards [hcover] with x hx hxn hxP
  obtain ⟨z, hz, hzx⟩ := hx.mp hxP
  have hzn : z ≠ 0 := by
    rintro rfl
    exact hxn (hzx.symm.trans hG0)
  simpa only [hzx] using (hrT hz).2 hzn

/-- The actual Euclidean target-radius map is jointly submersive with the
first coordinate on the punctured reduced central section. -/
theorem eventually_planeMapTargetRadialPair_surjective
    (H : Source 2 → Source 3) (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (S : Set (Source 2)) (hS : S ∈ 𝓝 0) (hinj : InjOn H S)
    (hsq : Squarefree (ofFunction (fun x => H x 0) ((analyticAt_pi_iff.mp hH) 0))) :
    ∀ᶠ x in 𝓝 (0 : Source 2), x ≠ 0 → H x 0 = 0 →
      Surjective (fderiv ℝ (planeMapTargetRadialPair H) x) := by
  let V : Source 2 → ℂ := fun x => H x 0
  have hV : AnalyticAt ℂ V 0 := (analyticAt_pi_iff.mp hH) 0
  have hV0 : V 0 = 0 := by simp only [V, hH0, Pi.zero_apply]
  obtain ⟨s, P, hP, _, hirr, _, hcover, _⟩ :=
    exists_separated_branch_representatives_of_squarefree V hV hsq
  have hbranch (i : s) : ∀ᶠ x in 𝓝 (0 : Source 2), x ≠ 0 → P i x = 0 →
      ∃ v : Source 2, fderiv ℝ V x v = 0 ∧
        fderiv ℝ (planeMapTargetRadiusSq H) x v ≠ 0 :=
    eventually_targetRadius_tangent_of_irreducible H hH hH0 S hS hinj V (P i) hV (hP i)
      (hirr i) (hcover.mono fun _ hx hpx => hx.mpr ⟨i, hpx⟩)
  filter_upwards [Filter.eventually_all.mpr hbranch, hcover, hH.eventually_analyticAt,
    eventually_real_fderiv_surjective_of_squarefree V hV hV0 hsq] with x hbr hc ha hs hx0 hxV
  obtain ⟨i, hi⟩ := hc.mp hxV
  obtain ⟨v, hv, hrv⟩ := hbr i hx0 hi
  have hvr := ((analyticAt_pi_iff.mp ha) 0).differentiableAt.restrictScalars ℝ
  have hrr := (contDiffAt_planeMapTargetRadiusSq ha).differentiableAt (by simp)
  rw [show planeMapTargetRadialPair H = (fun x => (V x, planeMapTargetRadiusSq H x)) from rfl,
    (hvr.hasFDerivAt.prodMk hrr.hasFDerivAt).fderiv]
  exact DifferentialTopology.surjective_prod_of_surjective_of_nonzero_on_ker
    _ _ (hs hx0) v hv hrv

/-- Compact target-radius annuli in a fixed source ball give one uniform
section-level bound. Both source and target cutoffs remain in the statement. -/
theorem exists_uniform_planeMapTargetRadialPair_submersion
    (H : Source 2 → Source 3) (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (S : Set (Source 2)) (hS : S ∈ 𝓝 0) (hinj : InjOn H S)
    (hsq : Squarefree (ofFunction (fun x => H x 0) ((analyticAt_pi_iff.mp hH) 0)))
    (R₀ : ℝ) (hR₀ : 0 < R₀) :
    ∃ R : ℝ, 0 < R ∧ R ≤ R₀ ∧
      AnalyticOnNhd ℂ H (closedBall (0 : Source 2) R) ∧
      ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ closedBall (0 : Source 2) R,
          ε₁ ≤ ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (H x)‖ →
          ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (H x)‖ ≤ ε₂ →
          ‖H x 0‖ < δ → Surjective (fderiv ℝ (planeMapTargetRadialPair H) x) := by
  have hcentral := eventually_planeMapTargetRadialPair_surjective H hH hH0 S hS hinj hsq
  obtain ⟨r, hr, hgood⟩ := Metric.mem_nhds_iff.mp (hH.eventually_analyticAt.and hcentral)
  let R : ℝ := min R₀ (r / 2)
  have hR : 0 < R := lt_min hR₀ (half_pos hr)
  have hsub : closedBall (0 : Source 2) R ⊆ ball 0 r :=
    closedBall_subset_ball ((min_le_right _ _).trans_lt (half_lt_self hr))
  have ha : AnalyticOnNhd ℂ H (closedBall (0 : Source 2) R) :=
    fun x hx => (hgood (hsub hx)).1
  refine ⟨R, hR, min_le_left _ _, ha, ?_⟩
  intro ε₁ ε₂ hε₁
  let Q : Source 2 → EuclideanSpace ℂ (Fin 3) :=
    fun x => (EuclideanSpace.equiv (Fin 3) ℂ).symm (H x)
  have hQc : ContinuousOn Q (closedBall (0 : Source 2) R) :=
    (EuclideanSpace.equiv (Fin 3) ℂ).symm.continuous.comp_continuousOn ha.continuousOn
  have hJc : ContinuousOn (fun x => fderiv ℝ (planeMapTargetRadialPair H) x)
      (closedBall (0 : Source 2) R) := by
    intro x hx
    exact ((contDiffAt_planeMapTargetRadialPair (ha x hx)).fderiv_right
      (m := 0) (by simp)).continuousAt.continuousWithinAt
  have hVc : ContinuousOn (fun x => H x 0) (closedBall (0 : Source 2) R) :=
    (continuous_apply 0).comp_continuousOn ha.continuousOn
  let K : Set (Source 2) := closedBall 0 R ∩ Q ⁻¹' {y | ε₁ ≤ ‖y‖ ∧ ‖y‖ ≤ ε₂}
  have hKc : IsCompact K := by
    apply (isCompact_closedBall (0 : Source 2) R).of_isClosed_subset _ inter_subset_left
    exact hQc.preimage_isClosed_of_isClosed isClosed_closedBall
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
  let Bad : Set (Source 2) := K ∩ (fun x => fderiv ℝ (planeMapTargetRadialPair H) x) ⁻¹'
    {L : Source 2 →L[ℝ] ℂ × ℝ | ¬ Surjective L}
  have hBadc : IsCompact Bad := by
    apply hKc.of_isClosed_subset _ inter_subset_left
    exact (hJc.mono inter_subset_left).preimage_isClosed_of_isClosed hKc.isClosed
      isOpen_setOf_surjective_continuousLinearMap.isClosed_compl
  have hBadne : ∀ x ∈ Bad, H x 0 ≠ 0 := by
    intro x hx hv
    have hx0 : x ≠ 0 := by
      rintro rfl
      have he := hx.1.2.1
      simp only [Q, hH0, map_zero, norm_zero] at he
      linarith
    exact hx.2 ((hgood (hsub hx.1.1)).2 hx0 hv)
  obtain ⟨δ, hδ, hbound⟩ : ∃ δ > 0, ∀ x ∈ Bad, δ ≤ ‖H x 0‖ := by
    rcases Bad.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun x hx => by rw [he] at hx; exact hx.elim⟩
    · obtain ⟨x, hx, hmin⟩ := hBadc.exists_isMinOn hne
        ((hVc.mono (fun _ hx => hx.1.1)).norm)
      exact ⟨‖H x 0‖, norm_pos_iff.mpr (hBadne x hx), fun y hy => hmin hy⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hx hlow hupp hv
  by_contra hn
  exact (not_lt_of_ge (hbound x ⟨⟨hx, hlow, hupp⟩, hn⟩)) hv

namespace ResolutionSectionAssembly

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- The assembled map has one source radius on which every positive target
sphere has uniformly submersive nearby section boundaries. The target sphere
uses its Euclidean norm explicitly. -/
theorem exists_target_boundary_submersion (A : ResolutionSectionAssembly g hd hi) :
    ∃ R : ℝ, 0 < R ∧ R ≤ A.radius ∧
      AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) R) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : ℂ, ‖s‖ < δ → ∀ x ∈ closedBall (0 : Source 2) R,
          A.H x 0 = s → ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ = ε →
          Surjective (fderiv ℝ (planeMapTargetRadialPair A.H) x) := by
  obtain ⟨L, hL⟩ := A.exists_level_at_radius A.radius A.radius_pos le_rfl
  have hinj : InjOn A.H (ball (0 : Source 2) A.radius) := by
    simpa only [hL] using L.injective
  have hsq : Squarefree (ofFunction (fun x => A.H x 0)
      ((analyticAt_pi_iff.mp A.H_analytic) 0)) := by
    have heq : ofFunction (fun x => A.H x 0) ((analyticAt_pi_iff.mp A.H_analytic) 0) =
        A.sourceEquation := by
      rw [← A.sourceEquation_component]
      apply Subtype.ext
      exact (MapGerm.component_ofFunction A.H A.H_analytic 0).symm
    rw [heq]
    exact A.sourceEquation_squarefree
  obtain ⟨R, hR, hRA, ha, hbound⟩ :=
    exists_uniform_planeMapTargetRadialPair_submersion A.H A.H_analytic A.H_zero
      (ball 0 A.radius) (ball_mem_nhds _ A.radius_pos) hinj hsq A.radius A.radius_pos
  refine ⟨R, hR, hRA, ha, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hδbound⟩ := hbound ε ε hε
  refine ⟨δ, hδ, ?_⟩
  intro s hs x hx hxs hxe
  exact hδbound x hx hxe.ge hxe.le (hxs ▸ hs)

/-- Choose an actual assembled nonzero level satisfying the target-boundary
submersivity estimate, rather than adding a bound on its parameter as an
external assumption. -/
theorem exists_level_with_target_boundary (A : ResolutionSectionAssembly g hd hi)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ResolutionSectionLevel A,
      AnalyticOnNhd ℂ A.H (closedBall (0 : Source 2) L.radius) ∧
      ∀ x ∈ L.sourceLevel,
        ‖(EuclideanSpace.equiv (Fin 3) ℂ).symm (A.H x)‖ = ε →
        Surjective (fderiv ℝ (planeMapTargetRadialPair A.H) x) := by
  obtain ⟨R, hR, hRA, ha, hboundary⟩ := A.exists_target_boundary_submersion
  obtain ⟨δ, hδ, hsub⟩ := hboundary ε hε
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s‖ < δ := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hδ] with s hs
    exact mem_ball_zero_iff.mp hs
  have hne : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ≠ 0 := self_mem_nhdsWithin
  obtain ⟨s, ⟨hlevel, hsδ⟩, hs0⟩ :=
    (((A.levels R hR hRA).and hsmall).filter_mono nhdsWithin_le_nhds |>.and hne).exists
  obtain ⟨Z, hZ, hcard, hinj, hemb, hregular, hsingular, hsum⟩ := hlevel hs0
  let L : ResolutionSectionLevel A :=
    ⟨R, hR, hRA, s, hs0, Z, hZ, hcard, hinj, hemb, hregular, hsingular, hsum⟩
  exact ⟨L, ha, fun x hx hxe => hsub s hsδ x hx.1 hx.2 hxe⟩

end ResolutionSectionAssembly

end OnLeConjecture.Analytic
