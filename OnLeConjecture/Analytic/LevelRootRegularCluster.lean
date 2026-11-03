/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelRootCriticalStrips

/-!
# The cluster at a regular point of a fibre

This module proves the pointwise cluster data (`LevelRootCriticalStrips.lean`) at the points of a
critical fibre at which the map `levelBaseMap A h : x ↦ (H x 0, h (H x))` has an injective
differential: by the inverse function theorem, over every small circle around the critical value
exactly one root comes from a small ball around the point, so the cluster has one strand and the
empty (Coxeter) word. Such a point is not a singular point of the level, since the differential of
`H` is not injective at the singular points.

`pointClusterStatement_of_critical` reduces `PointClusterStatement` to
`CriticalPointClusterStatement`, the same statement at the points of the critical fibres where the
differential of `levelBaseMap A h` is not injective: the singular points and the critical points of
`h ∘ H` on the smooth part of the level.
-/

@[expose] public noncomputable section

open Set Function Metric Real Filter
open scoped Topology

namespace OnLeConjecture.Analytic

open KnotTheory PlaneCurve SignedAdjacentWord OnLeConjecture.Analytic.Germ

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

namespace LevelProjectionSetup

variable {A : ResolutionSectionAssembly g hd hi} {L : ResolutionSectionLevel A}
  (P : LevelProjectionSetup A L)

/-- The derivative of `levelBaseMap`. -/
theorem hasFDerivAt_levelBaseMap {x : Source 2} {H' : Source 2 →L[ℂ] Source 3}
    (hH : HasFDerivAt A.H H' x) :
    HasFDerivAt (levelBaseMap A P.baseCoord)
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).comp H').prod
        (P.baseCoord.comp H')) x :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).hasFDerivAt.comp x hH).prodMk
    (P.baseCoord.hasFDerivAt.comp x hH)

theorem analyticAt_levelBaseMap {x : Source 2} (hH : AnalyticAt ℂ A.H x) :
    AnalyticAt ℂ (levelBaseMap A P.baseCoord) x :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).analyticAt _ |>.comp hH).prod
    (P.baseCoord.analyticAt _ |>.comp hH)

/-- At a singular point the differential of `levelBaseMap` is not injective. -/
theorem not_injective_fderiv_of_point (hP : P.SetupProperties) (j : Fin L.points.card) :
    ¬ Injective (fderiv ℂ (levelBaseMap A P.baseCoord) (L.point j)) := by
  intro hinj
  have hQ : L.point j ∈ L.points := Finset.coe_mem _
  obtain ⟨hQb, -, hni⟩ := (L.points_iff _).mp hQ
  have hH := hP.outer.analyticAt _ (ball_subset_closedBall hQb)
  have hd := hH.differentiableAt.hasFDerivAt
  rw [(P.hasFDerivAt_levelBaseMap hd).fderiv] at hinj
  apply hni
  intro v w hvw
  apply hinj
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [hvw]

/-- **The cluster at a regular point.** -/
theorem localClusterAt_of_regular (hP : P.SetupProperties) {c : ℂ} {x : Source 2}
    (hx : x ∈ P.levelFibre c)
    (hreg : Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x)) :
    P.LocalClusterAt c x 1 [] := by
  intro δ hδ
  set F := levelBaseMap A P.baseCoord
  have hHx := hP.outer.analyticAt x (ball_subset_closedBall hx.1)
  have hFa := P.analyticAt_levelBaseMap hHx
  have hstrict : HasStrictFDerivAt F (fderiv ℂ F x) x := hFa.hasStrictFDerivAt
  have hfr : Module.finrank ℂ (Source 2) = Module.finrank ℂ (ℂ × ℂ) := by
    simp [Module.finrank_prod]
  have hsurj : Surjective (fderiv ℂ F x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr
      (f := (fderiv ℂ F x : Source 2 →ₗ[ℂ] ℂ × ℂ))).mp hreg
  set f' : Source 2 ≃L[ℂ] ℂ × ℂ := ContinuousLinearEquiv.ofBijective (fderiv ℂ F x)
    (LinearMap.ker_eq_bot.mpr hreg) (LinearMap.range_eq_top.mpr hsurj)
  have hs' : HasStrictFDerivAt F (f' : Source 2 →L[ℂ] ℂ × ℂ) x := by
    have : (f' : Source 2 →L[ℂ] ℂ × ℂ) = fderiv ℂ F x :=
      ContinuousLinearMap.ext fun v => rfl
    rw [this]; exact hstrict
  set Φ := hs'.toOpenPartialHomeomorph F
  have hxs : x ∈ Φ.source := hs'.mem_toOpenPartialHomeomorph_source
  have hFt : F x ∈ Φ.target := hs'.image_mem_toOpenPartialHomeomorph_target
  have hΦ : ∀ y, Φ y = F y := fun y => by
    rw [hs'.toOpenPartialHomeomorph_coe]
  -- The ball around `x`.
  have hζc : ContinuousAt (fun y => P.fibreCoord (A.H y)) x :=
    P.fibreCoord.continuous.continuousAt.comp hHx.continuousAt
  have hN : Φ.source ∩ ball (0 : Source 2) L.radius ∩
      {y | ‖P.fibreCoord (A.H y) - P.fibreCoord (A.H x)‖ < δ} ∈ 𝓝 x := by
    refine inter_mem (inter_mem (Φ.open_source.mem_nhds hxs) (isOpen_ball.mem_nhds hx.1)) ?_
    have := hζc.preimage_mem_nhds (ball_mem_nhds (P.fibreCoord (A.H x)) hδ)
    filter_upwards [this] with y hy
    simpa [dist_eq_norm] using hy
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.mp hN
  -- The radius of the circles.
  have hsymm : ContinuousAt Φ.symm (F x) := Φ.continuousAt_symm hFt
  have hΦx : Φ.symm (F x) = x := by
    rw [← hΦ x]; exact Φ.left_inv hxs
  have hev : ∀ᶠ w in 𝓝 (F x), w ∈ Φ.target ∧ Φ.symm w ∈ ball x ε := by
    refine (Φ.open_target.eventually_mem hFt).and ?_
    have := hsymm.eventually_mem (ball_mem_nhds (Φ.symm (F x)) hε)
    rw [hΦx] at this
    exact this
  have hFxeq : F x = (L.parameter, c) := Prod.ext hx.2.1 hx.2.2
  have hpath : Tendsto (fun c' : ℂ => (L.parameter, c')) (𝓝 c) (𝓝 (F x)) := by
    rw [hFxeq]
    exact (continuous_const.prodMk continuous_id).tendsto c
  obtain ⟨r₀, hr₀, hr₀spec⟩ := Metric.eventually_nhds_iff.mp (hpath.eventually hev)
  refine ⟨ε, hε, r₀, hr₀, fun r hr hrr₀ => ⟨fun θ => ?_, fun θ y hy => ?_, fun b K _ W _ => ?_⟩⟩
  · -- Exactly one root comes from the ball.
    set c' := c + circlePath r θ
    have hc' : dist c' c < r₀ := by
      rw [dist_eq_norm, show c' - c = circlePath r θ by simp [c'], norm_circlePath hr.le]
      exact hrr₀
    obtain ⟨ht, hball⟩ := hr₀spec hc'
    set y₀ := Φ.symm (L.parameter, c')
    have hy₀s : y₀ ∈ Φ.source := (hεN hball).1.1
    have hFy₀ : F y₀ = (L.parameter, c') := by rw [← hΦ]; exact Φ.right_inv ht
    have hy₀F : y₀ ∈ P.levelFibre c' ∩ ball x ε :=
      ⟨⟨(hεN hball).1.2, congrArg Prod.fst hFy₀, congrArg Prod.snd hFy₀⟩, hball⟩
    have huniq : P.levelFibre c' ∩ ball x ε = {y₀} := by
      ext y
      constructor
      · rintro ⟨hy, hyb⟩
        have hFy : F y = (L.parameter, c') := Prod.ext hy.2.1 hy.2.2
        apply Φ.injOn (hεN hyb).1.1 hy₀s
        rw [hΦ, hΦ, hFy, hFy₀]
      · rintro rfl; exact hy₀F
    rw [localRoots, huniq, image_singleton, ncard_singleton]
  · exact (hεN hy.2).2
  · rw [eq_nil_of_zero W]
    exact SignedBraidConj.refl _

/-- **The cluster data at a regular point.** -/
def pointClusterData_of_regular (hP : P.SetupProperties) {c : ℂ} {x : Source 2}
    (hx : x ∈ P.levelFibre c)
    (hreg : Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x)) : P.PointClusterData c x where
  degree := 1
  word := []
  kind := none
  holds := P.localClusterAt_of_regular hP hx hreg
  kind_singular := fun j hj => by simp at hj
  kind_none := fun _ => rfl
  point_kind := fun j hj => by
    subst hj
    exact absurd hreg (P.not_injective_fderiv_of_point hP j)
  critical := fun h => absurd hreg h

end LevelProjectionSetup

/-- **The pointwise cluster statement at the critical points**: for every setup with
`SetupProperties`, every point of every critical fibre at which the differential of
`levelBaseMap A h` is not injective carries cluster data. -/
def CriticalPointClusterStatement : Prop :=
  ∀ (g : PointedMapGerm 2 3) (hd : g.differential = 0) (hi : g.HasInjectiveRepresentative)
    (A : ResolutionSectionAssembly g hd hi) (L : ResolutionSectionLevel A)
    (P : LevelProjectionSetup A L), P.SetupProperties →
      ∀ c ∈ P.critical, ∀ x ∈ P.levelFibre c,
        ¬ Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x) →
          Nonempty (P.PointClusterData c x)

theorem pointClusterStatement_of_critical (h : CriticalPointClusterStatement) :
    PointClusterStatement := by
  intro g hd hi A L P hP c hc x hx
  by_cases hreg : Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x)
  · exact ⟨P.pointClusterData_of_regular hP hx hreg⟩
  · exact h g hd hi A L P hP c hc x hx hreg

/-- **The pointwise cluster statement from its three cases.** The regular points are treated here
(`pointClusterData_of_regular`); the smooth critical points and the singular points are the two
hypotheses. -/
theorem pointClusterStatement_of_cases
    (hSmooth : ∀ {g : PointedMapGerm 2 3} {hd : g.differential = 0}
      {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}
      {L : ResolutionSectionLevel A} (P : LevelProjectionSetup A L), P.SetupProperties →
      ∀ {c : ℂ} {x : Source 2}, c ∈ P.critical → x ∈ P.levelFibre c →
        ¬ Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x) → (∀ j, x ≠ L.point j) →
          Nonempty (P.PointClusterData c x))
    (hSingular : ∀ {g : PointedMapGerm 2 3} {hd : g.differential = 0}
      {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}
      {L : ResolutionSectionLevel A} (P : LevelProjectionSetup A L), P.SetupProperties →
      ∀ j : Fin L.points.card,
        Nonempty (P.PointClusterData (P.baseCoord (A.H (L.point j))) (L.point j))) :
    PointClusterStatement := by
  refine pointClusterStatement_of_critical fun g hd hi A L P hP c hc x hx hcrit => ?_
  by_cases hpt : ∃ j, x = L.point j
  · obtain ⟨j, rfl⟩ := hpt
    have hcx : c = P.baseCoord (A.H (L.point j)) := hx.2.2.symm
    subst hcx
    exact hSingular P hP j
  · push Not at hpt
    exact hSmooth P hP hc hx hcrit hpt

end OnLeConjecture.Analytic
