/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelRootRegularCluster
public import OnLeConjecture.Analytic.LevelPointSmoothBraid

/-!
# The cluster at a smooth critical point of a fibre: the Coxeter word

This module proves the pointwise cluster data (`LevelRootCriticalStrips.lean`) at a point `x` of
a critical fibre `P.levelFibre c` which is not a singular point `L.point j` and at which the
differential of `levelBaseMap A h : y ↦ (H y 0, h (H y))` is not injective, that is, at a smooth
critical point of `h ∘ H` on the level. This is the case of an ordinary ramification point in the
subsection "Local factors, without a generic-Morse projection" of Section 3 of the written proof
of Statement E (`statement-E-complete-proof.tex`). The cluster has `d ≥ 2` strands and the
Coxeter word `σ_0 ⋯ σ_{d-2}`.

Write `s = L.parameter`, `h = P.baseCoord`, `ζ = P.fibreCoord` and `ζ₀ = ζ (H x)`.

* Since `x` is not a singular point, the differential `H'` of `H` at `x` is injective. The
  differential of `y ↦ H y 0` at `x` is nonzero (`L.regular`), so its kernel is a line. A
  nonzero vector `w` of the kernel of the differential of `levelBaseMap` spans this line, and
  `ζ (H' w) ≠ 0` because `(y₀, h, ζ)` are linear coordinates. Hence the map
  `F : y ↦ (H y 0, ζ (H y))` has an invertible differential at `x`, and `h (H' v) = 0` for every
  `v` of the line.
* By the analytic inverse function theorem, `G : ζ ↦ F⁻¹ (s, ζ)` parametrizes the level near `x`
  by the fibre coordinate, analytically. The function `φ = h ∘ H ∘ G` satisfies `φ ζ₀ = c` and
  `φ' ζ₀ = 0`. It is not constant near `ζ₀`, since the fibre over `c` is finite
  (`SetupProperties.fibre_finite`). Hence `φ = c + q^d` near `ζ₀` for some `d ≥ 2` and an analytic
  `q` with `q ζ₀ = 0` and `q' ζ₀ ≠ 0` (`LevelPointSmooth.exists_pow_normalForm`, using an analytic
  `d`-th root of a unit). The integer `d` is the order of vanishing of `φ - c` at `ζ₀`.
* Let `Y` be the local inverse of `q`. Over the circle `c + r e^{iθ}` the roots coming from a
  small ball around `x` are exactly the `d` points `Y (r^{1/d} e^{i(θ - 2πk)/d})`, and these form
  a closed braid represented by the Coxeter word (`exists_radius_isRepresented_coxeter`,
  `LevelPointSmoothBraid.lean`). Every labelling of the roots differs from this one by a constant
  permutation, so every path word is conjugate to the Coxeter word.

Main results:

* `LevelProjectionSetup.exists_localClusterAt_coxeter_of_smoothCritical`: the cluster at a
  smooth critical point has `d ≥ 2` strands and the Coxeter word.
* `LevelProjectionSetup.pointClusterData_of_smoothCritical`: the hypothesis `hSmooth` of
  `pointClusterStatement_of_cases` (`LevelRootRegularCluster.lean`).
* `pointClusterStatement_of_singular`: `PointClusterStatement` from the singular case alone.
-/

@[expose] public noncomputable section

open Set Function Metric Real Filter
open scoped Topology

namespace OnLeConjecture.Analytic

open KnotTheory PlaneCurve SignedAdjacentWord OnLeConjecture.Analytic.Germ

namespace LevelPointSmooth

/-- In the kernel of a nonzero linear form on `Source 2`, every vector is a multiple of a given
nonzero vector of the kernel. -/
theorem exists_eq_smul_of_mem_ker {ℓ : Source 2 →L[ℂ] ℂ} (hℓ : ℓ ≠ 0) {v w : Source 2}
    (hv : ℓ v = 0) (hw : ℓ w = 0) (hw0 : w ≠ 0) : ∃ μ : ℂ, v = μ • w := by
  obtain ⟨e, he⟩ : ∃ e, ℓ e ≠ 0 := by
    by_contra h
    exact hℓ (ContinuousLinearMap.ext fun e => not_not.mp fun h' => h ⟨e, h'⟩)
  set ℓ' : Source 2 →ₗ[ℂ] ℂ := ℓ.toLinearMap with hℓ'
  have hsurj : Surjective ℓ' := fun z => ⟨(z / ℓ e) • e, by
    rw [hℓ', ContinuousLinearMap.coe_coe, map_smul, smul_eq_mul, div_mul_cancel₀ z he]⟩
  have hrank : Module.finrank ℂ (LinearMap.ker ℓ') = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker ℓ'
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Module.finrank_fin_fun] at h
    omega
  have hw' : (⟨w, LinearMap.mem_ker.mpr hw⟩ : LinearMap.ker ℓ') ≠ 0 := fun h =>
    hw0 (congrArg Subtype.val h)
  obtain ⟨μ, hμ⟩ := (finrank_eq_one_iff_of_nonzero' _ hw').mp hrank
    ⟨v, LinearMap.mem_ker.mpr hv⟩
  exact ⟨μ, (congrArg Subtype.val hμ).symm⟩

/-- **Normal form at a critical point of a holomorphic function of one variable.** A function
`φ`, analytic at `ζ₀`, with `φ ζ₀ = c`, `φ' ζ₀ = 0`, and not constant near `ζ₀`, is
`c + q^d` near `ζ₀` for some `d ≥ 2` and an analytic `q` with `q ζ₀ = 0` and `q' ζ₀ ≠ 0`. -/
theorem exists_pow_normalForm {φ : ℂ → ℂ} {ζ₀ c : ℂ} (hφ : AnalyticAt ℂ φ ζ₀) (hφ0 : φ ζ₀ = c)
    (hφ' : deriv φ ζ₀ = 0) (hnc : ¬ ∀ᶠ ζ in 𝓝 ζ₀, φ ζ = c) :
    ∃ d : ℕ, 2 ≤ d ∧ ∃ q : ℂ → ℂ, AnalyticAt ℂ q ζ₀ ∧ q ζ₀ = 0 ∧ deriv q ζ₀ ≠ 0 ∧
      ∀ᶠ ζ in 𝓝 ζ₀, φ ζ = c + q ζ ^ d := by
  have hf : AnalyticAt ℂ (fun ζ => φ ζ - c) ζ₀ := hφ.sub analyticAt_const
  have hnz : ¬ ∀ᶠ ζ in 𝓝 ζ₀, φ ζ - c = 0 := fun h =>
    hnc (h.mono fun ζ hζ => sub_eq_zero.mp hζ)
  obtain ⟨n, u, hu, hu0, hfu⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h := hfu.self_of_nhds
    rw [hφ0, sub_self, pow_zero, one_smul] at h
    exact hu0 h.symm
  have hn1 : n ≠ 1 := by
    rintro rfl
    have hd1 : HasDerivAt (fun ζ => (ζ - ζ₀) * u ζ) (u ζ₀) ζ₀ :=
      (((hasDerivAt_id' (x := ζ₀)).sub_const ζ₀).mul hu.differentiableAt.hasDerivAt).congr_deriv
        (by simp)
    have hd2 : HasDerivAt (fun ζ => φ ζ - c) (u ζ₀) ζ₀ :=
      hd1.congr_of_eventuallyEq (hfu.mono fun z hz => by
        change φ z - c = (z - ζ₀) * u z
        rw [hz, pow_one, smul_eq_mul])
    have hd3 : HasDerivAt (fun ζ => φ ζ - c) 0 ζ₀ := by
      have := hφ.differentiableAt.hasDerivAt.sub_const c
      rwa [hφ'] at this
    exact hu0 (hd2.unique hd3)
  refine ⟨n, by omega, ?_⟩
  -- An analytic `n`-th root of `u`.
  set κ : ℂ := u ζ₀ ^ ((n : ℂ)⁻¹) with hκdef
  have hκn : κ ^ n = u ζ₀ := Complex.cpow_nat_inv_pow _ hn0
  have hκ : κ ≠ 0 := fun h => hu0 (by rw [← hκn, h, zero_pow hn0])
  set w : ℂ → ℂ := fun ζ => κ * (u ζ / u ζ₀) ^ ((n : ℂ)⁻¹) with hwdef
  have hwa : AnalyticAt ℂ w ζ₀ := by
    refine analyticAt_const.mul ((hu.div analyticAt_const hu0).cpow analyticAt_const ?_)
    change u ζ₀ / u ζ₀ ∈ Complex.slitPlane
    rw [div_self hu0]
    exact Complex.one_mem_slitPlane
  have hw0 : w ζ₀ = κ := by simp only [hwdef, div_self hu0, Complex.one_cpow, mul_one]
  have hwn : ∀ ζ, w ζ ^ n = u ζ := fun ζ => by
    rw [hwdef, mul_pow, hκn, Complex.cpow_nat_inv_pow _ hn0, mul_div_cancel₀ _ hu0]
  set q : ℂ → ℂ := fun ζ => (ζ - ζ₀) * w ζ with hqdef
  have hqa : AnalyticAt ℂ q ζ₀ := (analyticAt_id.sub analyticAt_const).mul hwa
  have hqd : HasDerivAt q κ ζ₀ :=
    (((hasDerivAt_id' (x := ζ₀)).sub_const ζ₀).mul hwa.differentiableAt.hasDerivAt).congr_deriv
      (by simp [hw0])
  refine ⟨q, hqa, by simp [hqdef], by rw [hqd.deriv]; exact hκ, ?_⟩
  filter_upwards [hfu] with ζ hζ
  rw [hqdef, mul_pow, hwn, ← smul_eq_mul, ← hζ]
  ring

end LevelPointSmooth

open LevelPointSmooth

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

namespace LevelProjectionSetup

variable {A : ResolutionSectionAssembly g hd hi} {L : ResolutionSectionLevel A}
  (P : LevelProjectionSetup A L)

/-- **The cluster at a smooth critical point.** At a point `x` of the fibre over a critical
value `c` which is not a singular point and at which the differential of `levelBaseMap` is not
injective, the cluster has `d ≥ 2` strands and the Coxeter word. -/
theorem exists_localClusterAt_coxeter_of_smoothCritical (hP : P.SetupProperties) {c : ℂ}
    {x : Source 2} (hc : c ∈ P.critical) (hx : x ∈ P.levelFibre c)
    (hcrit : ¬ Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x))
    (hpt : ∀ j, x ≠ L.point j) :
    ∃ d : ℕ, 2 ≤ d ∧ P.LocalClusterAt c x d (coxeterWord d) := by
  classical
  set s := L.parameter with hsdef
  set ζ₀ := P.fibreCoord (A.H x) with hζ₀def
  /- Step 1: the differential at `x`. -/
  have hHx := hP.outer.analyticAt x (ball_subset_closedBall hx.1)
  have hHd : HasFDerivAt A.H (fderiv ℂ A.H x) x := hHx.differentiableAt.hasFDerivAt
  set H' := fderiv ℂ A.H x with hH'def
  have hv0 : HasFDerivAt (fun y => A.H y 0)
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).comp H') x :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).hasFDerivAt.comp x hHd
  have hℓ : (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).comp H' ≠ 0 := by
    have h := (L.regular x hx.1 hx.2.1).1
    rwa [hv0.fderiv] at h
  have hℓapp : ∀ v, (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).comp H' v =
      H' v 0 := fun v => rfl
  have hHinj : Injective H' := by
    by_contra hni
    have hxp : x ∈ L.points := (L.points_iff x).mpr ⟨hx.1, hx.2.1, hni⟩
    exact hpt (L.points.equivFin ⟨x, hxp⟩) (by simp [ResolutionSectionLevel.point])
  rw [(P.hasFDerivAt_levelBaseMap hHd).fderiv] at hcrit
  obtain ⟨w, hw0, hw1, hw2⟩ : ∃ w : Source 2, w ≠ 0 ∧ H' w 0 = 0 ∧ P.baseCoord (H' w) = 0 := by
    simp only [Injective, not_forall] at hcrit
    obtain ⟨a, b, hab, hne⟩ := hcrit
    have hB0 : (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).comp H').prod
        (P.baseCoord.comp H')) (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    exact ⟨a - b, sub_ne_zero.mpr hne, congrArg Prod.fst hB0, congrArg Prod.snd hB0⟩
  have hζw : P.fibreCoord (H' w) ≠ 0 := by
    intro h0
    apply hw0
    apply hHinj
    rw [map_zero]
    apply P.coordinates
    change (H' w 0, P.baseCoord (H' w), P.fibreCoord (H' w)) =
      ((0 : Source 3) 0, P.baseCoord 0, P.fibreCoord 0)
    rw [hw1, hw2, h0, map_zero, map_zero]
    rfl
  have hker : ∀ v : Source 2, H' v 0 = 0 → ∃ μ : ℂ, v = μ • w := fun v hv =>
    exists_eq_smul_of_mem_ker hℓ (by rw [hℓapp]; exact hv) (by rw [hℓapp]; exact hw1) hw0
  have hbase : ∀ v : Source 2, H' v 0 = 0 → P.baseCoord (H' v) = 0 := by
    intro v hv
    obtain ⟨μ, rfl⟩ := hker v hv
    rw [map_smul, map_smul, hw2, smul_zero]
  /- Step 2: the chart `F = (H · 0, ζ ∘ H)` of the source near `x`. -/
  set F : Source 2 → ℂ × ℂ := fun y => (A.H y 0, P.fibreCoord (A.H y)) with hFdef
  set F' : Source 2 →L[ℂ] ℂ × ℂ :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).comp H').prod
      (P.fibreCoord.comp H') with hF'def
  have hF : HasFDerivAt F F' x :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).hasFDerivAt.comp x
      hHd).prodMk (P.fibreCoord.hasFDerivAt.comp x hHd)
  have hFinj : Injective F' := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : H' v 0 = 0 := congrArg Prod.fst hv
    have h2 : P.fibreCoord (H' v) = 0 := congrArg Prod.snd hv
    obtain ⟨μ, rfl⟩ := hker v h1
    rw [map_smul, map_smul, smul_eq_mul] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · rw [h, zero_smul]
    · exact absurd h hζw
  have hFa : AnalyticAt ℂ F x :=
    (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).analyticAt _).comp
      hHx).prod ((P.fibreCoord.analyticAt _).comp hHx)
  have hfr : Module.finrank ℂ (Source 2) = Module.finrank ℂ (ℂ × ℂ) := by
    simp [Module.finrank_prod]
  have hsurj : Surjective F' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr
      (f := (F' : Source 2 →ₗ[ℂ] ℂ × ℂ))).mp hFinj
  set f' : Source 2 ≃L[ℂ] ℂ × ℂ := ContinuousLinearEquiv.ofBijective F'
    (LinearMap.ker_eq_bot.mpr hFinj) (LinearMap.range_eq_top.mpr hsurj) with hf'def
  have hFeq : fderiv ℂ F x = (f' : Source 2 →L[ℂ] ℂ × ℂ) := by
    rw [hF.fderiv]
    exact ContinuousLinearMap.ext fun v => rfl
  have hs' : HasStrictFDerivAt F (f' : Source 2 →L[ℂ] ℂ × ℂ) x := by
    rw [← hFeq]
    exact hFa.hasStrictFDerivAt
  set Φ := hs'.toOpenPartialHomeomorph F with hΦdef
  have hΦF : (Φ : Source 2 → ℂ × ℂ) = F := hs'.toOpenPartialHomeomorph_coe
  have hxs : x ∈ Φ.source := hs'.mem_toOpenPartialHomeomorph_source
  have hFx : F x = (s, ζ₀) := Prod.ext hx.2.1 rfl
  have hFt : (s, ζ₀) ∈ Φ.target := by
    rw [← hFx]
    exact hs'.image_mem_toOpenPartialHomeomorph_target
  have hΦsa : AnalyticAt ℂ Φ.symm (s, ζ₀) := by
    have h := Φ.analyticAt_symm' (i := f') hxs (by rw [hΦF]; exact hFa) (by rw [hΦF]; exact hFeq)
    rwa [hΦF, hFx] at h
  have hΦx : Φ.symm (s, ζ₀) = x := by
    rw [← hFx, ← hΦF]
    exact Φ.left_inv hxs
  /- Step 3: the level near `x` as a graph over the fibre coordinate. -/
  set G : ℂ → Source 2 := fun ζ => Φ.symm (s, ζ) with hGdef
  have hGa : AnalyticAt ℂ G ζ₀ := hΦsa.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hGζ₀ : G ζ₀ = x := hΦx
  have hGev : ∀ᶠ ζ in 𝓝 ζ₀, (s, ζ) ∈ Φ.target := by
    have ht : Tendsto (fun ζ : ℂ => (s, ζ)) (𝓝 ζ₀) (𝓝 (s, ζ₀)) :=
      (continuous_const.prodMk continuous_id).tendsto ζ₀
    exact ht.eventually_mem (Φ.open_target.mem_nhds hFt)
  have hFG : ∀ ζ, (s, ζ) ∈ Φ.target → A.H (G ζ) 0 = s ∧ P.fibreCoord (A.H (G ζ)) = ζ := by
    intro ζ hζ
    have h := Φ.right_inv hζ
    rw [hΦF] at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  set φ : ℂ → ℂ := fun ζ => P.baseCoord (A.H (G ζ)) with hφdef
  have hφa : AnalyticAt ℂ φ ζ₀ :=
    (P.baseCoord.analyticAt _).comp (hHx.comp_of_eq hGa hGζ₀)
  have hφζ₀ : φ ζ₀ = c := by
    change P.baseCoord (A.H (G ζ₀)) = c
    rw [hGζ₀]
    exact hx.2.2
  have hGd : HasDerivAt G (deriv G ζ₀) ζ₀ := hGa.differentiableAt.hasDerivAt
  have hlev : HasDerivAt (fun ζ => A.H (G ζ) 0) (H' (deriv G ζ₀) 0) ζ₀ :=
    hv0.comp_hasDerivAt_of_eq (x := ζ₀) hGd hGζ₀.symm
  have hlev0 : HasDerivAt (fun ζ => A.H (G ζ) 0) 0 ζ₀ :=
    (hasDerivAt_const ζ₀ s).congr_of_eventuallyEq (hGev.mono fun ζ hζ => (hFG ζ hζ).1)
  have hwG : H' (deriv G ζ₀) 0 = 0 := hlev.unique hlev0
  have hφd : HasDerivAt φ (P.baseCoord (H' (deriv G ζ₀))) ζ₀ :=
    (P.baseCoord.hasFDerivAt.comp x hHd).comp_hasDerivAt_of_eq (x := ζ₀) hGd hGζ₀.symm
  have hφ' : deriv φ ζ₀ = 0 := by
    rw [hφd.deriv]
    exact hbase _ hwG
  /- Step 4: `φ` is not constant near `ζ₀`, since the fibre over `c` is finite. -/
  have hcball : c ∈ ball (0 : ℂ) P.radius := ((hP.critical_iff c).mp hc).1
  have hnc : ¬ ∀ᶠ ζ in 𝓝 ζ₀, φ ζ = c := by
    intro hev
    have hGb : ∀ᶠ ζ in 𝓝 ζ₀, G ζ ∈ ball (0 : Source 2) L.radius :=
      hGa.continuousAt.eventually_mem (by rw [hGζ₀]; exact isOpen_ball.mem_nhds hx.1)
    obtain ⟨U, hU, hUsub⟩ := (hev.and (hGev.and hGb)).exists_mem
    have hinj : InjOn G U := by
      intro ζ hζ ζ' hζ' he
      rw [← (hFG ζ (hUsub ζ hζ).2.1).2, ← (hFG ζ' (hUsub ζ' hζ').2.1).2, he]
    have hmaps : MapsTo G U (P.levelFibre c) := fun ζ hζ =>
      ⟨(hUsub ζ hζ).2.2, (hFG ζ (hUsub ζ hζ).2.1).1, (hUsub ζ hζ).1⟩
    exact (Set.infinite_of_injOn_mapsTo hinj hmaps (infinite_of_mem_nhds ζ₀ hU))
      (hP.fibre_finite c hcball)
  /- Step 5: the normal form `φ = c + q^d` and the local inverse `Y` of `q`. -/
  obtain ⟨d, hd2, q, hqa, hq0, hq', hφq⟩ := exists_pow_normalForm hφa hφζ₀ hφ' hnc
  have hd0 : 0 < d := by omega
  refine ⟨d, hd2, ?_⟩
  have hqs : HasStrictDerivAt q (deriv q ζ₀) ζ₀ := hqa.hasStrictDerivAt
  set Ψ := (hqs.hasStrictFDerivAt_equiv hq').toOpenPartialHomeomorph q with hΨdef
  have hΨq : (Ψ : ℂ → ℂ) = q := HasStrictFDerivAt.toOpenPartialHomeomorph_coe _
  have hζ₀Ψ : ζ₀ ∈ Ψ.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  have h0Ψ : (0 : ℂ) ∈ Ψ.target := by
    have h := HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target
      (hqs.hasStrictFDerivAt_equiv hq')
    rwa [hq0] at h
  have hY0 : Ψ.symm 0 = ζ₀ := by
    rw [← hq0, ← hΨq]
    exact Ψ.left_inv hζ₀Ψ
  have hYd : HasStrictDerivAt Ψ.symm (deriv q ζ₀)⁻¹ 0 :=
    Ψ.hasStrictDerivAt_symm h0Ψ hq' (by rw [hY0, hΨq]; exact hqs)
  obtain ⟨ρb, hρb, hbraid⟩ := exists_radius_isRepresented_coxeter hd2 (inv_ne_zero hq') hYd
  /- Step 6: the radii. -/
  intro δ hδ
  set N : Set ℂ := {ζ | (s, ζ) ∈ Φ.target ∧ φ ζ = c + q ζ ^ d ∧ ζ ∈ Ψ.source} with hNdef
  have hN : N ∈ 𝓝 ζ₀ := hGev.and (hφq.and (Ψ.open_source.eventually_mem hζ₀Ψ))
  have hζc : ContinuousAt (fun y => P.fibreCoord (A.H y)) x :=
    P.fibreCoord.continuous.continuousAt.comp hHx.continuousAt
  have hM : Φ.source ∩ ball (0 : Source 2) L.radius ∩
      {y | ‖P.fibreCoord (A.H y) - ζ₀‖ < δ ∧ P.fibreCoord (A.H y) ∈ N} ∈ 𝓝 x := by
    refine inter_mem (inter_mem (Φ.open_source.mem_nhds hxs) (isOpen_ball.mem_nhds hx.1)) ?_
    have h1 := hζc.preimage_mem_nhds (ball_mem_nhds ζ₀ hδ)
    have h2 := hζc.preimage_mem_nhds hN
    filter_upwards [h1, h2] with y hy1 hy2
    exact ⟨by simpa [dist_eq_norm] using hy1, hy2⟩
  obtain ⟨ε, hε, hεM⟩ := Metric.mem_nhds_iff.mp hM
  have hG' : G ⁻¹' ball x ε ∈ 𝓝 ζ₀ :=
    hGa.continuousAt.preimage_mem_nhds (by rw [hGζ₀]; exact ball_mem_nhds x hε)
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ Ψ.target ∧ Ψ.symm z ∈ N ∧ G (Ψ.symm z) ∈ ball x ε := by
    refine (Ψ.open_target.eventually_mem h0Ψ).and ?_
    have ht : Tendsto Ψ.symm (𝓝 0) (𝓝 ζ₀) := by
      rw [← hY0]
      exact Ψ.continuousAt_symm h0Ψ
    exact (ht.eventually_mem (inter_mem hN hG')).mono fun z hz => ⟨hz.1, hz.2⟩
  obtain ⟨r₁, hr₁, hr₁spec⟩ := Metric.eventually_nhds_iff.mp hev
  set ρ' := min r₁ ρb with hρ'def
  have hρ' : 0 < ρ' := lt_min hr₁ hρb
  refine ⟨ε, hε, ρ' ^ d, pow_pos hρ' d, fun r hr hrr₀ => ?_⟩
  set r' : ℝ := r ^ ((d : ℝ)⁻¹) with hr'def
  have hr' : 0 < r' := Real.rpow_pos_of_pos hr _
  have hr'd : r' ^ d = r := Real.rpow_inv_natCast_pow hr.le (by omega)
  have hr'ρ : r' < ρ' := by
    by_contra hle
    have h := pow_le_pow_left₀ hρ'.le (not_lt.mp hle) d
    rw [hr'd] at h
    linarith
  have hr'1 : r' < r₁ := hr'ρ.trans_le (min_le_left _ _)
  have hr'b : r' < ρb := hr'ρ.trans_le (min_le_right _ _)
  set z := smoothRootParameter d r' with hzdef
  have hzspec : ∀ k θ, z k θ ∈ Ψ.target ∧ Ψ.symm (z k θ) ∈ N ∧
      G (Ψ.symm (z k θ)) ∈ ball x ε := fun k θ => hr₁spec (by
    rw [dist_zero_right, hzdef, norm_smoothRootParameter d hr'.le]
    exact hr'1)
  have hcirc : ∀ k θ, circlePath r θ = z k θ ^ d := fun k θ => by
    rw [hzdef, smoothRootParameter_pow hd0.ne', hr'd]
    rfl
  /- Step 7: the roots from the ball are the `d` points `Y (z k θ)`. -/
  have hroots : ∀ θ : ℝ, P.localRoots x ε (c + circlePath r θ) =
      range fun k => Ψ.symm (z k θ) := by
    intro θ
    ext ζ'
    constructor
    · rintro ⟨y, ⟨hyF, hyb⟩, rfl⟩
      obtain ⟨⟨hys, -⟩, -, hyN⟩ := hεM hyb
      obtain ⟨-, hφN, hΨs⟩ := hyN
      have hFy : F y = (s, P.fibreCoord (A.H y)) := Prod.ext hyF.2.1 rfl
      have hGy : G (P.fibreCoord (A.H y)) = y := by
        change Φ.symm (s, P.fibreCoord (A.H y)) = y
        rw [← hFy, ← hΦF]
        exact Φ.left_inv hys
      have hφy : φ (P.fibreCoord (A.H y)) = c + circlePath r θ := by
        change P.baseCoord (A.H (G (P.fibreCoord (A.H y)))) = c + circlePath r θ
        rw [hGy]
        exact hyF.2.2
      rw [hφN] at hφy
      have hqd : q (P.fibreCoord (A.H y)) ^ d =
          ((r' ^ d : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
        rw [hr'd]
        exact add_left_cancel hφy
      obtain ⟨k, hk⟩ := exists_eq_smoothRootParameter hd0 hr' hqd
      refine ⟨k, ?_⟩
      change Ψ.symm (z k θ) = P.fibreCoord (A.H y)
      rw [hzdef, ← hk, ← hΨq]
      exact Ψ.left_inv hΨs
    · rintro ⟨k, rfl⟩
      obtain ⟨hzt, hYN, hGb⟩ := hzspec k θ
      obtain ⟨hYt, hφN, -⟩ := hYN
      obtain ⟨hlev, hζ⟩ := hFG _ hYt
      have hqY : q (Ψ.symm (z k θ)) = z k θ := by
        rw [← hΨq]
        exact Ψ.right_inv hzt
      refine ⟨G (Ψ.symm (z k θ)), ⟨⟨(hεM hGb).1.2, hlev, ?_⟩, hGb⟩, hζ⟩
      change φ (Ψ.symm (z k θ)) = c + circlePath r θ
      rw [hφN, hqY, hcirc k θ]
  have hinj : ∀ θ : ℝ, Injective fun k => Ψ.symm (z k θ) := by
    intro θ k l hkl
    apply smoothRootParameter_injective hd0 hr' θ
    have h1 := Ψ.right_inv (hzspec k θ).1
    have h2 := Ψ.right_inv (hzspec l θ).1
    change Ψ.symm (z k θ) = Ψ.symm (z l θ) at hkl
    change z k θ = z l θ
    rw [← h1, ← h2, hkl]
  /- Step 8: the three properties of the cluster. -/
  refine ⟨fun θ => ?_, fun θ y hy => (hεM hy.2).2.1, fun b K hK W hW => ?_⟩
  · rw [hroots θ, Set.ncard_range_of_injective (hinj θ), Nat.card_eq_fintype_card,
      Fintype.card_fin]
  · obtain ⟨hEcl, hErep⟩ := hbraid r' hr' hr'b b
    have hE : IsRootLabellingOn (P.localRoots x ε) (fun θ => c + circlePath r θ)
        (Icc b (b + 2 * π)) (fun k θ => Ψ.symm (z k θ)) :=
      ⟨fun k => hEcl.continuousOn k, fun θ _ => hinj θ, fun θ _ => (hroots θ).symm⟩
    obtain ⟨σ, hσ⟩ := hE.exists_perm isPreconnected_Icc hK
    exact (isRepresented_congr (isRepresented_relabel hErep σ) hσ).signedBraidConj hW

/-- **The cluster data at a smooth critical point**: `d ≥ 2` strands, the Coxeter word, and no
singular point. -/
theorem pointClusterData_of_smoothCritical (hP : P.SetupProperties) {c : ℂ} {x : Source 2}
    (hc : c ∈ P.critical) (hx : x ∈ P.levelFibre c)
    (hcrit : ¬ Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x))
    (hpt : ∀ j, x ≠ L.point j) : Nonempty (P.PointClusterData c x) := by
  obtain ⟨d, hd2, hcl⟩ := P.exists_localClusterAt_coxeter_of_smoothCritical hP hc hx hcrit hpt
  exact ⟨{ degree := d
           word := coxeterWord d
           kind := none
           holds := hcl
           kind_singular := fun j hj => by simp at hj
           kind_none := fun _ => rfl
           point_kind := fun j hj => absurd hj (hpt j)
           critical := fun _ => Or.inr hd2 }⟩

end LevelProjectionSetup

/-- **The pointwise cluster statement from the singular case.** The regular points are treated in
`LevelRootRegularCluster.lean` and the smooth critical points in this module. The remaining
hypothesis is the cluster data at the singular points. -/
theorem pointClusterStatement_of_singular
    (hSingular : ∀ {g : PointedMapGerm 2 3} {hd : g.differential = 0}
      {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}
      {L : ResolutionSectionLevel A} (P : LevelProjectionSetup A L), P.SetupProperties →
      ∀ j : Fin L.points.card,
        Nonempty (P.PointClusterData (P.baseCoord (A.H (L.point j))) (L.point j))) :
    PointClusterStatement :=
  pointClusterStatement_of_cases (fun P hP => P.pointClusterData_of_smoothCritical hP) hSingular

end OnLeConjecture.Analytic
