/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionTargetCollarHomology
public import OnLeConjecture.Analytic.PlaneMilnorBoundaryOrientation

/-! # Oriented local charts for the literal target boundary

The inward coordinate is the decrease of the target radius function.
The construction reuses the holomorphic level parametrization and the
proved oriented real inverse theorem. Its ambient source domain remains
an explicit open set.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff ComplexConjugate

namespace OnLeConjecture.Analytic

/-- A local oriented chart for a complex level cut by a real radius.
Its imaginary coordinate is exactly the inward change of radius. -/
structure SectionRadiusBoundaryChart (f : CollarPlane → ℂ) (ρ : CollarPlane → ℝ)
    (O : Set CollarPlane) (z : CollarPlane) where
  W : Set ℂ
  isOpen_W : IsOpen W
  zero_mem : (0 : ℂ) ∈ W
  φ : ℂ → CollarPlane
  χ : CollarPlane → ℂ
  φ_zero : φ 0 = z
  smooth : ContDiffOn ℝ ω φ W
  inverse_smooth : ContDiffOn ℝ ω χ O
  mapsTo : MapsTo φ W O
  left_inverse : ∀ t ∈ W, χ (φ t) = t
  level_eq : ∀ t ∈ W, f (φ t) = f z
  radius_eq : ∀ t ∈ W, ρ (φ t) = ρ z - t.im
  inverse_im : ∀ w, (χ w).im = ρ z - ρ w
  local_inverse : ∀ᶠ w in 𝓝 z, f w = f z → χ w ∈ W ∧ φ (χ w) = w
  oriented : ∀ t ∈ W, ∃ c : ℂ, 0 < c.im ∧
    fderiv ℝ φ t Complex.I = c • fderiv ℝ φ t 1

/-- Joint submersivity constructs an oriented chart for an arbitrary real
analytic radius, inside the prescribed open source neighborhood. -/
theorem nonempty_sectionRadiusBoundaryChart (f : CollarPlane → ℂ) (ρ : CollarPlane → ℝ)
    (O : Set CollarPlane) (hO : IsOpen O) {z : CollarPlane} (hzO : z ∈ O)
    (han : AnalyticAt ℂ f z) (hρa : ∀ w ∈ O, ContDiffAt ℝ ω ρ w)
    (hrad : Surjective (fderiv ℝ (fun w => (f w, ρ w)) z)) :
    Nonempty (SectionRadiusBoundaryChart f ρ O z) := by
  have hNd : ∀ w ∈ O, DifferentiableAt ℝ ρ w := fun w hw =>
    (hρa w hw).differentiableAt (by simp)
  have hradd : fderiv ℝ (fun w => (f w, ρ w)) z =
      (fderiv ℝ f z).prod (fderiv ℝ ρ z) :=
    ((han.differentiableAt.restrictScalars ℝ).hasFDerivAt.prodMk (hNd z hzO).hasFDerivAt).fderiv
  have hsurj : Surjective (fderiv ℝ f z) := by
    intro c
    obtain ⟨v, hv⟩ := hrad (c, 0)
    rw [hradd] at hv
    exact ⟨v, congrArg Prod.fst hv⟩
  obtain ⟨ℓ, ψ, U₀, N₀, hU₀, h0U₀, hN₀, hzN₀, hψ0, hψan₀, hψF₀, hψℓ₀, hloc₀, hker⟩ :=
    exists_levelParametrization f han (fderiv_ne_zero_of_real_surjective han.differentiableAt hsurj)
  let U := U₀ ∩ ψ ⁻¹' O
  have hU : IsOpen U := ContinuousOn.isOpen_inter_preimage
    (fun u hu => (hψan₀ u hu).continuousAt.continuousWithinAt) hU₀ hO
  have h0U : (0 : ℂ) ∈ U := ⟨h0U₀, by change ψ 0 ∈ O; rw [hψ0]; exact hzO⟩
  have hψan : ∀ u ∈ U, AnalyticAt ℂ ψ u := fun u hu => hψan₀ u hu.1
  have hψF : ∀ u ∈ U, f (ψ u) = f z := fun u hu => hψF₀ u hu.1
  have hψℓ : ∀ u ∈ U, ℓ (ψ u - z) = u := fun u hu => hψℓ₀ u hu.1
  let N := N₀ ∩ O
  have hzN : z ∈ N := ⟨hzN₀, hzO⟩
  have hN : IsOpen N := hN₀.inter hO
  have hloc : ∀ w ∈ N, f w = f z → ℓ (w - z) ∈ U ∧ ψ (ℓ (w - z)) = w := by
    intro w hw hfw
    obtain ⟨hu, he⟩ := hloc₀ w hw.1 hfw
    exact ⟨⟨hu, by change ψ (ℓ (w - z)) ∈ O; rw [he]; exact hw.2⟩, he⟩
  let k := deriv ψ 0
  let r : ℂ → ℝ := fun u => ρ (ψ u)
  have hψR : ∀ u ∈ U, ContDiffAt ℝ ω ψ u := fun u hu =>
    ((hψan u hu).restrictScalars (𝕜 := ℝ)).contDiffAt
  let β : ℂ →L[ℝ] ℝ := (fderiv ℝ ρ z).comp (fderiv ℝ ψ 0)
  have hρd : HasFDerivAt r β 0 := by
    have h1 : HasFDerivAt ρ (fderiv ℝ ρ z) (ψ 0) := by
      rw [hψ0]
      exact (hNd z hzO).hasFDerivAt
    exact h1.comp 0 ((hψan 0 h0U).differentiableAt.restrictScalars ℝ).hasFDerivAt
  have hβ : ∀ v, β v = fderiv ℝ ρ z (v • k) := by
    intro v
    simp only [β, ContinuousLinearMap.coe_comp, comp_apply]
    rw [fderiv_real_apply_eq_smul_deriv (hψan 0 h0U).differentiableAt]
  obtain ⟨h, hh⟩ := hrad (0, 1)
  rw [hradd] at hh
  have hh1 : fderiv ℝ f z h = 0 := congrArg Prod.fst hh
  have hh2 : fderiv ℝ ρ z h = 1 := congrArg Prod.snd hh
  have hhk : h = ℓ h • k := by
    apply hker
    rw [han.differentiableAt.fderiv_restrictScalars ℝ] at hh1
    exact hh1
  have hβ1 : β (ℓ h) = 1 := by rw [hβ, ← hhk, hh2]
  let μ : ℂ := -(β Complex.I : ℂ) - (β 1 : ℂ) * Complex.I
  have hμ : μ ≠ 0 := by
    intro h0
    have hre : β Complex.I = 0 := by
      have := congrArg Complex.re h0
      simpa [μ] using this
    have him : β 1 = 0 := by
      have := congrArg Complex.im h0
      simpa [μ] using this
    have := realLinearForm_apply_eq β (ℓ h)
    rw [hβ1, hre, him] at this
    simp at this
  let T : ℂ → ℂ := fun u => ((μ * u).re : ℂ) + (ρ z - r u) • Complex.I
  have hT0 : T 0 = 0 := by simp [T, r, hψ0]
  let A : ℂ →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp (Complex.reCLM.comp (mulRealEquiv μ hμ : ℂ →L[ℝ] ℂ))
  have hTd : HasFDerivAt T ((mulRealEquiv μ hμ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) 0 := by
    have h2 : HasFDerivAt T (A + (0 - β).smulRight Complex.I) 0 :=
      A.hasFDerivAt.add (((hasFDerivAt_const (𝕜 := ℝ) (ρ z) (0 : ℂ)).sub hρd).smul_const
        Complex.I)
    refine h2.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    apply Complex.ext
    · simp [A]
    · have hAv : (A v).im = 0 := by simp [A]
      have h3 : ((A + (0 - β).smulRight Complex.I) v).im = -β v := by simp [hAv]
      rw [h3, realLinearForm_apply_eq β v]
      simp [μ]
      ring
  have hTc : ∀ u ∈ U, ContDiffAt ℝ ω T u := by
    intro u hu
    have hrc : ContDiffAt ℝ ω r u := (hρa (ψ u) hu.2).comp u (hψR u hu)
    exact A.contDiff.contDiffAt.add ((contDiffAt_const.sub hrc).smul contDiffAt_const)
  obtain ⟨G, hG, h0G, hGs, hq⟩ := exists_orientedLocalInverse hμ
    (by filter_upwards [hU.mem_nhds h0U] with u hu using hTc u hu) hT0 hTd
  obtain ⟨P, hPq, hP, h0P⟩ := _root_.eventually_nhds_iff.mp hq
  have hG0 : G 0 = 0 := by rw [hG, hT0]
  have h0T : (0 : ℂ) ∈ G.target := hG0 ▸ G.map_source h0G
  have hGs0 : G.symm 0 = 0 := by
    have h := G.left_inv h0G
    rwa [hG0] at h
  let W := G.target ∩ G.symm ⁻¹' U ∩ P
  have hW : IsOpen W := (G.isOpen_inter_preimage_symm hU).inter hP
  have h0W : (0 : ℂ) ∈ W := ⟨⟨h0T, by rw [mem_preimage, hGs0]; exact h0U⟩, h0P⟩
  let φ : ℂ → CollarPlane := fun t => ψ (G.symm t)
  let χ : CollarPlane → ℂ :=
    fun w => ((μ * ℓ (w - z)).re : ℂ) + (ρ z - ρ w) • Complex.I
  have hχT : ∀ u ∈ U, χ (ψ u) = T u := by
    intro u hu
    simp only [χ, T, r, hψℓ u hu]
  have hχim : ∀ w, (χ w).im = ρ z - ρ w := by
    intro w
    simp only [χ, Complex.add_im, Complex.ofReal_im, Complex.smul_im, Complex.I_im,
      smul_eq_mul, mul_one, zero_add]
  have hleft : ∀ t ∈ W, χ (φ t) = t := by
    intro t ht
    change χ (ψ (G.symm t)) = t
    rw [hχT _ ht.1.2, ← hG]
    exact G.right_inv ht.1.1
  have hχs : ContDiffOn ℝ ω χ O := by
    intro w hw
    have hA : ContDiffAt ℝ ω
        (fun w : CollarPlane => ((μ * ℓ (w - z)).re : ℂ)) w :=
      (A.comp (ℓ.restrictScalars ℝ)).contDiff.contDiffAt.comp w
        (contDiffAt_id.sub contDiffAt_const)
    exact (hA.add ((contDiffAt_const.sub (hρa w hw)).smul
      (contDiffAt_const (c := Complex.I)))).contDiffWithinAt
  have hsmooth : ContDiffOn ℝ ω φ W := fun t ht =>
    ((hψR _ ht.1.2).comp t (hGs t ht.1.1)).contDiffWithinAt
  have horient : ∀ t ∈ W,
      ∃ c : ℂ, 0 < c.im ∧ fderiv ℝ φ t Complex.I = c • fderiv ℝ φ t 1 := by
    intro t ht
    have hgd : DifferentiableAt ℝ G.symm t := (hGs t ht.1.1).differentiableAt (by simp)
    have hψd : DifferentiableAt ℂ ψ (G.symm t) := (hψan _ ht.1.2).differentiableAt
    have hφd : fderiv ℝ φ t = (fderiv ℝ ψ (G.symm t)).comp (fderiv ℝ G.symm t) :=
      fderiv_fun_comp t (hψd.restrictScalars ℝ) hgd
    have hab := hPq t ht.2
    refine ⟨fderiv ℝ G.symm t Complex.I / fderiv ℝ G.symm t 1,
      im_div_pos_of_im_mul_conj_pos hab, ?_⟩
    have hb : fderiv ℝ G.symm t 1 ≠ 0 := by
      intro hb0
      rw [hb0] at hab
      simp at hab
    rw [hφd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      fderiv_real_apply_eq_smul_deriv hψd, fderiv_real_apply_eq_smul_deriv hψd,
      smul_smul, div_mul_cancel₀ _ hb]
  refine ⟨⟨W, hW, h0W, φ, χ, by simp [φ, hGs0, hψ0], hsmooth, hχs,
    (fun _ ht => ht.1.2.2), hleft, (fun t ht => hψF _ ht.1.2), ?_, hχim, ?_, horient⟩⟩
  · intro t ht
    have h := hχim (φ t)
    rw [hleft t ht] at h
    linarith
  · have hχz : χ z = 0 := by simp [χ]
    have hχc : ContinuousAt χ z := (hχs.contDiffAt (hO.mem_nhds hzO)).continuousAt
    have hχnear : ∀ᶠ w in 𝓝 z, χ w ∈ W := by
      exact hχc.preimage_mem_nhds (hW.mem_nhds (by rw [hχz]; exact h0W))
    have hℓnear : ∀ᶠ w in 𝓝 z, ℓ (w - z) ∈ G.source := by
      have hc : ContinuousAt (fun w => ℓ (w - z)) z := by fun_prop
      exact hc.preimage_mem_nhds (G.open_source.mem_nhds
        (by simpa only [sub_self, map_zero] using h0G))
    filter_upwards [hN.mem_nhds hzN, hχnear, hℓnear] with w hw hwW hwG hfw
    obtain ⟨hu, hψu⟩ := hloc w hw hfw
    have hχw : χ w = G (ℓ (w - z)) := by
      conv_lhs => rw [← hψu]
      rw [hχT _ hu, hG]
    have hgχ : G.symm (χ w) = ℓ (w - z) := by rw [hχw, G.left_inv hwG]
    exact ⟨hwW, by change ψ (G.symm (χ w)) = w; rw [hgχ, hψu]⟩

namespace SectionRadiusBoundaryChart

variable {f : CollarPlane → ℂ} {ρ : CollarPlane → ℝ} {O : Set CollarPlane} {z : CollarPlane}

/-- The upper half-plane part of the chart parametrizes the cut. -/
def model (C : SectionRadiusBoundaryChart f ρ O z) : Set ℂ :=
  C.W ∩ {t | 0 ≤ t.im}

theorem mapsTo_model (C : SectionRadiusBoundaryChart f ρ O z) :
    MapsTo C.φ C.model {w | w ∈ O ∧ f w = f z ∧ ρ w ≤ ρ z} := by
  intro t ht
  exact ⟨C.mapsTo ht.1, C.level_eq t ht.1, by rw [C.radius_eq t ht.1]; exact sub_le_self _ ht.2⟩

theorem immersion (C : SectionRadiusBoundaryChart f ρ O z) (hO : IsOpen O)
    {t : ℂ} (ht : t ∈ C.W) : Injective (fderiv ℝ C.φ t) := by
  apply injective_fderiv_of_leftInverse
    ((C.smooth.contDiffAt (C.isOpen_W.mem_nhds ht)).differentiableAt (by simp))
    ((C.inverse_smooth.contDiffAt (hO.mem_nhds (C.mapsTo ht))).differentiableAt (by simp))
  filter_upwards [C.isOpen_W.mem_nhds ht] with u hu using C.left_inverse u hu

theorem injOn (C : SectionRadiusBoundaryChart f ρ O z) : InjOn C.φ C.W := by
  intro t ht u hu htu
  rw [← C.left_inverse t ht, ← C.left_inverse u hu, htu]

/-- The model maps homeomorphically onto its image. -/
def homeomorph (C : SectionRadiusBoundaryChart f ρ O z) : C.model ≃ₜ C.φ '' C.model where
  toFun t := ⟨C.φ t, mem_image_of_mem _ t.property⟩
  invFun w := ⟨C.χ w, by
    obtain ⟨t, ht, he⟩ := w.property
    rw [← he, C.left_inverse t ht.1]
    exact ht⟩
  left_inv t := Subtype.ext (C.left_inverse t t.property.1)
  right_inv w := by
    apply Subtype.ext
    obtain ⟨t, ht, he⟩ := w.property
    change C.φ (C.χ w) = w
    rw [← he, C.left_inverse t ht.1]
  continuous_toFun :=
    (C.smooth.continuousOn.mono inter_subset_left).domRestrict.subtype_mk _
  continuous_invFun := by
    refine (C.inverse_smooth.continuousOn.comp_continuous continuous_subtype_val ?_).subtype_mk _
    intro w
    obtain ⟨t, ht, he⟩ := w.property
    exact he ▸ C.mapsTo ht.1

/-- The image is a neighborhood in the literal level sublevel set. -/
theorem image_model_mem_nhdsWithin (C : SectionRadiusBoundaryChart f ρ O z) :
    C.φ '' C.model ∈ 𝓝[{w | w ∈ O ∧ f w = f z ∧ ρ w ≤ ρ z}] z := by
  filter_upwards [C.local_inverse.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with w hw hwcut
  obtain ⟨hwW, he⟩ := hw hwcut.2.1
  refine ⟨C.χ w, ⟨hwW, ?_⟩, he⟩
  change 0 ≤ (C.χ w).im
  rw [C.inverse_im]
  exact sub_nonneg.mpr hwcut.2.2

/-- The real axis of the chart is exactly the radius boundary. -/
theorem boundary_iff (C : SectionRadiusBoundaryChart f ρ O z) {t : ℂ} (ht : t ∈ C.W) :
    ρ (C.φ t) = ρ z ↔ t.im = 0 := by
  rw [C.radius_eq t ht]
  exact sub_eq_self

/-- The real-coordinate tangent stays on the level and the radius boundary,
while the imaginary-coordinate tangent decreases radius at unit speed. -/
theorem tangent_properties (C : SectionRadiusBoundaryChart f ρ O z)
    (hf : DifferentiableAt ℂ f z) (hρ : DifferentiableAt ℝ ρ z) :
    (∀ v : ℂ, fderiv ℂ f z (fderiv ℝ C.φ 0 v) = 0) ∧
      fderiv ℝ ρ z (fderiv ℝ C.φ 0 1) = 0 ∧
      fderiv ℝ ρ z (fderiv ℝ C.φ 0 Complex.I) = -1 := by
  have hφ : HasFDerivAt C.φ (fderiv ℝ C.φ 0) 0 :=
    ((C.smooth.contDiffAt (C.isOpen_W.mem_nhds C.zero_mem)).differentiableAt (by simp)).hasFDerivAt
  have hfd : HasFDerivAt (fun t => f (C.φ t))
      (((fderiv ℂ f z).restrictScalars ℝ).comp (fderiv ℝ C.φ 0)) 0 := by
    have h := hf.hasFDerivAt.restrictScalars ℝ
    have h' : HasFDerivAt f ((fderiv ℂ f z).restrictScalars ℝ) (C.φ 0) := C.φ_zero.symm ▸ h
    exact h'.comp 0 hφ
  have hfc : HasFDerivAt (fun t => f (C.φ t)) (0 : ℂ →L[ℝ] ℂ) 0 := by
    apply (hasFDerivAt_const (𝕜 := ℝ) (f z) (0 : ℂ)).congr_of_eventuallyEq
    filter_upwards [C.isOpen_W.mem_nhds C.zero_mem] with t ht using C.level_eq t ht
  have hrd : HasFDerivAt (fun t => ρ (C.φ t))
      ((fderiv ℝ ρ z).comp (fderiv ℝ C.φ 0)) 0 := by
    have h' : HasFDerivAt ρ (fderiv ℝ ρ z) (C.φ 0) := C.φ_zero.symm ▸ hρ.hasFDerivAt
    exact h'.comp 0 hφ
  have hrc : HasFDerivAt (fun t => ρ (C.φ t)) (-Complex.imCLM) 0 := by
    have h := (hasFDerivAt_const (𝕜 := ℝ) (ρ z) (0 : ℂ)).sub Complex.imCLM.hasFDerivAt
    simp only [zero_sub] at h
    apply h.congr_of_eventuallyEq
    filter_upwards [C.isOpen_W.mem_nhds C.zero_mem] with t ht using C.radius_eq t ht
  refine ⟨fun v => DFunLike.congr_fun (hfd.unique hfc) v, ?_, ?_⟩
  · simpa only [ContinuousLinearMap.comp_apply, neg_apply,
      Complex.imCLM_apply, Complex.one_im, neg_zero] using DFunLike.congr_fun (hrd.unique hrc) 1
  · simpa only [ContinuousLinearMap.comp_apply, neg_apply,
      Complex.imCLM_apply, Complex.I_im] using DFunLike.congr_fun (hrd.unique hrc) Complex.I

end SectionRadiusBoundaryChart

end OnLeConjecture.Analytic
