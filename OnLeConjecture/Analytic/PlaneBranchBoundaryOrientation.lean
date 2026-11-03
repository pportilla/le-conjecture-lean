/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidLinkIsotopy
public import OnLeConjecture.Analytic.PlaneMilnorBoundaryOrientation

/-!
# Angular orientation of the analytic branch sphere parametrization

The positive Circle parameter is explicitly `Circle.exp theta`. At a sphere
level the actual radial parameter is `rho(theta) * exp(i theta)`. Radial
monotonicity and the constant norm of its image imply a positive imaginary
Hermitian pairing of position with angular velocity.
-/

@[expose] public noncomputable section

open Filter Set Metric Manifold
open scoped Topology ContDiff Manifold ComplexConjugate

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

/-- Angular differentiation of a variable positive radius in the standard
positive parametrization `Circle.exp`. -/
theorem hasDerivAt_radial_circleExp {ρ : ℝ → ℝ} {θ : ℝ}
    (hρ : DifferentiableAt ℝ ρ θ) (hρ0 : ρ θ ≠ 0) :
    HasDerivAt (fun t : ℝ => ρ t • (Circle.exp t : ℂ))
      ((((deriv ρ θ / ρ θ : ℝ) : ℂ) + Complex.I) *
        (ρ θ • (Circle.exp θ : ℂ))) θ := by
  have he : HasDerivAt (fun t : ℝ => (Circle.exp t : ℂ))
      (Complex.I * (Circle.exp θ : ℂ)) θ := by
    have h := ((Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I).cexp
    apply h.congr_deriv
    simp only [Circle.coe_exp, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul]
    ring
  apply (hρ.hasDerivAt.smul he).congr_deriv
  simp only [Complex.real_smul, Complex.ofReal_div]
  have hr : (ρ θ : ℂ) ≠ 0 := by exact_mod_cast hρ0
  field_simp
  ring

/-- A holomorphic curve with positive radial squared-norm derivative has
positive angular tangent on a smoothly parametrized sphere level. -/
theorem radial_curve_sphere_tangent_im_pos
    {F : ℂ → EuclideanSpace ℂ (Fin 2)} {ρ : ℝ → ℝ} {θ : ℝ}
    (hρ : DifferentiableAt ℝ ρ θ) (hρpos : 0 < ρ θ)
    (hF : DifferentiableAt ℂ F (ρ θ • (Circle.exp θ : ℂ)))
    (hpos : 0 < fderiv ℝ (fun z => ‖F z‖ ^ 2)
      (ρ θ • (Circle.exp θ : ℂ)) (ρ θ • (Circle.exp θ : ℂ)))
    (hlevel : ∀ᶠ t in 𝓝 θ,
      ‖F (ρ t • (Circle.exp t : ℂ))‖ ^ 2 = ‖F (ρ θ • (Circle.exp θ : ℂ))‖ ^ 2) :
    0 < (inner ℂ (F (ρ θ • (Circle.exp θ : ℂ)))
      (deriv (fun t : ℝ => F (ρ t • (Circle.exp t : ℂ))) θ)).im := by
  let z : ℂ := ρ θ • (Circle.exp θ : ℂ)
  let q : ℝ := deriv ρ θ / ρ θ
  let A : ℂ := inner ℂ (F z) (z • deriv F z)
  have hγ : HasDerivAt (fun t : ℝ => F (ρ t • (Circle.exp t : ℂ)))
      (((q : ℂ) + Complex.I) • (z • deriv F z)) θ := by
    simpa only [Function.comp_def, smul_smul, z, q] using
      hF.hasDerivAt.scomp θ (hasDerivAt_radial_circleExp hρ hρpos.ne')
  have hA : 0 < A.re := by
    have hn := (hF.restrictScalars ℝ).hasFDerivAt.norm_sq
    rw [hn.fderiv] at hpos
    simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      nsmul_eq_mul, Nat.cast_ofNat] at hpos
    rw [fderiv_real_apply_eq_smul_deriv hF, real_inner_euclidean] at hpos
    change 0 < 2 * A.re at hpos
    linarith
  have hconst : HasDerivAt (fun t : ℝ => ‖F (ρ t • (Circle.exp t : ℂ))‖ ^ 2) 0 θ :=
    (hasDerivAt_const θ (‖F z‖ ^ 2)).congr_of_eventuallyEq hlevel
  have hzero := hγ.norm_sq.unique hconst
  rw [real_inner_euclidean, inner_smul_right] at hzero
  change 2 * (((q : ℂ) + Complex.I) * A).re = 0 at hzero
  have hrel : A.im = q * A.re := by
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.I_re,
      add_zero, Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add, one_mul] at hzero
    linarith
  rw [hγ.deriv, inner_smul_right]
  change 0 < (((q : ℂ) + Complex.I) * A).im
  rw [Complex.mul_im]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero,
    Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add, one_mul]
  rw [hrel]
  have heq : q * (q * A.re) + A.re = (q ^ 2 + 1) * A.re := by ring
  rw [heq]
  exact mul_pos (by positivity) hA

section MixedLevel

variable {F : ℂ → EuclideanSpace ℂ (Fin 2)} {i : Fin 2} {R c : ℝ}
    (hlevels : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : Circle,
      ∃! r : ℝ, r ∈ Ioo 0 R ∧ planeMixedRadiusSq i t (F (r • (u : ℂ))) = c)

/-- The actual unscaled sphere endpoint, with its chosen variable radius,
has positive angular tangent. -/
theorem planeMixedLevelParameter_at_one_tangent_im_pos
    (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball 0 R, z ≠ 0 →
      0 < fderiv ℝ (fun w => planeMixedRadiusSq i t (F w)) z z)
    (θ : ℝ) :
    0 < (inner ℂ (F (planeMixedLevelParameter hlevels (Circle.exp θ, 1)))
      (deriv (fun t : ℝ => F (planeMixedLevelParameter hlevels (Circle.exp t, 1))) θ)).im := by
  let ρ : ℝ → ℝ := fun t => planeMixedLevelRadius hlevels (Circle.exp t, 1)
  have hρs : ContDiff ℝ ∞ ρ := by
    have h := planeMixedLevelRadius_reparam_contMDiff hlevels hF hpos
      (σ := fun _ => (1 : ℝ)) contDiff_const (fun _ => ⟨zero_le_one, le_rfl⟩)
    have harg : ContMDiff 𝓘(ℝ) ((𝓡 1).prod 𝓘(ℝ)) ∞
        (fun t : ℝ => (Circle.exp t, (0 : ℝ))) :=
      contMDiff_circleExp.prodMk contMDiff_const
    exact (h.comp harg).contDiff
  have hr := (planeMixedLevelRadius_spec hlevels (Circle.exp θ, 1)
    ⟨zero_le_one, le_rfl⟩).1
  have hball := planeMixedLevelParameter_mem_ball hlevels (Circle.exp θ, 1)
    ⟨zero_le_one, le_rfl⟩
  have hn : planeMixedLevelParameter hlevels (Circle.exp θ, 1) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [planeMixedLevelParameter_norm hlevels _ ⟨zero_le_one, le_rfl⟩]
    exact hr.1.ne'
  have hp := hpos 1 ⟨zero_le_one, le_rfl⟩ _ hball hn
  simp only [planeMixedRadiusSq, sub_self, zero_mul, one_mul, zero_add] at hp
  apply radial_curve_sphere_tangent_im_pos (hρs.differentiable (by simp) θ) hr.1
    (hF _ hball).differentiableAt hp
  apply Filter.Eventually.of_forall
  intro t
  change ‖F (planeMixedLevelParameter hlevels (Circle.exp t, 1))‖ ^ 2 =
    ‖F (planeMixedLevelParameter hlevels (Circle.exp θ, 1))‖ ^ 2
  rw [planeMixedLevelParameter_at_one_norm, planeMixedLevelParameter_at_one_norm]

/-- Constant positive normalization of the actual sphere endpoint preserves
its positive angular tangent. No endpoint parametrization is replaced. -/
theorem planeMixedLevelFamily_at_one_tangent_im_pos
    (hc : 0 < c) (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball 0 R, z ≠ 0 →
      0 < fderiv ℝ (fun w => planeMixedRadiusSq i t (F w)) z z)
    {σ : ℝ → ℝ} {t₀ : ℝ} (ht : σ t₀ = 1) (θ : ℝ) :
    0 < (inner ℂ (planeMixedLevelFamily hlevels σ (Circle.exp θ, t₀))
      (deriv (fun t : ℝ => planeMixedLevelFamily hlevels σ (Circle.exp t, t₀)) θ)).im := by
  have heq : (fun t : ℝ => planeMixedLevelFamily hlevels σ (Circle.exp t, t₀)) =
      (fun t : ℝ => (Real.sqrt c)⁻¹ • F (planeMixedLevelParameter hlevels (Circle.exp t, 1))) :=
    funext fun t => planeMixedLevelFamily_at_one hlevels ht (Circle.exp t)
  rw [heq, planeMixedLevelFamily_at_one hlevels ht, deriv_fun_const_smul_field,
    inner_smul_left_eq_smul, inner_smul_right_eq_smul]
  simp only [Complex.smul_im, smul_eq_mul]
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hc))
    (mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hc))
      (planeMixedLevelParameter_at_one_tangent_im_pos hlevels hF hpos θ))

end MixedLevel

/-- The analytic branch construction supplies the radial positivity and a mixed-level
family whose actual sphere endpoint has positive angular tangent. -/
theorem exists_plane_branch_mixed_level_families_with_orientation
    {F : ℂ → EuclideanSpace ℂ (Fin 2)} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (i : Fin 2) (a : ℕ) (ha : 0 < a)
    (hpower : ∀ᶠ z in 𝓝 (0 : ℂ), F z i = z ^ a)
    {S : Set ℂ} (hS : S ∈ 𝓝 0) (hinj : InjOn F S)
    {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (hσmem : ∀ t, σ t ∈ Icc (0 : ℝ) 1) :
    ∃ R : ℝ, 0 < R ∧ closedBall (0 : ℂ) R ⊆ S ∧
      ∀ c : ℝ, 0 < c → c < R ^ (2 * a) →
      ∃ hlevels : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : Circle,
          ∃! r : ℝ, r ∈ Ioo 0 R ∧ planeMixedRadiusSq i t (F (r • (u : ℂ))) = c,
        ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
          (planeMixedLevelFamily hlevels σ) ∧
        (∀ p, ‖planeMixedLevelFamily hlevels σ p‖ = 1) ∧
        (∀ t, Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞
          (fun u : Circle => planeMixedLevelFamily hlevels σ (u, t))) ∧
        (∀ p, ‖planeMixedLevelFamily hlevels σ p i‖⁻¹ • planeMixedLevelFamily hlevels σ p i =
          (p.1 : ℂ) ^ a) ∧
        (∀ t, σ t = 0 → ∀ u : Circle,
          planeMixedLevelFamily hlevels σ (u, t) =
            planeRadialNormalization (F ((c ^ ((2 * a : ℕ) : ℝ)⁻¹) • (u : ℂ)))) ∧
        (∀ t, σ t = 1 → ∀ θ : ℝ,
          0 < (inner ℂ (planeMixedLevelFamily hlevels σ (Circle.exp θ, t))
            (deriv (fun x : ℝ => planeMixedLevelFamily hlevels σ (Circle.exp x, t)) θ)).im) ∧
        ∀ t, σ t = 1 →
          Set.range (fun u : Circle => planeMixedLevelFamily hlevels σ (u, t)) =
            (fun y : EuclideanSpace ℂ (Fin 2) => (Real.sqrt c)⁻¹ • y) ''
              (sphere 0 (Real.sqrt c) ∩ F '' ball 0 R) := by
  obtain ⟨R, hR, hRS, hAF, hp, hreg, hlevels⟩ :=
    exists_plane_mixed_radial_levels hF hF0 i a ha hpower hS
  refine ⟨R, hR, hRS, ?_⟩
  intro c hc hcR
  let hl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : Circle,
      ∃! r : ℝ, r ∈ Ioo 0 R ∧ planeMixedRadiusSq i t (F (r • (u : ℂ))) = c :=
    fun t ht u => hlevels t ht u u.norm_coe c hc hcR
  have hFb : AnalyticOnNhd ℂ F (ball 0 R) := hAF.mono ball_subset_closedBall
  have hip : InjOn F (ball 0 R) := hinj.mono (ball_subset_closedBall.trans hRS)
  have hpb : ∀ z ∈ ball 0 R, F z i = z ^ a := fun z hz => hp z (ball_subset_closedBall hz)
  have hpos := fun t ht => (hreg t ht).2.2
  refine ⟨hl,
    planeMixedLevelFamily_contMDiff hl hc.ne' hFb hpos hσ hσmem,
    planeMixedLevelFamily_norm hl hc.ne' hσmem,
    planeMixedLevelFamily_slice_isSmoothEmbedding hl hc.ne' hFb hip hpos ha hpb hσ hσmem,
    planeMixedLevelFamily_phase hl hc.ne' hpb hσmem, ?_, ?_, ?_⟩
  · intro t ht u
    exact planeMixedLevelFamily_at_zero hl ha hpb ht u
  · intro t ht θ
    exact planeMixedLevelFamily_at_one_tangent_im_pos hl hc hFb hpos ht θ
  · intro t ht
    exact planeMixedLevelFamily_at_one_range hl hc hF0 ht

local instance planeBranchBoundaryRealInner :
    InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _

local instance planeBranchBoundaryRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

/-- The actual analytic sphere-link embedding retains its positive Circle
orientation in the cylinder-to-sphere ambient diffeotopy. -/
theorem exists_plane_branch_braid_link_diffeotopy_with_orientation
    {F : ℂ → EuclideanSpace ℂ (Fin 2)} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (i : Fin 2) (a : ℕ) (ha : 0 < a)
    (hpower : ∀ᶠ z in 𝓝 (0 : ℂ), F z i = z ^ a)
    (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hcont : ContinuousOn F (Metric.closedBall 0 R₀))
    (hinj : InjOn F (Metric.closedBall 0 R₀))
    (H : EuclideanSpace ℂ (Fin 2) → ℂ)
    (himage : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℂ (Fin 2)),
      H y = 0 ↔ y ∈ F '' Metric.closedBall 0 R₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ (r : ℝ), 0 < r ∧ r < R₀ ∧
      ∃ (L₀ L₁ : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
          (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
        (∀ u, (L₀ u : EuclideanSpace ℂ (Fin 2)) = planeRadialNormalization (F (r • (u : ℂ)))) ∧
        (∀ u, ‖(L₀ u : EuclideanSpace ℂ (Fin 2)) i‖⁻¹ •
          (L₀ u : EuclideanSpace ℂ (Fin 2)) i = (u : ℂ) ^ a) ∧
        Set.range (fun u => (L₁ u : EuclideanSpace ℂ (Fin 2))) =
          (fun y : EuclideanSpace ℂ (Fin 2) => ε⁻¹ • y) ''
            (Metric.sphere 0 ε ∩ {y | H y = 0}) ∧
        (∀ θ : ℝ,
          0 < (inner ℂ (L₁ (Circle.exp θ) : EuclideanSpace ℂ (Fin 2))
            (deriv (fun t : ℝ => (L₁ (Circle.exp t) : EuclideanSpace ℂ (Fin 2))) θ)).im) ∧
        ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
          ∀ u, Φ.final (L₀ u) = L₁ u := by
  have hσ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hσmem (t : ℝ) : Real.smoothTransition t ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  obtain ⟨R, hR, hRS, hfamilies⟩ := exists_plane_branch_mixed_level_families_with_orientation
    hF hF0 i a ha hpower (Metric.closedBall_mem_nhds (0 : ℂ) hR₀) hinj hσ hσmem
  have hunique (z : ℂ) (hz : z ∈ Metric.closedBall 0 R₀) (hzero : F z = 0) : z = 0 :=
    hinj hz (Metric.mem_closedBall_self hR₀.le) (hzero.trans hF0.symm)
  have hshrink := eventually_mem_image_iff_of_compact_unique_fibre
    (isCompact_closedBall (0 : ℂ) R₀) hcont
    (Metric.ball_mem_nhds (0 : ℂ) hR) (Metric.ball_subset_closedBall.trans hRS) hunique
  have heq : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℂ (Fin 2)),
      H y = 0 ↔ y ∈ F '' Metric.ball 0 R := by
    filter_upwards [himage, hshrink] with y hy hs
    exact hy.trans hs.symm
  obtain ⟨δ, hδ, hδeq⟩ := Metric.eventually_nhds_iff.mp heq
  refine ⟨min (R ^ a) δ, lt_min (pow_pos hR a) hδ, ?_⟩
  intro ε hε hεsmall
  have hεR : ε < R ^ a := hεsmall.trans_le (min_le_left _ _)
  have hεδ : ε < δ := hεsmall.trans_le (min_le_right _ _)
  have hc : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hcR : ε ^ 2 < R ^ (2 * a) := by
    have hsq : ε ^ 2 < (R ^ a) ^ 2 := sq_lt_sq₀ hε.le (pow_pos hR a).le |>.mpr hεR
    simpa only [← pow_mul, Nat.mul_comm a 2] using hsq
  obtain ⟨hlevels, hs, hn, he, hphase, hstart, hpositive, hend⟩ := hfamilies (ε ^ 2) hc hcR
  let K := planeMixedLevelFamily hlevels Real.smoothTransition
  obtain ⟨L₀, L₁, hL₀, hL₁, Φ, hΦ⟩ := exists_plane_sphere_family_endpoint_diffeotopy K
    (fun t u => hn (u, t)) hs
    (planeSphereFamily_mfderiv_injective_of_power_phase K i ha hs hphase)
    (fun t => (he t).isEmbedding)
  let r : ℝ := (ε ^ 2) ^ ((2 * a : ℕ) : ℝ)⁻¹
  have hr : 0 < r := Real.rpow_pos_of_pos hc _
  have hrR : r < R := by
    have hn : 2 * a ≠ 0 := by omega
    have hlt := Real.rpow_lt_rpow hc.le hcR
      (inv_pos.mpr (show (0 : ℝ) < (2 * a : ℕ) by exact_mod_cast Nat.pos_of_ne_zero hn))
    simpa only [Real.pow_rpow_inv_natCast hR.le hn] using hlt
  have hRR₀ : R ≤ R₀ := by
    have hz : (R : ℂ) ∈ Metric.closedBall 0 R := by
      simp [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR]
    simpa [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR] using hRS hz
  refine ⟨r, hr, hrR.trans_le hRR₀, L₀, L₁, ?_, ?_, ?_, ?_, Φ, hΦ⟩
  · intro u
    exact (hL₀ u).trans (hstart 0 Real.smoothTransition.zero u)
  · intro u
    rw [hL₀]
    exact hphase (u, 0)
  · have hrange := hend 1 Real.smoothTransition.one
    rw [Real.sqrt_sq hε.le] at hrange
    rw [show (fun u => (L₁ u : EuclideanSpace ℂ (Fin 2))) = (fun u => K (u, 1)) from
      funext hL₁, hrange]
    congr 1
    ext y
    constructor
    · rintro ⟨hy, hyF⟩
      exact ⟨hy, (hδeq (by simpa only [Metric.mem_sphere, dist_zero_right] using
        (show dist y 0 < δ from (Metric.mem_sphere.mp hy).trans_lt hεδ))).mpr hyF⟩
    · rintro ⟨hy, hyH⟩
      exact ⟨hy, (hδeq ((Metric.mem_sphere.mp hy).trans_lt hεδ)).mp hyH⟩
  · intro θ
    have heq : (fun t : ℝ => (L₁ (Circle.exp t) : EuclideanSpace ℂ (Fin 2))) =
        (fun t : ℝ => K (Circle.exp t, 1)) := funext fun t => hL₁ (Circle.exp t)
    rw [heq, hL₁]
    exact hpositive 1 Real.smoothTransition.one θ


end OnLeConjecture.Analytic
