/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchAmbientIsotopy
public import OnLeConjecture.Analytic.PlaneBranchMixedLevels
public import OnLeConjecture.Analytic.PlaneBranchMixedLevelFamily
public import OnLeConjecture.Analytic.CurveLocalImageShrink
public import OnLeConjecture.Analytic.PlaneBranchPowerEquationCoverage
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # Ambient isotopies between the cylinder and sphere presentations of a branch -/

@[expose] public noncomputable section

open Filter Set Manifold
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

local instance planeBraidLinkRealInner : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
  InnerProductSpace.rclikeToReal ℂ _

local instance planeBraidLinkRealDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 2)) = 3 + 1) :=
  ⟨by rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]⟩

namespace OnLeConjecture.Analytic

/-- A globally smooth family of embedded sphere circles has ambient-isotopic endpoints.
The reindexing places times zero and one inside the open family interval. -/
theorem exists_plane_sphere_family_endpoint_diffeotopy
    (K : Circle × ℝ → EuclideanSpace ℂ (Fin 2))
    (hnorm : ∀ t u, ‖K (u, t)‖ = 1)
    (hsmooth : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ K)
    (hd : ∀ t u, Function.Injective
      (mfderiv (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) (fun v => K (v, t)) u))
    (he : ∀ t, Topology.IsEmbedding (fun u => K (u, t))) :
    ∃ (L₀ L₁ : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
        (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
      (∀ u, (L₀ u : EuclideanSpace ℂ (Fin 2)) = K (u, 0)) ∧
      (∀ u, (L₁ u : EuclideanSpace ℂ (Fin 2)) = K (u, 1)) ∧
      ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
        ∀ u, Φ.final (L₀ u) = L₁ u := by
  let J : Circle × ℝ → Circle × ℝ := fun p => (p.1, p.2 - 1)
  let K' : Circle × ℝ → EuclideanSpace ℂ (Fin 2) := fun p => K (J p)
  have hJ : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ)) ∞ J :=
    contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const)
  have hn' : ∀ c ∈ Ioo (0 : ℝ) 3, ∀ u : Circle, ‖K' (u, c)‖ = 1 :=
    fun c _ u => hnorm (c - 1) u
  have hs' : ∀ c ∈ Ioo (0 : ℝ) 3, ∀ u : Circle,
      ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ K' (u, c) :=
    fun _ _ _ => (hsmooth.comp hJ).contMDiffAt
  have hd' : ∀ c ∈ Ioo (0 : ℝ) 3, ∀ u : Circle, Function.Injective
      (mfderiv (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) (fun v => K' (v, c)) u) :=
    fun c _ u => hd (c - 1) u
  have he' : ∀ c ∈ Ioo (0 : ℝ) 3, Topology.IsEmbedding (fun u => K' (u, c)) :=
    fun c _ => he (c - 1)
  have h₀ : (1 : ℝ) ∈ Ioo 0 3 := by norm_num
  have h₁ : (2 : ℝ) ∈ Ioo 0 3 := by norm_num
  refine ⟨unitSphereFamilySlice (n := 3) K' hn' hs' hd' he' 1 h₀,
    unitSphereFamilySlice (n := 3) K' hn' hs' hd' he' 2 h₁, ?_, ?_, ?_⟩
  · intro u
    simp only [unitSphereFamilySlice_coe_apply, K', J, sub_self]
  · intro u
    simp only [unitSphereFamilySlice_coe_apply, K', J, show (2 : ℝ) - 1 = 1 by norm_num]
  · exact exists_unitSphereFamilyDiffeotopy (n := 3) K' hn' hs' hd' he' 1 2 h₀ h₁

set_option backward.isDefEq.respectTransparency false in
/-- The angular power identity forces each sphere-family slice to have
injective differential. This uses the actual phase of its selected coordinate. -/
theorem planeSphereFamily_mfderiv_injective_of_power_phase
    (K : Circle × ℝ → EuclideanSpace ℂ (Fin 2)) (i : Fin 2) {a : ℕ} (ha : 0 < a)
    (hsmooth : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ K)
    (hphase : ∀ p, ‖K p i‖⁻¹ • K p i = (p.1 : ℂ) ^ a) (t : ℝ) (u : Circle) :
    Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2))
      (fun v => K (v, t)) u) := by
  let C : Circle → EuclideanSpace ℂ (Fin 2) := fun v => K (v, t)
  let P : EuclideanSpace ℂ (Fin 2) → ℂ := fun y => ‖y i‖⁻¹ • y i
  have hC : ContMDiff (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ∞ C :=
    hsmooth.comp (contMDiff_id.prodMk (contMDiff_const (c := t)))
  have hi : C u i ≠ 0 := by
    intro hz
    have hp := hphase (u, t)
    change ‖C u i‖⁻¹ • C u i = (u : ℂ) ^ a at hp
    rw [hz, smul_zero] at hp
    exact pow_ne_zero _ u.coe_ne_zero hp.symm
  have hP : ContDiffAt ℝ ∞ P (C u) := by
    have hcoord : ContDiff ℝ ∞ (fun y : EuclideanSpace ℂ (Fin 2) => y i) :=
      (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 => ℂ) i).contDiff.restrict_scalars ℝ
    exact ((hcoord.contDiffAt.norm ℂ hi).inv (norm_ne_zero_iff.mpr hi)).smul hcoord.contDiffAt
  have heq : P ∘ C = fun v : Circle => (v : ℂ) ^ a := funext (fun v => hphase (v, t))
  have hchain := mfderiv_comp u (hP.differentiableAt (by simp)).mdifferentiableAt
    (hC.mdifferentiableAt (by simp))
  have hdEq := mfderiv_congr (I := 𝓡 1) (I' := 𝓘(ℝ, ℂ)) (x := u) heq
  have hd : mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun v : Circle => (v : ℂ) ^ a) u =
      (mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) 𝓘(ℝ, ℂ) P (C u)).comp
        (mfderiv (𝓡 1) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) C u) := hdEq.symm.trans hchain
  intro v w hvw
  apply circle_pow_coe_mfderiv_injective ha u
  exact (congrArg (fun L => L v) hd).trans
    ((congrArg (mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) 𝓘(ℝ, ℂ) P (C u)) hvw).trans
      (congrArg (fun L => L w) hd).symm)

/-- The actual sphere zero-set link of a power-normalized injective analytic
branch is ambient diffeotopic to its constant-parameter closed braid.
Both circles are native smooth embeddings into the unit three-sphere.
The covering coordinate has phase `u^a`, and the sphere endpoint has exactly
the scaled zero-set range of the given equation. -/
theorem exists_plane_branch_braid_link_diffeotopy_with_radius_bound
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
        ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
          ∀ u, Φ.final (L₀ u) = L₁ u := by
  have hσ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hσmem (t : ℝ) : Real.smoothTransition t ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  obtain ⟨R, hR, hRS, hfamilies⟩ := exists_plane_branch_mixed_level_families
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
  obtain ⟨hlevels, hs, hn, he, hphase, hstart, hend⟩ := hfamilies (ε ^ 2) hc hcR
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
  refine ⟨r, hr, hrR.trans_le hRR₀, L₀, L₁, ?_, ?_, ?_, Φ, hΦ⟩
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

/-- The radius-free form of the actual branch endpoint theorem. -/
theorem exists_plane_branch_braid_link_diffeotopy
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
      ∃ (r : ℝ), 0 < r ∧
      ∃ (L₀ L₁ : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
          (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
        (∀ u, (L₀ u : EuclideanSpace ℂ (Fin 2)) = planeRadialNormalization (F (r • (u : ℂ)))) ∧
        (∀ u, ‖(L₀ u : EuclideanSpace ℂ (Fin 2)) i‖⁻¹ •
          (L₀ u : EuclideanSpace ℂ (Fin 2)) i = (u : ℂ) ^ a) ∧
        Set.range (fun u => (L₁ u : EuclideanSpace ℂ (Fin 2))) =
          (fun y : EuclideanSpace ℂ (Fin 2) => ε⁻¹ • y) ''
            (Metric.sphere 0 ε ∩ {y | H y = 0}) ∧
        ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
          ∀ u, Φ.final (L₀ u) = L₁ u := by
  obtain ⟨ε₀, hε₀, hlinks⟩ := exists_plane_branch_braid_link_diffeotopy_with_radius_bound
    hF hF0 i a ha hpower R₀ hR₀ hcont hinj H himage
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hs
  obtain ⟨r, hr, _hrR, L₀, L₁, hL₀, hphase, hrange, Φ, hΦ⟩ := hlinks ε hε hs
  exact ⟨r, hr, L₀, L₁, hL₀, hphase, hrange, Φ, hΦ⟩

/-- An injective parametrization and its exact equation ideal supply the
analytic representative and all image-coverage hypotheses internally.
Every sufficiently small link of that equation is ambient diffeotopic to
an embedded circle whose selected-coordinate phase is `u^a`. -/
theorem PointedMapGerm.exists_braid_link_diffeotopy_of_component_order
    (β : PointedMapGerm 1 2) (hi : β.HasInjectiveRepresentative)
    (i : Fin 2) {a : ℕ} (ha : 0 < a)
    (ho : Germ.vanishingOrder (β.1.component i) = a)
    (W : Source 2 → ℂ) (hW : AnalyticAt ℂ W 0)
    (hker : RingHom.ker β.pullbackRingHom = Ideal.span {Germ.ofFunction W hW}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ (L₀ L₁ : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
          (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
        (∀ u, ‖(L₀ u : EuclideanSpace ℂ (Fin 2)) i‖⁻¹ •
          (L₀ u : EuclideanSpace ℂ (Fin 2)) i = (u : ℂ) ^ a) ∧
        Set.range (fun u => (L₁ u : EuclideanSpace ℂ (Fin 2))) =
          (fun y : EuclideanSpace ℂ (Fin 2) => ε⁻¹ • y) ''
            (Metric.sphere 0 ε ∩ {y | W ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0}) ∧
        ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
          ∀ u, Φ.final (L₀ u) = L₁ u := by
  obtain ⟨e, G, hG, hG0, _hg, R, hR, hF, hF0, hFa, hFi, hp, himage⟩ :=
    β.exists_injective_power_equation_coverage hi i ha ho W hW hker
  have hpower : ∀ᶠ z in 𝓝 (0 : ℂ),
      ((EuclideanSpace.equiv (Fin 2) ℂ).symm (G (curveParameterEquiv.symm z))) i = z ^ a := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) hR] with z hz
    exact hp z hz
  obtain ⟨ε₀, hε₀, hlinks⟩ := exists_plane_branch_braid_link_diffeotopy
    hF hF0 i a ha hpower R hR hFa.continuousOn hFi
    (fun y => W ((EuclideanSpace.equiv (Fin 2) ℂ) y)) himage
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεsmall
  obtain ⟨r, _hr, L₀, L₁, _hconstant, hphase, hrange, Φ, hΦ⟩ := hlinks ε hε hεsmall
  exact ⟨L₀, L₁, hphase, hrange, Φ, hΦ⟩

/-- Each singular section in the actual analytic assembly has a sphere
link ambient diffeotopic to a closed braid with its exact branch
multiplicity `a`, and `2 ≤ a ≤ m`. The sphere range uses the specified
analytic representative of the assembled local equation. -/
theorem SingularSectionPointData.exists_braid_link_diffeotopy
    {H : Source 2 → Source 3} {x : Source 2} {m : ℕ}
    (h : SingularSectionPointData H x m)
    (W : Source 2 → ℂ) (hW : AnalyticAt ℂ W 0)
    (hWgerm : localSectionEquation H x = Germ.ofFunction W hW) :
    ∃ (a : ℕ) (i : Fin 2), 2 ≤ a ∧ a ≤ m ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ (L₀ L₁ : TauCeti.SmoothEmbedding (𝓡 1) (𝓡 3) ∞ Circle
            (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)),
          (∀ u, ‖(L₀ u : EuclideanSpace ℂ (Fin 2)) i‖⁻¹ •
            (L₀ u : EuclideanSpace ℂ (Fin 2)) i = (u : ℂ) ^ a) ∧
          Set.range (fun u => (L₁ u : EuclideanSpace ℂ (Fin 2))) =
            (fun y : EuclideanSpace ℂ (Fin 2) => ε⁻¹ • y) ''
              (Metric.sphere 0 ε ∩ {y | W ((EuclideanSpace.equiv (Fin 2) ℂ) y) = 0}) ∧
          ∃ Φ : TauCeti.Diffeotopy (𝓡 3) ∞ (Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1),
            ∀ u, Φ.final (L₀ u) = L₁ u := by
  obtain ⟨β, a, i, ha2, ham, hi, hker, ho⟩ := h.exists_branch_component_order
  refine ⟨a, i, ha2, ham, ?_⟩
  apply β.exists_braid_link_diffeotopy_of_component_order hi i
    (lt_of_lt_of_le (by decide : 0 < 2) ha2) ho W hW
  simpa only [hWgerm] using hker

end OnLeConjecture.Analytic
