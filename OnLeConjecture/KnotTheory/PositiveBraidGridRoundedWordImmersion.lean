/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRoundedWordCircle
public import OnLeConjecture.DifferentialTopology.ComplexSolidTorus
public import OnLeConjecture.Analytic.PlaneBranchBraidLinkIsotopy

/-! # Immersion of the native rounded-word circle

The complex cylinder coordinates detect every nonzero strand velocity. The exact
period formula therefore gives injective native differentials, including the seam.
-/

@[expose] public noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic OnLeConjecture.DifferentialTopology
attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.KnotTheory

private theorem injective_of_ne_zero_one_dimensional
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hV : Module.finrank ℝ V = 1) (D : V →L[ℝ] E) (hD : D ≠ 0) : Function.Injective D := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change D x = 0 at hx
  by_contra hx0
  apply hD
  ext y
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hV hx0 y
  simp [hx]

/-- Cylinder coordinates cannot annihilate a regular real-parameter strand. -/
theorem roundedCylinder_deriv_ne_zero {T : ℝ} (hT : 0 < T)
    {h : ℝ → ℝ × ℂ} {t : ℝ} (hd : DifferentiableAt ℝ h t) (hne : deriv h t ≠ 0) :
    deriv (fun q => (Complex.exp (((2 * Real.pi / T * (h q).1 : ℝ) : ℂ) * Complex.I),
      (h q).2)) t ≠ 0 := by
  let v := deriv h t
  have hh : HasDerivAt h v t := hd.hasDerivAt
  have hfst : HasDerivAt (fun q => (h q).1) v.1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℂ).hasFDerivAt.comp_hasDerivAt t hh
  have hsnd : HasDerivAt (fun q => (h q).2) v.2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℂ).hasFDerivAt.comp_hasDerivAt t hh
  have hx := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
    (hfst.const_mul (2 * Real.pi / T))).mul_const Complex.I
  have he := hx.cexp.prodMk hsnd
  change HasDerivAt _ (Complex.exp (((2 * Real.pi / T * (h t).1 : ℝ) : ℂ) * Complex.I) *
    (((2 * Real.pi / T * v.1 : ℝ) : ℂ) * Complex.I), v.2) t at he
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at he
  rw [he.deriv]
  intro hz
  have hz₂ : v.2 = 0 := congrArg Prod.snd hz
  have hz₁ := congrArg Prod.fst hz
  have hv₁ : v.1 = 0 := by
    have hc : (2 * Real.pi / T : ℝ) ≠ 0 := div_ne_zero Real.two_pi_pos.ne' hT.ne'
    simpa only [Prod.fst_zero, mul_eq_zero, Complex.exp_ne_zero, false_or,
      Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero, mul_eq_zero, hc] using hz₁
  apply hne
  exact Prod.ext hv₁ hz₂

set_option backward.isDefEq.respectTransparency false in
/-- A nonzero velocity in complex coordinates forces injectivity of the native
circle differential, since its source tangent space has dimension one. -/
theorem circle_cylinder_mfderiv_injective_of_curve
    {F : Circle → Circle × ℂ} (hF : ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ F)
    {γ : ℝ → Circle} {θ : ℝ} (hγ : ContMDiffAt 𝓘(ℝ) (𝓡 1) ∞ γ θ)
    (hne : deriv (fun t => (((F (γ t)).1 : ℂ), (F (γ t)).2)) θ ≠ 0) :
    Function.Injective (mfderiv (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) F (γ θ)) := by
  apply injective_of_ne_zero_one_dimensional (V := EuclideanSpace ℝ (Fin 1))
    (E := EuclideanSpace ℝ (Fin 1) × ℂ) (by simp) _
  intro hz
  let J : Circle × ℂ → ℂ × ℂ := fun p => ((p.1 : ℂ), p.2)
  have hJ : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ × ℂ) ∞ J :=
    (contMDiff_coe_sphere.comp contMDiff_fst).prodMk_space contMDiff_snd
  have hFγ := mfderiv_comp θ (hF.mdifferentiableAt (by simp))
    (hγ.mdifferentiableAt (by simp))
  have hJFγ := mfderiv_comp θ (hJ.mdifferentiableAt (by simp))
    ((hF.contMDiffAt.comp θ hγ).mdifferentiableAt (by simp))
  rw [hFγ, hz, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero] at hJFγ
  apply hne
  change deriv (J ∘ (F ∘ γ)) θ = 0
  rw [deriv, ← mfderiv_eq_fderiv, hJFγ]
  rfl

/-- The exact rounded-word circle family is immersed at every point and time. -/
theorem positiveRoundedWord_circle_family_mfderiv_injective {m : ℕ} (hm : 0 < m)
    (w : PositiveAdjacentWord m) (σ : Equiv.Perm (Fin m))
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (hls : ∀ j, ContDiff ℝ ∞ (l j)) (hus : ∀ j, ContDiff ℝ ∞ (u j))
    {F : Circle × ℝ → Circle × ℂ}
    (hF : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ F)
    (he : ∀ k θ s, θ ∈ Icc (0 : ℝ) (2 * Real.pi) →
      F (braidCircleSheet m k θ, s) = positiveRectilinearCylinderPoint w
        (positiveRoundedWordDeformation w l u (σ k) s (positiveRoundedWordPeriodTime w θ)))
    (s : ℝ) (v : Circle) :
    Function.Injective (mfderiv (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) (fun v => F (v, s)) v) := by
  obtain ⟨θ, hθ, k, rfl⟩ := exists_braidCircleSheet_half_open hm v
  have hFs : ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℂ)) ∞ (fun v => F (v, s)) :=
    hF.comp (contMDiff_id.prodMk contMDiff_const)
  have hγ : ContMDiff 𝓘(ℝ) (𝓡 1) ∞ (braidCircleSheet m k) :=
    contMDiff_circleExp.comp (((contDiff_id.add contDiff_const).div_const (m : ℝ)).contMDiff)
  apply circle_cylinder_mfderiv_injective_of_curve hFs hγ.contMDiffAt
  let H : ℝ → ℝ × ℂ := fun q => positiveRoundedWordDeformation w l u (σ k) s
    (positiveRoundedWordPeriodTime w q)
  have hH : ContDiff ℝ ∞ H :=
    (positiveRoundedWordDeformation_contDiff w hls hus (σ k)).comp
      (contDiff_const.prodMk (positiveRoundedWordPeriodTime_contDiff w))
  have ht : HasDerivAt (positiveRoundedWordPeriodTime w)
      ((2 * (w.length : ℝ) + 1) / (2 * Real.pi)) θ := by
    change HasDerivAt (fun q : ℝ => (2 * (w.length : ℝ) + 1) * q / (2 * Real.pi)) _ θ
    convert! ((hasDerivAt_id θ).const_mul
      (2 * (w.length : ℝ) + 1 )).div_const (2 * Real.pi) using 1
    simp
  have hD := (((positiveRoundedWordDeformation_contDiff w hls hus (σ k)).comp
    ((contDiff_const (c := s)).prodMk contDiff_id)).differentiable (by simp)
      (positiveRoundedWordPeriodTime w θ)).hasDerivAt.scomp θ ht
  change HasDerivAt H (((2 * (w.length : ℝ) + 1) / (2 * Real.pi)) •
    deriv (positiveRoundedWordDeformation w l u (σ k) s)
      (positiveRoundedWordPeriodTime w θ)) θ at hD
  have hHne : deriv H θ ≠ 0 := by
    rw [hD.deriv]
    apply smul_ne_zero (div_ne_zero (by positivity) Real.two_pi_pos.ne')
    exact positiveRoundedWordDeformation_deriv_ne_zero w hl hu hU hls hus (σ k) s
      (positiveRoundedWordPeriodTime_mem w ⟨hθ.1, hθ.2.le⟩)
  have hCn := roundedCylinder_deriv_ne_zero
    (show (0 : ℝ) < 2 * (w.length : ℝ) + 1 by positivity)
    (hH.differentiable (by simp) θ) hHne
  let A : ℝ → ℂ × ℂ := fun q =>
    (((F (braidCircleSheet m k q, s)).1 : ℂ), (F (braidCircleSheet m k q, s)).2)
  let B : ℝ → ℂ × ℂ := fun q =>
    (Complex.exp (((2 * Real.pi / (2 * (w.length : ℝ) + 1) * (H q).1 : ℝ) : ℂ) * Complex.I),
      (H q).2)
  have hA : ContDiff ℝ ∞ A :=
    (((contMDiff_coe_sphere.comp hFs.fst).prodMk_space hFs.snd).comp hγ).contDiff
  have hB : ContDiff ℝ ∞ B := by
    apply ContDiff.prodMk _ hH.snd
    exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hH.fst)).mul contDiff_const).cexp
  have hAB : EqOn A B (Icc (0 : ℝ) (2 * Real.pi)) := by
    intro q hq
    dsimp [A, B]
    rw [he k q s hq]
    simp only [positiveRectilinearCylinderPoint, Circle.coe_exp, H]
    congr 2
    push_cast
    ring
  have huniq := uniqueDiffOn_Icc Real.two_pi_pos θ ⟨hθ.1, hθ.2.le⟩
  have hde := (hB.differentiable (by simp) θ).hasDerivAt.hasDerivWithinAt.congr_of_mem hAB
    ⟨hθ.1, hθ.2.le⟩
  have heder : deriv A θ = deriv B θ :=
    ((hA.differentiable (by simp) θ).hasDerivAt.hasDerivWithinAt.derivWithin huniq).symm.trans
      (hde.derivWithin huniq)
  change deriv A θ ≠ 0
  rw [heder]
  exact hCn

end OnLeConjecture.KnotTheory
