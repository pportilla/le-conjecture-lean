/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchClosedBraid
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # A smooth motion from a parameter circle to a positive radial graph

The interpolating parameter curves retain their unit direction. This proves
injectivity and immersion without radial monotonicity at the original circle.
-/

@[expose] public noncomputable section

open Set Metric Function Manifold
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

/-- Smooth interpolation of the radii of a constant circle and a radial graph. -/
def radialGraphMotionRadius (R : ℝ) (ρ : Circle → ℝ) (p : ℝ × Circle) : ℝ :=
  (1 - Real.smoothTransition p.1) * R + Real.smoothTransition p.1 * ρ p.2

/-- The interpolating parameter curve. -/
def radialGraphMotion (R : ℝ) (ρ : Circle → ℝ) (p : ℝ × Circle) : ℂ :=
  radialGraphMotionRadius R ρ p • (p.2 : ℂ)

theorem radialGraphMotionRadius_pos {R : ℝ} (hR : 0 < R) {ρ : Circle → ℝ}
    (hρ : ∀ u, 0 < ρ u) (p : ℝ × Circle) : 0 < radialGraphMotionRadius R ρ p := by
  have h0 := Real.smoothTransition.nonneg p.1
  have h1 := Real.smoothTransition.le_one p.1
  have hp := hρ p.2
  unfold radialGraphMotionRadius
  by_cases h : Real.smoothTransition p.1 = 1
  · simp only [h, sub_self, zero_mul, one_mul, zero_add]; exact hp
  · have hlt : Real.smoothTransition p.1 < 1 := lt_of_le_of_ne h1 h
    positivity

theorem radialGraphMotionRadius_le {R : ℝ} {ρ : Circle → ℝ}
    (hρ : ∀ u, ρ u ≤ R) (p : ℝ × Circle) : radialGraphMotionRadius R ρ p ≤ R := by
  have h := mul_le_mul_of_nonneg_left (hρ p.2) (Real.smoothTransition.nonneg p.1)
  unfold radialGraphMotionRadius
  nlinarith

theorem radialGraphMotion_norm {R : ℝ} (hR : 0 < R) {ρ : Circle → ℝ}
    (hρ : ∀ u, 0 < ρ u) (p : ℝ × Circle) :
    ‖radialGraphMotion R ρ p‖ = radialGraphMotionRadius R ρ p := by
  rw [radialGraphMotion, norm_smul, Real.norm_eq_abs,
    abs_of_pos (radialGraphMotionRadius_pos hR hρ p), Circle.norm_coe, mul_one]

theorem radialGraphMotion_phase {R : ℝ} (hR : 0 < R) {ρ : Circle → ℝ}
    (hρ : ∀ u, 0 < ρ u) (p : ℝ × Circle) :
    ‖radialGraphMotion R ρ p‖⁻¹ • radialGraphMotion R ρ p = (p.2 : ℂ) := by
  rw [radialGraphMotion_norm hR hρ, radialGraphMotion, smul_smul,
    inv_mul_cancel₀ (radialGraphMotionRadius_pos hR hρ p).ne', one_smul]

set_option backward.isDefEq.respectTransparency false in
theorem radialGraphMotion_contMDiff (R : ℝ) {ρ : Circle → ℝ}
    (hρ : ContMDiff (𝓡 1) 𝓘(ℝ) ∞ ρ) :
    ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞ (radialGraphMotion R ρ) := by
  have hs : ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) ∞
      (fun p : ℝ × Circle => Real.smoothTransition p.1) :=
    Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst
  have hr : ContMDiff (𝓘(ℝ).prod (𝓡 1)) 𝓘(ℝ) ∞
      (radialGraphMotionRadius R ρ) := by
    convert (((contMDiff_const.sub hs).smul (contMDiff_const (c := R))).add
        (hs.smul (hρ.comp contMDiff_snd))) using 1 <;> rfl
  exact hr.smul (contMDiff_coe_sphere.comp contMDiff_snd)

theorem radialGraphMotion_injective {R : ℝ} (hR : 0 < R) {ρ : Circle → ℝ}
    (hρ : ∀ u, 0 < ρ u) (t : ℝ) :
    Injective (fun u => radialGraphMotion R ρ (t, u)) := by
  intro u v huv
  change radialGraphMotion R ρ (t, u) = radialGraphMotion R ρ (t, v) at huv
  apply Subtype.ext
  rw [← radialGraphMotion_phase hR hρ (t, u), ← radialGraphMotion_phase hR hρ (t, v), huv]

set_option backward.isDefEq.respectTransparency false in
theorem radialGraphMotion_mfderiv_injective {R : ℝ} (hR : 0 < R) {ρ : Circle → ℝ}
    (hρ : ∀ u, 0 < ρ u) (hs : ContMDiff (𝓡 1) 𝓘(ℝ) ∞ ρ) (t : ℝ) (u : Circle) :
    Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun v => radialGraphMotion R ρ (t, v)) u) := by
  let C : Circle → ℂ := fun v => radialGraphMotion R ρ (t, v)
  let P : ℂ → ℂ := fun z => ‖z‖⁻¹ • z
  have hC : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ C :=
    (radialGraphMotion_contMDiff R hs).comp (contMDiff_const.prodMk contMDiff_id)
  have hn : C u ≠ 0 := norm_pos_iff.mp (by
    rw [show C u = radialGraphMotion R ρ (t, u) from rfl,
      radialGraphMotion_norm hR hρ]
    exact radialGraphMotionRadius_pos hR hρ _)
  have hP : ContDiffAt ℝ ∞ P (C u) :=
    ((contDiffAt_id.norm ℂ hn).inv (norm_ne_zero_iff.mpr hn)).smul contDiffAt_id
  have heq : P ∘ C = fun v : Circle => (v : ℂ) ^ 1 := by
    funext v
    simpa only [P, C, Function.comp_apply, pow_one] using radialGraphMotion_phase hR hρ (t, v)
  have hchain := mfderiv_comp u (hP.differentiableAt (by simp)).mdifferentiableAt
    (hC.mdifferentiableAt (by simp))
  have hd := (mfderiv_congr (I := 𝓡 1) (I' := 𝓘(ℝ, ℂ)) (x := u) heq).symm.trans hchain
  intro v w hvw
  apply circle_pow_coe_mfderiv_injective (by decide : 0 < 1) u
  exact (congrArg (fun L => L v) hd).trans
    ((congrArg (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) P (C u)) hvw).trans
      (congrArg (fun L => L w) hd).symm)

theorem radialGraphMotion_of_nonpos (R : ℝ) (ρ : Circle → ℝ) {t : ℝ} (ht : t ≤ 0)
    (u : Circle) : radialGraphMotion R ρ (t, u) = R • (u : ℂ) := by
  simp only [radialGraphMotion, radialGraphMotionRadius, Real.smoothTransition.zero_of_nonpos ht,
    sub_zero, one_mul, zero_mul, add_zero]

theorem radialGraphMotion_of_one_le (R : ℝ) (ρ : Circle → ℝ) {t : ℝ} (ht : 1 ≤ t)
    (u : Circle) : radialGraphMotion R ρ (t, u) = ρ u • (u : ℂ) := by
  simp only [radialGraphMotion, radialGraphMotionRadius, Real.smoothTransition.one_of_one_le ht,
    sub_self, zero_mul, one_mul, zero_add]

end OnLeConjecture.Analytic
