/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchSheetRotation
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Angular derivatives of analytic branch sheets

The parameter `θ` is the angle of the power coordinate of the branch. The
source parameter therefore rotates at speed `1 / a`. This file identifies
the derivative of a sheet difference along that parameter and proves the
positive crossing determinant at every double point of a projection.

The crossing determinant is the product of the height difference with the
negative derivative of the projected difference. This convention makes
counterclockwise rotation positive. Constructing a finite braid word and
identifying its smooth closure remain separate statements.

The analytic-to-crossing argument follows the unnumbered positive-braid
paragraph on page 12 of Lee Rudolph, *Some knot theory of complex plane
curves*, arXiv:math/0106058v1. No result from that source is assumed here.
-/

@[expose] public noncomputable section

open Set Metric

namespace OnLeConjecture.Analytic

/-- A source parameter whose `a`th power turns at unit angular speed. -/
def planeBranchAngularParameter (a : ℕ) (r θ : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp (((θ : ℂ) / (a : ℂ)) * Complex.I)

theorem planeBranchAngularParameter_norm (a : ℕ) (r θ : ℝ) :
    ‖planeBranchAngularParameter a r θ‖ = |r| := by
  unfold planeBranchAngularParameter
  have hn : ‖Complex.exp (((θ : ℂ) / (a : ℂ)) * Complex.I)‖ = 1 := by
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using
      Complex.norm_exp_ofReal_mul_I (θ / (a : ℝ))
  simp only [norm_mul, hn, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem planeBranchAngularParameter_pow {a : ℕ} (ha : 0 < a) (r θ : ℝ) :
    planeBranchAngularParameter a r θ ^ a =
      (r : ℂ) ^ a * Complex.exp ((θ : ℂ) * Complex.I) := by
  unfold planeBranchAngularParameter
  rw [mul_pow, ← Complex.exp_nat_mul]
  congr 2
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp

theorem planeBranchAngularParameter_hasDerivAt (a : ℕ) (r θ : ℝ) :
    HasDerivAt (planeBranchAngularParameter a r)
      (Complex.I / (a : ℂ) * planeBranchAngularParameter a r θ) θ := by
  have h := (((Complex.ofRealCLM.hasDerivAt (x := θ)).div_const (a : ℂ)).mul_const
    Complex.I).cexp.const_mul (r : ℂ)
  apply h.congr_deriv
  simp only [planeBranchAngularParameter, Complex.ofRealCLM_apply, Complex.ofReal_one]
  ring

/-- The sheet difference as a function of the base angle. -/
def planeBranchAngularDifference (F : ℂ → Source 2) (i : Fin 2) (ζ : ℂ)
    (a : ℕ) (r : ℝ) : ℝ → ℂ :=
  fun θ => planeBranchSheetDifference F i ζ (planeBranchAngularParameter a r θ)

theorem deriv_comp_planeBranchAngularParameter
    {d : ℂ → ℂ} (a : ℕ) (r θ : ℝ)
    (hd : DifferentiableAt ℂ d (planeBranchAngularParameter a r θ)) :
    deriv (fun t : ℝ => d (planeBranchAngularParameter a r t)) θ =
      Complex.I / (a : ℂ) * planeBranchAngularParameter a r θ *
        deriv d (planeBranchAngularParameter a r θ) := by
  have h := hd.hasDerivAt.comp θ (planeBranchAngularParameter_hasDerivAt a r θ)
  simpa only [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h.deriv

theorem im_logDeriv_comp_planeBranchAngularParameter
    {d : ℂ → ℂ} (a : ℕ) (r θ : ℝ)
    (hd : DifferentiableAt ℂ d (planeBranchAngularParameter a r θ)) :
    (deriv (fun t : ℝ => d (planeBranchAngularParameter a r t)) θ /
      d (planeBranchAngularParameter a r θ)).im =
    (planeBranchAngularParameter a r θ *
      deriv d (planeBranchAngularParameter a r θ) /
      d (planeBranchAngularParameter a r θ)).re / (a : ℝ) := by
  rw [deriv_comp_planeBranchAngularParameter a r θ hd]
  have heq : (Complex.I / (a : ℂ) * planeBranchAngularParameter a r θ *
      deriv d (planeBranchAngularParameter a r θ) /
      d (planeBranchAngularParameter a r θ)) =
    Complex.I * ((planeBranchAngularParameter a r θ *
      deriv d (planeBranchAngularParameter a r θ) /
      d (planeBranchAngularParameter a r θ)) / (a : ℂ)) := by ring
  rw [heq]
  simp

/-- Angular positivity determines the crossing sign whenever the real
projection of the difference vanishes. It also implies transversality. -/
theorem crossing_determinant_pos_of_im_div_pos
    {v w : ℂ} (hw : w ≠ 0) (hrot : 0 < (v / w).im) (hproj : w.re = 0) :
    0 < -v.re * w.im := by
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  have heq : (v / w).im = (-v.re * w.im) / Complex.normSq w := by
    rw [Complex.div_im, hproj]
    ring
  rw [heq] at hrot
  exact (div_pos_iff_of_pos_right hn).mp hrot

theorem deriv_re_eq_re_deriv {f : ℝ → ℂ} {θ : ℝ}
    (hf : DifferentiableAt ℝ f θ) :
    deriv (fun t => (f t).re) θ = (deriv f θ).re :=
  (Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ hf.hasDerivAt).deriv

/-- A nonzero complex rescaling changes the direction of projection without
changing the angular derivative or the crossing sign. -/
theorem projected_crossing_determinant_pos
    {f : ℝ → ℂ} {θ : ℝ} (hf : DifferentiableAt ℝ f θ) (hne : f θ ≠ 0)
    (hrot : 0 < (deriv f θ / f θ).im) {c : ℂ} (hc : c ≠ 0)
    (hproj : (c * f θ).re = 0) :
    0 < -deriv (fun t => (c * f t).re) θ * (c * f θ).im ∧
      deriv (fun t => (c * f t).re) θ ≠ 0 := by
  have hdc := hf.hasDerivAt.const_mul c
  have hd := deriv_re_eq_re_deriv hdc.differentiableAt
  rw [hdc.deriv] at hd
  have hrotc : 0 < ((c * deriv f θ) / (c * f θ)).im := by
    rwa [mul_div_mul_left _ _ hc]
  have hp := crossing_determinant_pos_of_im_div_pos (mul_ne_zero hc hne) hrotc hproj
  rw [← hd] at hp
  refine ⟨hp, ?_⟩
  intro heq
  simp only [heq, neg_zero, zero_mul, lt_self_iff_false] at hp

/-- Holomorphicity on the representative ball gives the complex derivative
at every nonzero source parameter of a sheet difference. -/
theorem planeBranchSheetDifference_analyticAt_of_mem_ball
    {F : ℂ → Source 2} {R : ℝ} (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (i : Fin 2) {a : ℕ} (ha : 0 < a) {ζ : ℂ} (hζ : ζ ^ a = 1)
    {z : ℂ} (hz : z ∈ ball 0 R) :
    AnalyticAt ℂ (planeBranchSheetDifference F i ζ) z := by
  have hnorm : ‖ζ‖ = 1 := (norm_pow_eq_one_iff ha ζ).mp (by rw [hζ, norm_one])
  have hrot : ζ * z ∈ ball 0 R := by
    simpa only [mem_ball, dist_zero_right, norm_mul, hnorm, one_mul] using hz
  have hc (w : ℂ) (hw : w ∈ ball 0 R) :
      AnalyticAt ℂ (fun z => F z i.rev) w :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) i.rev).analyticAt _).comp
      (hF w hw)
  exact ((hc _ hrot).comp (analyticAt_const.mul analyticAt_id)).sub (hc _ hz)

/-- One radius makes all differences rotate positively with respect to the
base angle, for every smaller source circle. The factor `1 / a` is included. -/
theorem exists_radius_planeBranchAngularDifference_im_pos
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} (ha : 0 < a) {R : ℝ} (hR : 0 < R)
    (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hi : InjOn F (ball 0 R)) (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      ∀ r : ℝ, 0 < r → r < ρ → ∀ ζ : ℂ, ζ ^ a = 1 → ζ ≠ 1 → ∀ θ : ℝ,
        planeBranchAngularDifference F i ζ a r θ ≠ 0 ∧
        DifferentiableAt ℝ (planeBranchAngularDifference F i ζ a r) θ ∧
        0 < (deriv (planeBranchAngularDifference F i ζ a r) θ /
          planeBranchAngularDifference F i ζ a r θ).im := by
  obtain ⟨ρ, hρ, hρR, hrot⟩ := exists_radius_planeBranchSheetDifference_re_pos
    (hF 0 (mem_ball_self hR)) ha hR hi hp
  refine ⟨ρ, hρ, hρR, ?_⟩
  intro r hr hrρ ζ hζ hζ1 θ
  have hz : planeBranchAngularParameter a r θ ∈ ball 0 ρ := by
    simpa only [mem_ball, dist_zero_right, planeBranchAngularParameter_norm,
      abs_of_pos hr] using hrρ
  have hz0 : planeBranchAngularParameter a r θ ≠ 0 := by
    apply norm_pos_iff.mp
    simpa only [planeBranchAngularParameter_norm, abs_of_pos hr] using hr
  have hd := (planeBranchSheetDifference_analyticAt_of_mem_ball hF i ha hζ
    (ball_subset_ball hρR hz)).differentiableAt
  obtain ⟨hne, hpos⟩ := hrot ζ hζ hζ1 _ hz hz0
  refine ⟨hne, (hd.hasDerivAt.comp θ
    (planeBranchAngularParameter_hasDerivAt a r θ)).differentiableAt, ?_⟩
  change 0 < (deriv (fun t : ℝ => planeBranchSheetDifference F i ζ
    (planeBranchAngularParameter a r t)) θ /
    planeBranchSheetDifference F i ζ (planeBranchAngularParameter a r θ)).im
  rw [im_logDeriv_comp_planeBranchAngularParameter a r θ hd]
  exact div_pos hpos (by exact_mod_cast ha)

/-- Every double point of a real projection of the analytic branch sheets
has positive crossing determinant and a nonzero projected derivative. -/
theorem exists_radius_planeBranchAngularDifference_crossings_pos
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} (ha : 0 < a) {R : ℝ} (hR : 0 < R)
    (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hi : InjOn F (ball 0 R)) (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      ∀ r : ℝ, 0 < r → r < ρ → ∀ ζ : ℂ, ζ ^ a = 1 → ζ ≠ 1 → ∀ θ : ℝ,
        (planeBranchAngularDifference F i ζ a r θ).re = 0 →
        0 < -(deriv (planeBranchAngularDifference F i ζ a r) θ).re *
          (planeBranchAngularDifference F i ζ a r θ).im ∧
        (deriv (planeBranchAngularDifference F i ζ a r) θ).re ≠ 0 := by
  obtain ⟨ρ, hρ, hρR, hrot⟩ :=
    exists_radius_planeBranchAngularDifference_im_pos ha hR hF hi hp
  refine ⟨ρ, hρ, hρR, ?_⟩
  intro r hr hrρ ζ hζ hζ1 θ hproj
  obtain ⟨hne, _, hpos⟩ := hrot r hr hrρ ζ hζ hζ1 θ
  have hcross := crossing_determinant_pos_of_im_div_pos hne hpos hproj
  refine ⟨hcross, ?_⟩
  intro heq
  simp only [heq, neg_zero, zero_mul, lt_self_iff_false] at hcross

/-- Every direction of projection has positive transverse crossings for the
actual analytic branch on every sufficiently small source circle. -/
theorem exists_radius_planeBranchAngularDifference_projected_crossings_pos
    {F : ℂ → Source 2} {i : Fin 2} {a : ℕ} (ha : 0 < a) {R : ℝ} (hR : 0 < R)
    (hF : AnalyticOnNhd ℂ F (ball 0 R))
    (hi : InjOn F (ball 0 R)) (hp : ∀ z ∈ ball 0 R, F z i = z ^ a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      ∀ r : ℝ, 0 < r → r < ρ → ∀ ζ : ℂ, ζ ^ a = 1 → ζ ≠ 1 →
      ∀ θ : ℝ, ∀ c : ℂ, c ≠ 0 →
        (c * planeBranchAngularDifference F i ζ a r θ).re = 0 →
        0 < -deriv (fun t => (c * planeBranchAngularDifference F i ζ a r t).re) θ *
          (c * planeBranchAngularDifference F i ζ a r θ).im ∧
        deriv (fun t => (c * planeBranchAngularDifference F i ζ a r t).re) θ ≠ 0 := by
  obtain ⟨ρ, hρ, hρR, hrot⟩ :=
    exists_radius_planeBranchAngularDifference_im_pos ha hR hF hi hp
  refine ⟨ρ, hρ, hρR, ?_⟩
  intro r hr hrρ ζ hζ hζ1 θ c hc hproj
  obtain ⟨hne, hd, hpos⟩ := hrot r hr hrρ ζ hζ hζ1 θ
  exact projected_crossing_determinant_pos hd hne hpos hc hproj

end OnLeConjecture.Analytic
