/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CurveSphereRadialGraph
public import OnLeConjecture.Analytic.PlaneBranchBoundaryOrientation

/-! # Positive and incoming orientations of the same sphere radial graph

Counterclockwise source angles give positive Hermitian angular tangents.
Inverting the unit source parameter reverses the derivative and gives the
incoming sign required for a hole in the exterior surface.
-/

@[expose] public noncomputable section

open Filter Set Metric Function
open scoped Topology ContDiff Manifold

attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.Analytic

set_option backward.isDefEq.respectTransparency false in
/-- A positively radial analytic sphere graph and its explicitly reversed
parametrization have opposite strict tangent signs. -/
theorem sphere_radialGraph_orientation
    {F : ℂ → EuclideanSpace ℂ (Fin 2)} {ρ : Circle → ℝ} {ε : ℝ}
    (hρ : ∀ u, 0 < ρ u) (hs : ContMDiff (𝓡 1) 𝓘(ℝ) ∞ ρ)
    (hF : ∀ u : Circle, DifferentiableAt ℂ F (ρ u • (u : ℂ)))
    (hp : ∀ u : Circle, 0 < fderiv ℝ (fun z => ‖F z‖ ^ 2)
      (ρ u • (u : ℂ)) (ρ u • (u : ℂ)))
    (hn : ∀ u : Circle, ‖F (ρ u • (u : ℂ))‖ = ε) :
    (∀ θ : ℝ, 0 < (inner ℂ
      (F (ρ (Circle.exp θ) • (Circle.exp θ : ℂ)))
      (deriv (fun t : ℝ => F (ρ (Circle.exp t) • (Circle.exp t : ℂ))) θ)).im) ∧
    (∀ θ : ℝ, (inner ℂ
      (F (ρ ((Circle.exp θ)⁻¹) • (((Circle.exp θ)⁻¹ : Circle) : ℂ)))
      (deriv (fun t : ℝ => F (ρ ((Circle.exp t)⁻¹) •
        (((Circle.exp t)⁻¹ : Circle) : ℂ))) θ)).im < 0) := by
  let C : ℝ → EuclideanSpace ℂ (Fin 2) :=
    fun t => F (ρ (Circle.exp t) • (Circle.exp t : ℂ))
  have hρd : Differentiable ℝ (fun t : ℝ => ρ (Circle.exp t)) :=
    (hs.comp contMDiff_circleExp).contDiff.differentiable (by simp)
  have hCd (θ : ℝ) : DifferentiableAt ℝ C θ := by
    apply (hF (Circle.exp θ)).restrictScalars ℝ |>.comp θ
    exact (hasDerivAt_radial_circleExp (hρd θ) (hρ _).ne').differentiableAt
  have hpositive (θ : ℝ) : 0 < (inner ℂ (C θ) (deriv C θ)).im := by
    apply radial_curve_sphere_tangent_im_pos (hρd θ) (hρ _) (hF _) (hp _)
    filter_upwards [] with t
    rw [hn, hn]
  refine ⟨hpositive, ?_⟩
  intro θ
  have hrev : (fun t : ℝ => F (ρ ((Circle.exp t)⁻¹) •
      (((Circle.exp t)⁻¹ : Circle) : ℂ))) = fun t => C (-t) := by
    funext t
    simp only [C, Circle.exp_neg]
  have hd : deriv (fun t => C (-t)) θ = -deriv C (-θ) := by
    simpa only [Function.comp_def, neg_one_smul] using
      ((hCd (-θ)).hasDerivAt.scomp θ (hasDerivAt_neg θ)).deriv
  rw [hrev, hd, inner_neg_right, Complex.neg_im]
  have hpoint : F (ρ ((Circle.exp θ)⁻¹) •
      (((Circle.exp θ)⁻¹ : Circle) : ℂ)) = C (-θ) := by
    simp only [C, Circle.exp_neg]
  rw [hpoint]
  exact neg_neg_of_pos (hpositive (-θ))

end OnLeConjecture.Analytic
