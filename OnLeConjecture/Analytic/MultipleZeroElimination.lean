/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.AnalyticImplicitFunction
public import OnLeConjecture.Analytic.MultipleZeroPersistence

/-!
# Analytic elimination at a multiple zero

Two equations with an invertible derivative in the point variables are
solved analytically. A positive order zero of a remaining scalar equation
then persists under a second complex parameter.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Analytic elimination of transverse equations reduces persistence of a
multiple zero to the scalar theorem. -/
theorem eventually_exists_fullZero_of_analyticElimination
    (plane : ((ℂ × ℂ) × E) → E)
    (third : ((ℂ × ℂ) × E) → ℂ)
    (q : E)
    (hplane : AnalyticAt ℂ plane ((0, 0), q))
    (hpoint :
      (fderiv ℂ plane ((0, 0), q) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × ℂ) E).IsInvertible)
    (hplaneZero : plane ((0, 0), q) = 0)
    (hthird : AnalyticAt ℂ third ((0, 0), q))
    (m : ℕ) (u : ℂ → ℂ) (hm : 0 < m)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hfactor : ∀ᶠ lambda in nhds 0,
      third ((0, lambda),
        analyticImplicitBranch plane ((0, 0), q) hplane hpoint (0, lambda)) =
          lambda ^ m * u lambda) :
    ∃ r > 0, ∀ᶠ tau in nhds 0,
      ∃ lambda ∈ closedBall (0 : ℂ) r,
        plane ((tau, lambda),
          analyticImplicitBranch plane ((0, 0), q) hplane hpoint
            (tau, lambda)) = 0 ∧
        third ((tau, lambda),
          analyticImplicitBranch plane ((0, 0), q) hplane hpoint
            (tau, lambda)) = 0 := by
  let branch := analyticImplicitBranch plane ((0, 0), q) hplane hpoint
  have hbranch : AnalyticAt ℂ branch (0, 0) := by
    exact analyticAt_analyticImplicitBranch plane ((0, 0), q) hplane hpoint
  let scalar : ℂ × ℂ → ℂ :=
    fun p ↦ third (p, branch p)
  have hscalar : AnalyticAt ℂ scalar (0, 0) := by
    have hlift : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ (p, branch p)) (0, 0) :=
      analyticAt_id.prod hbranch
    have hbranchBase : branch ((0, 0) : ℂ × ℂ) = q := by
      exact analyticImplicitBranch_apply_base
        plane ((0, 0), q) hplane hpoint
    have hliftBase :
        (((0, 0) : ℂ × ℂ), branch ((0, 0) : ℂ × ℂ)) =
          (((0, 0) : ℂ × ℂ), q) := by
      rw [hbranchBase]
    simpa [scalar, Function.comp_def] using
      hthird.comp_of_eq hlift hliftBase
  have hplaneBranch : ∀ᶠ p in nhds (0, 0), plane (p, branch p) = 0 := by
    filter_upwards
      [eventually_analyticImplicitBranch_eq
        plane ((0, 0), q) hplane hpoint] with p hp
    simpa [hplaneZero] using hp
  obtain ⟨R, hR, hplaneOnBall⟩ := Metric.mem_nhds_iff.mp hplaneBranch
  have hfactorScalar : ∀ᶠ lambda in nhds 0,
      scalar (0, lambda) = lambda ^ m * u lambda := by
    simpa [scalar, branch] using hfactor
  obtain ⟨r, hr, hrR, hscalarZero⟩ :=
    eventually_exists_zero_of_analyticAt_of_specialFiber_factorization_lt
      scalar m u hm hscalar hu hu0 hfactorScalar R hR
  have htau : ball (0 : ℂ) (R - r) ∈ nhds 0 :=
    Metric.ball_mem_nhds 0 (sub_pos.mpr hrR)
  refine ⟨r, hr, ?_⟩
  filter_upwards [hscalarZero, htau] with tau hzero htau'
  obtain ⟨lambda, hlambda, hthirdZero⟩ := hzero
  refine ⟨lambda, hlambda, ?_, ?_⟩
  · apply hplaneOnBall
    rw [mem_ball, Prod.dist_eq]
    have htauNorm : dist tau 0 < R - r := by
      simpa [mem_ball] using htau'
    have hlambdaNorm : dist lambda 0 ≤ r := by
      simpa [mem_closedBall] using hlambda
    exact max_lt (by linarith) (lt_of_le_of_lt hlambdaNorm hrR)
  · exact hthirdZero

end OnLeConjecture.Analytic
