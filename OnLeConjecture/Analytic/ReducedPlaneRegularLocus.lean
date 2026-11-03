/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ReducedPlaneIsolatedCritical
public import OnLeConjecture.Analytic.CriticalDivisorZeroSet
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# The punctured regular locus of a reduced plane equation

Finite dimension of the Jacobian algebra implies that the two actual
partial derivatives have no common zero near the origin except possibly
the origin. A nonzero complex linear functional is surjective, including
when regarded as a real linear map.
-/

public noncomputable section

open Filter Set
open scoped Topology

namespace OnLeConjecture.Analytic.Germ

/-- The differential of a reduced pointed plane equation is nonzero
throughout a sufficiently small punctured neighborhood. -/
theorem eventually_fderiv_ne_zero_of_squarefree
    (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (hsq : Squarefree (ofFunction H hH)) :
    ∀ᶠ z in 𝓝 (0 : Source 2), z ≠ 0 → fderiv ℂ H z ≠ 0 := by
  let P : Fin 2 → Source 2 → ℂ := fun i z => fderiv ℂ H z (coordinateVector i)
  have hP (i : Fin 2) : AnalyticAt ℂ (P i) 0 :=
    ((ContinuousLinearMap.apply ℂ ℂ (coordinateVector i)).analyticAt _).comp hH.fderiv
  have hI : Ideal.span (Set.range (fun i => ofFunction (P i) (hP i))) =
      PlaneCurve.jacobianIdeal (ofFunction H hH) := by
    congr 1
    ext f
    simp only [Set.mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [P, partialDerivative, directionalDerivative_ofFunction]
    · intro hf
      rcases hf with (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hfinite : Module.Finite ℂ
      (Germ 2 ⧸ Ideal.span (Set.range (fun i => ofFunction (P i) (hP i)))) := by
    rw [hI]
    exact PlaneCurve.hasFiniteJacobianAlgebra_of_squarefree _
      (mem_maximalIdeal_iff.mpr hH0) hsq
  filter_upwards [eventually_common_zero_imp_eq_zero_of_finite_colength P hP hfinite]
    with z hz hzne hzero
  apply hzne
  apply hz
  intro i
  simp [P, hzero]

/-- The actual complex differential is surjective away from the origin. -/
theorem eventually_fderiv_surjective_of_squarefree
    (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (hsq : Squarefree (ofFunction H hH)) :
    ∀ᶠ z in 𝓝 (0 : Source 2), z ≠ 0 → Function.Surjective (fderiv ℂ H z) := by
  filter_upwards [eventually_fderiv_ne_zero_of_squarefree H hH hH0 hsq] with z hz hzne
  have hv : ∃ v, fderiv ℂ H z v ≠ 0 := by
    by_contra! h
    exact hz hzne (ContinuousLinearMap.ext h)
  obtain ⟨v, hv⟩ := hv
  intro a
  refine ⟨(a / fderiv ℂ H z v) • v, ?_⟩
  simp only [map_smul, smul_eq_mul]
  exact div_mul_cancel₀ _ hv

/-- The complex-valued equation is also a real submersion on the punctured
neighborhood, with real target dimension two. -/
theorem eventually_real_fderiv_surjective_of_squarefree
    (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (hsq : Squarefree (ofFunction H hH)) :
    ∀ᶠ z in 𝓝 (0 : Source 2), z ≠ 0 → Function.Surjective (fderiv ℝ H z) := by
  filter_upwards [eventually_fderiv_surjective_of_squarefree H hH hH0 hsq,
    hH.eventually_analyticAt] with z hz ha hzne
  rw [ha.differentiableAt.fderiv_restrictScalars ℝ]
  exact hz hzne

end OnLeConjecture.Analytic.Germ
