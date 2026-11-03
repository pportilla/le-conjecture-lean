/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.QuadraticCrossingSpecialization
public import OnLeConjecture.Analytic.PolynomialCommonZeroPersistence

/-!
# Persistence for a prepared analytic quadratic pair

The polynomial resultant is formed from convergent analytic coefficient
functions. Its common roots are returned in the original coordinate order
`(Y,tau,x)`.
-/

public section

open Filter Set Polynomial
open scoped Topology

namespace OnLeConjecture.Analytic.QuadraticCrossing

@[expose] def rootPoint (z : (ℂ × ℂ) × ℂ) : Source 3 := ![z.2, z.1.1, z.1.2]

theorem rootPoint_analyticAt : AnalyticAt ℂ rootPoint ((0, 0), 0) := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact analyticAt_snd
  · exact analyticAt_fst.comp analyticAt_fst
  · exact analyticAt_snd.comp analyticAt_fst

/-- A prepared quadratic pair with nonzero special branch restrictions
has common zeros near the origin for every sufficiently small parameter. -/
theorem eventually_exists_prepared_zero_mem_nhds
    (H A B : ℂ × ℂ → ℂ)
    (hH : AnalyticAt ℂ H (0, 0)) (hA : AnalyticAt ℂ A (0, 0))
    (hB : AnalyticAt ℂ B (0, 0)) (hAzero : A (0, 0) = 0)
    (hspecial : ∀ᶠ x in nhds 0, H (0, x) = -(x ^ 2))
    (hplus : ¬ ∀ᶠ x in nhds 0, A (0, x) + x * B (0, x) = 0)
    (hminus : ¬ ∀ᶠ x in nhds 0, A (0, x) - x * B (0, x) = 0)
    (U : Set (Source 3)) (hU : U ∈ nhds 0) :
    ∀ᶠ tau in nhds 0, ∃ z : Source 3, z ∈ U ∧ z 1 = tau ∧
      z 0 ^ 2 + H (tau, z 2) = 0 ∧ A (tau, z 2) + z 0 * B (tau, z 2) = 0 := by
  let P : ℂ × ℂ → Polynomial ℂ := fun z ↦ X ^ 2 + C (H z)
  let Q : ℂ × ℂ → Polynomial ℂ := fun z ↦ C (A z) + C (B z) * X
  have hP (n : ℕ) : AnalyticAt ℂ (fun z ↦ (P z).coeff n) (0, 0) := by
    simp only [P, coeff_add, coeff_X_pow, coeff_C]
    apply analyticAt_const.add
    split_ifs
    · exact hH
    · exact analyticAt_const
  have hQ (n : ℕ) : AnalyticAt ℂ (fun z ↦ (Q z).coeff n) (0, 0) := by
    simp only [Q, coeff_add, coeff_C, coeff_C_mul, coeff_X]
    apply AnalyticAt.add
    · split_ifs
      · exact hA
      · exact analyticAt_const
    · exact hB.mul analyticAt_const
  have hmonic (z : ℂ × ℂ) : (P z).Monic := monic_X_pow_add_C _ (by decide)
  have hdegree (z : ℂ × ℂ) : (P z).natDegree = 2 := natDegree_X_pow_add_C
  have hQdegree (z : ℂ × ℂ) : (Q z).natDegree ≤ 1 := by
    exact (natDegree_add_le _ _).trans (max_le (by simp) (by
      simpa only [natDegree_X] using natDegree_C_mul_le (B z) (X : Polynomial ℂ)))
  have hzero : (Q (0, 0)).IsRoot 0 := by simp [Q, IsRoot.def, hAzero]
  have hPspecial : ∀ᶠ x in nhds 0, P (0, x) = X ^ 2 - C (x ^ 2) := by
    filter_upwards [hspecial] with x hx
    simp [P, hx, sub_eq_add_neg]
  have hplusQ : ¬ ∀ᶠ x in nhds 0, (Q (0, x)).eval x = 0 := by
    simpa only [Q, eval_add, eval_C, eval_mul, eval_X, mul_comm] using hplus
  have hminusQ : ¬ ∀ᶠ x in nhds 0, (Q (0, x)).eval (-x) = 0 := by
    have heq (x : ℂ) : (Q (0, x)).eval (-x) = A (0, x) - x * B (0, x) := by
      simp only [Q, eval_add, eval_C, eval_mul, eval_X]
      ring
    simp only [heq]
    exact hminus
  have hpreimage : rootPoint ⁻¹' U ∈ nhds ((0, 0), 0) := by
    have ht := rootPoint_analyticAt.continuousAt.tendsto
    have hzeroPoint : rootPoint ((0, 0), 0) = 0 := by ext i; fin_cases i <;> rfl
    rw [hzeroPoint] at ht
    exact ht.eventually hU
  have hpersist := eventually_exists_common_root_mem_nhds_of_quadratic_branches P Q 1
    hP hQ hmonic hdegree hQdegree hPspecial hzero hplusQ hminusQ (rootPoint ⁻¹' U) hpreimage
  filter_upwards [hpersist] with tau htau
  obtain ⟨x, y, hmem, hPy, hQy⟩ := htau
  refine ⟨rootPoint ((tau, x), y), hmem, rfl, ?_, ?_⟩
  · change y ^ 2 + H (tau, x) = 0
    simpa only [P, IsRoot.def, eval_add, eval_pow, eval_X, eval_C] using hPy
  · change A (tau, x) + y * B (tau, x) = 0
    have hq : A (tau, x) + B (tau, x) * y = 0 := by
      simpa only [Q, IsRoot.def, eval_add, eval_mul, eval_C, eval_X] using hQy
    rwa [mul_comm] at hq

end OnLeConjecture.Analytic.QuadraticCrossing
