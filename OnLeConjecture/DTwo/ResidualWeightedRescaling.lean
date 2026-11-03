/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ResidueRotationMultiplePersistence
public import OnLeConjecture.DTwo.ResidualTransversality
public import Mathlib.Analysis.Analytic.Polynomial

/-!
# Weighted rescaling of the residual collision

This file connects the source weights `(L, 2)` to the common affine
difference and perturbation constructions.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open OnLeConjecture.DThree

/-- A local radial expansion certificate for source weights `(L, 2)`. -/
structure HasResidualWeightedRadialExpansionAt
    (L : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (z : ℂ × ℂ) : Prop where
  remainder_analyticAt : AnalyticAt ℂ remainder (0, z)
  expansion :
    ∀ᶠ s in nhds (0, z), ∀ i,
      representative (residualWeightedRadialSource L s.1 s.2) i =
        s.1 ^ degrees i *
          (initialMap s.2 i + s.1 * remainder s i)

theorem analyticAt_residualWeightedInitialMap
    (k L N : ℕ) (c T : ℂ) (Psi : PreparedOddFamily N)
    (model : Psi.BivariateModel) (z : ℂ × ℂ) :
    AnalyticAt ℂ (residualWeightedInitialMap k L N c T Psi) z := by
  have hx : AnalyticAt ℂ (fun z : ℂ × ℂ ↦ z.1) z := analyticAt_fst
  have hy : AnalyticAt ℂ (fun z : ℂ × ℂ ↦ z.2) z := analyticAt_snd
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · change AnalyticAt ℂ (fun z : ℂ × ℂ ↦ z.2 ^ k) z
    exact hy.pow k
  · change AnalyticAt ℂ (fun z : ℂ × ℂ ↦
      -c * (z.1 ^ 2 + T * z.2 ^ L)) z
    fun_prop (disch := assumption)
  · have hcoordinates : ∀ j : Fin 2, AnalyticAt ℂ
        (fun z : ℂ × ℂ ↦ ![z.1, T * z.2 ^ L] j) z := by
      intro j
      fin_cases j
      · exact hx
      · exact analyticAt_const.mul (hy.pow L)
    have heval : AnalyticAt ℂ
        (fun z : ℂ × ℂ ↦
          MvPolynomial.eval ![z.1, T * z.2 ^ L] model.polynomial) z := by
      simpa [MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq] using
        AnalyticAt.aeval_mvPolynomial hcoordinates model.polynomial
    have heq :
        (fun z : ℂ × ℂ ↦
          (Psi.polynomial (T * z.2 ^ L)).eval z.1) =
        fun z : ℂ × ℂ ↦
          MvPolynomial.eval ![z.1, T * z.2 ^ L] model.polynomial := by
      funext z
      rw [model.specialization, parameterSpecialization_eval]
    change AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦
        (Psi.polynomial (T * z.2 ^ L)).eval z.1) z
    rw [heq]
    exact heval

theorem analyticAt_weightedInitialDifference_residualWeightedInitialMap
    (k L N : ℕ) (c T : ℂ) (Psi : PreparedOddFamily N)
    (model : Psi.BivariateModel) (q : Fin 3 → ℂ) :
    AnalyticAt ℂ
      (weightedInitialDifference
        (residualWeightedInitialMap k L N c T Psi)) q := by
  change AnalyticAt ℂ
    ((fun q ↦ residualWeightedInitialMap k L N c T Psi
        (residueFirstChartPoint q)) -
      fun q ↦ residualWeightedInitialMap k L N c T Psi
        (residueSecondChartPoint q)) q
  exact
    (analyticAt_residualWeightedInitialMap k L N c T Psi model
      (residueFirstChartPoint q)).fun_comp
        (analyticAt_residueFirstChartPoint q) |>.sub
      ((analyticAt_residualWeightedInitialMap k L N c T Psi model
        (residueSecondChartPoint q)).fun_comp
          (analyticAt_residueSecondChartPoint q))

theorem residualRotationPlanePart_weightedRescaledPerturbation_zero
    (k L N : ℕ) (c T : ℂ) (Psi : PreparedOddFamily N)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x lambda : ℂ) (v : Fin 2 → ℂ) :
    rotationPlanePart
        (weightedRescaledPerturbation
          (residualWeightedInitialMap k L N c T Psi) remainder)
        x ((0, lambda), v) =
      residualRotationPlaneDifference k L c T x (lambda, v) := by
  funext i
  fin_cases i
  · simp [rotationPlanePart, rotationReparametrization, rotationAffinePoint,
      weightedRescaledPerturbation_zero, weightedInitialDifference,
      residueFirstChartPoint, residueSecondChartPoint,
      residualWeightedInitialMap, residualRotationPlaneDifference]
  · simp [rotationPlanePart, rotationReparametrization, rotationAffinePoint,
      weightedRescaledPerturbation_zero, weightedInitialDifference,
      residueFirstChartPoint, residueSecondChartPoint,
      residualWeightedInitialMap, residualRotationPlaneDifference]
    ring

theorem residualRotationThirdPart_weightedRescaledPerturbation_zero
    (k L N : ℕ) (c T : ℂ) (Psi : PreparedOddFamily N)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x lambda : ℂ) (v : Fin 2 → ℂ) :
    rotationThirdPart
        (weightedRescaledPerturbation
          (residualWeightedInitialMap k L N c T Psi) remainder)
        x ((0, lambda), v) =
      residualRotationThirdDifference L T x Psi (lambda, v) := by
  simp [rotationThirdPart, rotationReparametrization, rotationAffinePoint,
    weightedRescaledPerturbation_zero, weightedInitialDifference,
    residueFirstChartPoint, residueSecondChartPoint,
    residualWeightedInitialMap, residualRotationThirdDifference]

/-- Weighted source substitution tends to the origin when `L` is
positive. -/
theorem tendsto_residualWeightedRadialSource_zero
    (L : ℕ) (hL : 0 < L) (z : ℂ × ℂ) :
    Tendsto (fun lambda : ℂ ↦ residualWeightedRadialSource L lambda z)
      (nhds 0) (nhds 0) := by
  have hx : Tendsto (fun lambda : ℂ ↦ lambda ^ L * z.1)
      (nhds 0) (nhds 0) := by
    simpa [zero_pow hL.ne'] using
      ((tendsto_id.pow L).mul (tendsto_const_nhds :
        Tendsto (fun _ : ℂ ↦ z.1) (nhds 0) (nhds z.1)))
  have hy : Tendsto (fun lambda : ℂ ↦ lambda ^ 2 * z.2)
      (nhds 0) (nhds 0) := by
    simpa using
      ((tendsto_id.pow 2).mul (tendsto_const_nhds :
        Tendsto (fun _ : ℂ ↦ z.2) (nhds 0) (nhds z.2)))
  change Tendsto (fun lambda : ℂ ↦
    (lambda ^ L * z.1, lambda ^ 2 * z.2)) (nhds 0) (nhds (0, 0))
  exact hx.prodMk_nhds hy

end OnLeConjecture.DTwo
