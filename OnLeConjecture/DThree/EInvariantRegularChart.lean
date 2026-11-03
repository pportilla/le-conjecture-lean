/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EInvariantCollision
public import OnLeConjecture.DThree.ResidueRotationTransversality

/-!
# A regular affine chart for invariant E collisions

When both residual cube coordinates are nonzero, the residual direction can
be represented by two points `(s z, 1)` and `(s, g)`.  The first two fibre
equations are transverse in `s` and `g`.  This file records the chart and its
invertible point derivative.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DThree

/-- The first two fibre differences in the residual direction chart. -/
@[expose]
noncomputable def eInvariantPlaneDifference
    (z : ℂ) (q : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![q.2 0 ^ 3 * ((z + q.1) ^ 3 - 1) + 3 * (1 - q.2 1 ^ 3),
    q.2 0 ^ 4 * ((z + q.1) ^ 4 - 1) +
      4 * q.2 0 * (z + q.1 - q.2 1 ^ 3)]

/-- The point Jacobian in the two variables `s` and `g`. -/
@[expose]
noncomputable def eInvariantPlanePointJacobian
    (z s g : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![3 * s ^ 2 * (z ^ 3 - 1), -9 * g ^ 2;
    4 * s ^ 3 * (z ^ 4 - 1) + 4 * (z - g ^ 3),
      -12 * s * g ^ 2]

/-- The continuous linear map represented by the point Jacobian. -/
@[expose]
noncomputable def eInvariantPlanePointDerivative
    (z s g : ℂ) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLin' (eInvariantPlanePointJacobian z s g)).toContinuousLinearMap

theorem analyticAt_eInvariantPlaneDifference
    (z : ℂ) (q : ℂ × (Fin 2 → ℂ)) :
    AnalyticAt ℂ (eInvariantPlaneDifference z) q := by
  have hlambda : AnalyticAt ℂ
      (fun q : ℂ × (Fin 2 → ℂ) ↦ q.1) q := analyticAt_fst
  have hcoordinate (i : Fin 2) : AnalyticAt ℂ
      (fun q : ℂ × (Fin 2 → ℂ) ↦ q.2 i) q := by
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt q.2).comp
        (analyticAt_snd : AnalyticAt ℂ
          (fun q : ℂ × (Fin 2 → ℂ) ↦ q.2) q)
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · change AnalyticAt ℂ (fun q : ℂ × (Fin 2 → ℂ) ↦
      q.2 0 ^ 3 * ((z + q.1) ^ 3 - 1) +
        3 * (1 - q.2 1 ^ 3)) q
    fun_prop (disch := assumption)
  · change AnalyticAt ℂ (fun q : ℂ × (Fin 2 → ℂ) ↦
      q.2 0 ^ 4 * ((z + q.1) ^ 4 - 1) +
        4 * q.2 0 * (z + q.1 - q.2 1 ^ 3)) q
    fun_prop (disch := assumption)

theorem hasStrictFDerivAt_eInvariantPlaneDifference_point
    (z s g : ℂ) :
    HasStrictFDerivAt (fun v ↦ eInvariantPlaneDifference z (0, v))
      (eInvariantPlanePointDerivative z s g) ![s, g] := by
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  all_goals simp only [eInvariantPlaneDifference]
  · convert
      ((((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![s, g]).pow 3)
        |>.mul (hasStrictFDerivAt_const (𝕜 := ℂ) (z ^ 3 - 1) ![s, g]))
        |>.add
          ((hasStrictFDerivAt_const (𝕜 := ℂ) 1 ![s, g]).sub
            ((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![s, g]).pow 3)
            |>.const_mul (3 : ℂ)))
      using 1
    all_goals ext v
    all_goals simp [eInvariantPlanePointDerivative,
      eInvariantPlanePointJacobian, Matrix.toLin'_apply, dotProduct,
      Fin.sum_univ_succ]
    all_goals ring
  · convert
      ((((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![s, g]).pow 4)
        |>.mul (hasStrictFDerivAt_const (𝕜 := ℂ) (z ^ 4 - 1) ![s, g]))
        |>.add
          (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![s, g]).mul
            ((hasStrictFDerivAt_const (𝕜 := ℂ) z ![s, g]).sub
              ((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![s, g]).pow 3)))
            |>.const_mul (4 : ℂ)))
      using 1
    all_goals ext v
    all_goals simp [eInvariantPlanePointDerivative,
      eInvariantPlanePointJacobian, Matrix.toLin'_apply, dotProduct,
      Fin.sum_univ_succ]
    all_goals ring

theorem det_eInvariantPlanePointJacobian (z s g : ℂ) :
    Matrix.det (eInvariantPlanePointJacobian z s g) =
      36 * g ^ 2 *
        (-g ^ 3 + s ^ 3 * z ^ 4 - s ^ 3 * z ^ 3 + z) := by
  simp [eInvariantPlanePointJacobian, Matrix.det_fin_two]
  ring

theorem eInvariant_regular_determinant_identity
    (z s g : ℂ)
    (hs : s ^ 3 * eResidualW z 1 = 1)
    (hg : g ^ 3 = s ^ 3 * eResidualW 1 z) :
    -g ^ 3 + s ^ 3 * z ^ 4 - s ^ 3 * z ^ 3 + z =
      -3 * (z - 1) := by
  simp only [eResidualW] at hs hg
  field_simp at hs hg ⊢
  linear_combination
    (-1 / 12 : ℂ) * hg + ((3 - 4 * z) / 12) * hs

theorem det_eInvariantPlanePointDerivative
    (z s g : ℂ)
    (hs : s ^ 3 * eResidualW z 1 = 1)
    (hg : g ^ 3 = s ^ 3 * eResidualW 1 z) :
    (eInvariantPlanePointDerivative z s g).det =
      -108 * g ^ 2 * (z - 1) := by
  calc
    (eInvariantPlanePointDerivative z s g).det =
        Matrix.det (eInvariantPlanePointJacobian z s g) := by
      simp [eInvariantPlanePointDerivative,
        LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin']
    _ = 36 * g ^ 2 *
        (-g ^ 3 + s ^ 3 * z ^ 4 - s ^ 3 * z ^ 3 + z) :=
      det_eInvariantPlanePointJacobian z s g
    _ = -108 * g ^ 2 * (z - 1) := by
      rw [eInvariant_regular_determinant_identity z s g hs hg]
      ring

theorem eInvariantPlaneDifference_base_eq_zero
    (z s g : ℂ)
    (hs : s ^ 3 * eResidualW z 1 = 1)
    (hg : g ^ 3 = s ^ 3 * eResidualW 1 z) :
    eInvariantPlaneDifference z (0, ![s, g]) = 0 := by
  funext i
  fin_cases i
  · have hzero : s ^ 3 * (z ^ 3 - 1) + 3 * (1 - g ^ 3) = 0 := by
      simp only [eResidualW] at hs hg
      field_simp at hs hg
      linear_combination
        (-1 / 4 : ℂ) * hs + (-1 / 4 : ℂ) * hg
    simpa [eInvariantPlaneDifference] using hzero
  · have hzero :
        s ^ 4 * (z ^ 4 - 1) + 4 * s * (z - g ^ 3) = 0 := by
      simp only [eResidualW] at hs hg
      field_simp at hs hg
      linear_combination
        (-s * z / 3 : ℂ) * hs + (-s / 3 : ℂ) * hg
    simpa [eInvariantPlaneDifference] using hzero

theorem eInvariant_chart_s_ne_zero
    {z s : ℂ} (hs : s ^ 3 * eResidualW z 1 = 1) : s ≠ 0 := by
  intro hsZero
  rw [hsZero, zero_pow (by norm_num : 3 ≠ 0), zero_mul] at hs
  exact zero_ne_one hs

theorem eInvariant_chart_g_ne_zero
    {z s g : ℂ}
    (hs : s ^ 3 * eResidualW z 1 = 1)
    (hg : g ^ 3 = s ^ 3 * eResidualW 1 z)
    (hW : eResidualW 1 z ≠ 0) : g ≠ 0 := by
  have hsNe := eInvariant_chart_s_ne_zero hs
  have hright : s ^ 3 * eResidualW 1 z ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 hsNe) hW
  exact fun hgZero ↦ hright <| by rw [← hg, hgZero, zero_pow (by norm_num)]

/-- The point derivative is invertible in every regular residual chart. -/
@[expose]
noncomputable def eInvariantPlanePointDerivativeEquiv
    (z s g : ℂ)
    (hs : s ^ 3 * eResidualW z 1 = 1)
    (hg : g ^ 3 = s ^ 3 * eResidualW 1 z)
    (hW : eResidualW 1 z ≠ 0)
    (hz : z ≠ 1) :
    (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (eInvariantPlanePointDerivative z s g).toContinuousLinearEquivOfDetNeZero <| by
    rw [det_eInvariantPlanePointDerivative z s g hs hg]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num)
        (pow_ne_zero 2 (eInvariant_chart_g_ne_zero hs hg hW)))
      (sub_ne_zero.mpr hz)

/-- A regular residual direction determines normalized cube coordinates. -/
theorem exists_eInvariantRegularChartCoordinates
    (z : ℂ) (hw : eResidualW z 1 ≠ 0) :
    ∃ s g : ℂ,
      s ^ 3 * eResidualW z 1 = 1 ∧
      g ^ 3 = s ^ 3 * eResidualW 1 z := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq
    (eResidualW z 1)⁻¹ (by norm_num : 0 < 3)
  have hsNormalized : s ^ 3 * eResidualW z 1 = 1 := by
    rw [hs]
    exact inv_mul_cancel₀ hw
  obtain ⟨g, hg⟩ := IsAlgClosed.exists_pow_nat_eq
    (s ^ 3 * eResidualW 1 z) (by norm_num : 0 < 3)
  exact ⟨s, g, hsNormalized, hg⟩

end OnLeConjecture.DThree
