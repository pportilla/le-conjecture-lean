/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HPoleCollision

/-!
# A transverse H chart with zero second source coordinate

When the second source point has zero second coordinate, its second
coordinate is used as the curve parameter.  The two first coordinates are
the variables eliminated by the implicit function theorem.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- The two plane differences with both first coordinates variable. -/
@[expose]
noncomputable def hZeroSecondPlaneDifference
    (a : ℕ) (T : ℂ → ℂ) (q : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![hP (q.2 0) 1 - hP (q.2 1) (T q.1 ^ (2 * a)),
    hQ (q.2 0) 1 - hQ (q.2 1) (T q.1 ^ (2 * a))]

/-- The derivative in the two first coordinates at a zero second
coordinate. -/
@[expose]
noncomputable def hZeroSecondPointJacobian
    (x X : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![3 * x ^ 2 + 3, -(3 * X ^ 2);
    4 * x ^ 3 + 8 * x, -(4 * X ^ 3)]

@[expose]
noncomputable def hZeroSecondPointDerivative
    (x X : ℂ) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLin' (hZeroSecondPointJacobian x X)).toContinuousLinearMap

theorem analyticAt_hZeroSecondPlaneDifference
    (a : ℕ) (T : ℂ → ℂ) (q : ℂ × (Fin 2 → ℂ))
    (hT : AnalyticAt ℂ T q.1) :
    AnalyticAt ℂ (hZeroSecondPlaneDifference a T) q := by
  have hparameter : AnalyticAt ℂ
      (fun q : ℂ × (Fin 2 → ℂ) ↦ T q.1) q :=
    hT.fun_comp analyticAt_fst
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
      hP (q.2 0) 1 - hP (q.2 1) (T q.1 ^ (2 * a))) q
    simp only [hP]
    exact (((hcoordinate 0).pow 3).add
      ((analyticAt_const.mul (hcoordinate 0)).mul analyticAt_const)).sub
        (((hcoordinate 1).pow 3).add
          ((analyticAt_const.mul (hcoordinate 1)).mul
            (hparameter.pow (2 * a))))
  · change AnalyticAt ℂ (fun q : ℂ × (Fin 2 → ℂ) ↦
      hQ (q.2 0) 1 - hQ (q.2 1) (T q.1 ^ (2 * a))) q
    simp only [hQ]
    exact ((((hcoordinate 0).pow 4).add
      ((analyticAt_const.mul ((hcoordinate 0).pow 2)).mul
        analyticAt_const)).add
          (analyticAt_const.mul (analyticAt_const.pow 2))).sub
      ((((hcoordinate 1).pow 4).add
        ((analyticAt_const.mul ((hcoordinate 1).pow 2)).mul
          (hparameter.pow (2 * a)))).add
            (analyticAt_const.mul
              ((hparameter.pow (2 * a)).pow 2)))

theorem hasStrictFDerivAt_hZeroSecondPlaneDifference_point
    (a : ℕ) (ha : 0 < a) (T : ℂ → ℂ) (x X : ℂ)
    (hT : T 0 = 0) :
    HasStrictFDerivAt
      (fun v ↦ hZeroSecondPlaneDifference a T (0, v))
      (hZeroSecondPointDerivative x X) ![x, X] := by
  have hfunction :
      (fun v ↦ hZeroSecondPlaneDifference a T (0, v)) =
        fun v ↦ ![hP (v 0) 1 - hP (v 1) 0,
          hQ (v 0) 1 - hQ (v 1) 0] := by
    funext v
    simp [hZeroSecondPlaneDifference, hT, zero_pow (by omega : 2 * a ≠ 0)]
  rw [hfunction]
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  · have hx := hasStrictFDerivAt_apply
      (𝕜 := ℂ) (0 : Fin 2) ![x, X]
    have hX := hasStrictFDerivAt_apply
      (𝕜 := ℂ) (1 : Fin 2) ![x, X]
    convert ((hx.pow 3).add (hx.const_mul (3 : ℂ))).sub (hX.pow 3) using 1
    · funext v
      simp [hP]
    · ext v
      simp [hZeroSecondPointDerivative, hZeroSecondPointJacobian,
        Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
      ring
  · have hx := hasStrictFDerivAt_apply
      (𝕜 := ℂ) (0 : Fin 2) ![x, X]
    have hX := hasStrictFDerivAt_apply
      (𝕜 := ℂ) (1 : Fin 2) ![x, X]
    have htwo := hasStrictFDerivAt_const
      (𝕜 := ℂ) (2 : ℂ) ![x, X]
    convert (((hx.pow 4).add ((hx.pow 2).const_mul (4 : ℂ))).add
      htwo).sub (hX.pow 4) using 1
    · funext v
      simp [hQ]
    · ext v
      simp [hZeroSecondPointDerivative, hZeroSecondPointJacobian,
        Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
      ring

theorem det_hZeroSecondPointJacobian (x X : ℂ) :
    Matrix.det (hZeroSecondPointJacobian x X) =
      12 * X ^ 2 * (x ^ 3 + 2 * x - X * x ^ 2 - X) := by
  simp [hZeroSecondPointJacobian, Matrix.det_fin_two]
  ring

theorem det_hZeroSecondPointDerivative (x X : ℂ) :
    (hZeroSecondPointDerivative x X).det =
      12 * X ^ 2 * (x ^ 3 + 2 * x - X * x ^ 2 - X) := by
  calc
    (hZeroSecondPointDerivative x X).det =
        Matrix.det (hZeroSecondPointJacobian x X) := by
      simp [hZeroSecondPointDerivative,
        LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin']
    _ = _ := det_hZeroSecondPointJacobian x X

theorem h_zero_second_transverse
    (x X : ℂ)
    (hPfiber : hP x 1 = hP X 0)
    (hQfiber : hQ x 1 = hQ X 0) :
    X ≠ 0 ∧ x ^ 3 + 2 * x - X * x ^ 2 - X ≠ 0 := by
  have hp : x ^ 3 + 3 * x - X ^ 3 = 0 := by
    simpa [hP] using sub_eq_zero.mpr hPfiber
  have hq : x ^ 4 + 4 * x ^ 2 + 2 - X ^ 4 = 0 := by
    simpa [hQ] using sub_eq_zero.mpr hQfiber
  constructor
  · intro hX
    have hp' : x ^ 3 + 3 * x = 0 := by simpa [hX] using hp
    have hq' : x ^ 4 + 4 * x ^ 2 + 2 = 0 := by simpa [hX] using hq
    have hquadratic : x ^ 2 + 2 = 0 := by
      linear_combination hq' - x * hp'
    have hx : x = 0 := by
      linear_combination hp' - x * hquadratic
    rw [hx] at hquadratic
    norm_num at hquadratic
  · intro hinner
    have hfalse : (1 : ℂ) = 0 := by
      linear_combination
        (-x * (x ^ 2 + 2) / 2) * hp +
        ((x ^ 2 + 1) / 2) * hq -
        (X ^ 3 / 2) * hinner
    norm_num at hfalse

/-- The point derivative in the zero second coordinate chart is invertible
at every fibre point of this form. -/
@[expose]
noncomputable def hZeroSecondPointDerivativeEquiv
    (x X : ℂ)
    (hPfiber : hP x 1 = hP X 0)
    (hQfiber : hQ x 1 = hQ X 0) :
    (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (hZeroSecondPointDerivative x X).toContinuousLinearEquivOfDetNeZero <| by
    rw [det_hZeroSecondPointDerivative]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num)
        (pow_ne_zero 2 (h_zero_second_transverse x X hPfiber hQfiber).1))
      (h_zero_second_transverse x X hPfiber hQfiber).2

end OnLeConjecture.DThree
