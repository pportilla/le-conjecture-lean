/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HQuadraticWeightedPolynomialMap
public import OnLeConjecture.Analytic.MultipleZeroElimination
public import Mathlib.Tactic.FinCases

/-!
# A transverse affine chart for H fibre collisions

The first source point is written as `(x(lambda), 1)`.  The second point is
the pair of variables eliminated by the analytic implicit function theorem.
The determinant of the point derivative is nonzero whenever the second
coordinate of the second point is nonzero.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DThree

/-- The first two fibre differences with first point `(x(lambda), 1)`. -/
@[expose]
noncomputable def hCollisionPlaneDifference
    (a : ℕ) (x : ℂ → ℂ) (q : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![hP (x q.1) 1 - hP (q.2 0) (q.2 1 ^ (2 * a)),
    hQ (x q.1) 1 - hQ (q.2 0) (q.2 1 ^ (2 * a))]

/-- The Jacobian in the second point variables. -/
@[expose]
noncomputable def hCollisionPointJacobian
    (a : ℕ) (X T : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-(3 * X ^ 2 + 3 * T ^ (2 * a)),
      -(3 * X * (2 * a) * T ^ (2 * a - 1));
    -(4 * X ^ 3 + 8 * X * T ^ (2 * a)),
      -(4 * X ^ 2 * (2 * a) * T ^ (2 * a - 1) +
        2 * (4 * a) * T ^ (4 * a - 1))]

/-- The continuous linear map represented by the point Jacobian. -/
@[expose]
noncomputable def hCollisionPointDerivative
    (a : ℕ) (X T : ℂ) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLin' (hCollisionPointJacobian a X T)).toContinuousLinearMap

theorem analyticAt_hCollisionPlaneDifference
    (a : ℕ) (x : ℂ → ℂ) (q : ℂ × (Fin 2 → ℂ))
    (hx : AnalyticAt ℂ x q.1) :
    AnalyticAt ℂ (hCollisionPlaneDifference a x) q := by
  have hlambda : AnalyticAt ℂ
      (fun q : ℂ × (Fin 2 → ℂ) ↦ x q.1) q :=
    hx.fun_comp analyticAt_fst
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
      hP (x q.1) 1 - hP (q.2 0) (q.2 1 ^ (2 * a))) q
    simp only [hP]
    exact ((hlambda.pow 3).add
      ((analyticAt_const.mul hlambda).mul analyticAt_const)).sub
        (((hcoordinate 0).pow 3).add
          ((analyticAt_const.mul (hcoordinate 0)).mul
            ((hcoordinate 1).pow (2 * a))))
  · change AnalyticAt ℂ (fun q : ℂ × (Fin 2 → ℂ) ↦
      hQ (x q.1) 1 - hQ (q.2 0) (q.2 1 ^ (2 * a))) q
    simp only [hQ]
    exact (((hlambda.pow 4).add
      ((analyticAt_const.mul (hlambda.pow 2)).mul analyticAt_const)).add
        (analyticAt_const.mul (analyticAt_const.pow 2))).sub
          ((((hcoordinate 0).pow 4).add
            ((analyticAt_const.mul ((hcoordinate 0).pow 2)).mul
              ((hcoordinate 1).pow (2 * a)))).add
                (analyticAt_const.mul
                  (((hcoordinate 1).pow (2 * a)).pow 2)))

theorem hasStrictFDerivAt_hCollisionPlaneDifference_point
    (a : ℕ) (x : ℂ → ℂ) (X T : ℂ) :
    HasStrictFDerivAt
      (fun v ↦ hCollisionPlaneDifference a x (0, v))
      (hCollisionPointDerivative a X T) ![X, T] := by
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  all_goals simp only [hCollisionPlaneDifference]
  · convert
      ((hasStrictFDerivAt_const (𝕜 := ℂ)
          (hP (x 0) 1) ![X, T]).sub
        ((((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![X, T]).pow 3).add
          (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![X, T]).mul
            ((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![X, T]).pow
              (2 * a))).const_mul (3 : ℂ)))))
      using 1
    all_goals ext v
    all_goals simp [hCollisionPointDerivative, hCollisionPointJacobian,
      hP, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
    all_goals ring
  · convert
      ((hasStrictFDerivAt_const (𝕜 := ℂ)
          (hQ (x 0) 1) ![X, T]).sub
        (((((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![X, T]).pow 4).add
          ((((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![X, T]).pow 2).mul
            ((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![X, T]).pow
              (2 * a))).const_mul (4 : ℂ))).add
          (((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![X, T]).pow
            (4 * a)).const_mul (2 : ℂ)))))
      using 1
    all_goals ext v
    all_goals simp [hCollisionPointDerivative, hCollisionPointJacobian,
      hQ, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
    all_goals ring

theorem det_hCollisionPointJacobian
    (a : ℕ) (ha : 0 < a) (X T : ℂ) :
    Matrix.det (hCollisionPointJacobian a X T) =
      24 * a * T ^ (6 * a - 1) := by
  simp [hCollisionPointJacobian, Matrix.det_fin_two]
  ring_nf
  have hpole : T ^ (a * 2) * T ^ (a * 4 - 1) =
      T ^ (a * 6 - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hcancel : T ^ (a * 2) * T ^ (a * 2 - 1) =
      T ^ (a * 4 - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpole, hcancel]
  ring

theorem det_hCollisionPointDerivative
    (a : ℕ) (ha : 0 < a) (X T : ℂ) :
    (hCollisionPointDerivative a X T).det =
      24 * a * T ^ (6 * a - 1) := by
  calc
    (hCollisionPointDerivative a X T).det =
        Matrix.det (hCollisionPointJacobian a X T) := by
      simp [hCollisionPointDerivative,
        LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin']
    _ = 24 * a * T ^ (6 * a - 1) :=
      det_hCollisionPointJacobian a ha X T

/-- The derivative in the second point variables is invertible when its
second coordinate is nonzero. -/
@[expose]
noncomputable def hCollisionPointDerivativeEquiv
    (a : ℕ) (ha : 0 < a) (X T : ℂ) (hT : T ≠ 0) :
    (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (hCollisionPointDerivative a X T).toContinuousLinearEquivOfDetNeZero <| by
    rw [det_hCollisionPointDerivative a ha X T]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr ha.ne'))
      (pow_ne_zero _ hT)

theorem hCollisionPlaneDifference_base_eq_zero
    (a : ℕ) (x : ℂ → ℂ) (X T : ℂ)
    (hPfiber : hP (x 0) 1 = hP X (T ^ (2 * a)))
    (hQfiber : hQ (x 0) 1 = hQ X (T ^ (2 * a))) :
    hCollisionPlaneDifference a x (0, ![X, T]) = 0 := by
  funext i
  fin_cases i
  · simpa [hCollisionPlaneDifference] using sub_eq_zero.mpr hPfiber
  · simpa [hCollisionPlaneDifference] using sub_eq_zero.mpr hQfiber

end OnLeConjecture.DThree
