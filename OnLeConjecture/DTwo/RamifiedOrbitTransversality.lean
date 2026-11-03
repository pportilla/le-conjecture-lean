/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitTransversality
public import OnLeConjecture.DTwo.ExtremeThetaDecomposition

/-!
# The derivative of the ramified orbit plane map

The map `(x,y) ↦ (x²+y^(2a),2x³+3xy^(2a))` has determinant
`-6a y^(4a-1)`. Thus any point with nonzero second coordinate supplies
the invertible derivative needed to eliminate that point in a collision.
-/

public section

namespace OnLeConjecture.DTwo

/-- The actual polynomial plane map in the extreme quadratic case. -/
@[expose] def ramifiedOrbitPlaneMap (a : ℕ) (q : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![q 0 ^ 2 + q 1 ^ (2 * a), 2 * q 0 ^ 3 + 3 * q 0 * q 1 ^ (2 * a)]

@[expose] noncomputable def ramifiedOrbitPointJacobian
    (a : ℕ) (x y : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![2 * x, 2 * (a : ℂ) * y ^ (2 * a - 1);
    6 * x ^ 2 + 3 * y ^ (2 * a), 6 * (a : ℂ) * x * y ^ (2 * a - 1)]

@[expose] noncomputable def ramifiedOrbitPointDerivative
    (a : ℕ) (x y : ℂ) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLin' (ramifiedOrbitPointJacobian a x y)).toContinuousLinearMap

theorem ramifiedOrbitPointDerivative_apply (a : ℕ) (x y : ℂ) (v : Fin 2 → ℂ) :
    ramifiedOrbitPointDerivative a x y v =
      ![2 * x * v 0 + 2 * (a : ℂ) * y ^ (2 * a - 1) * v 1,
        (6 * x ^ 2 + 3 * y ^ (2 * a)) * v 0 +
          6 * (a : ℂ) * x * y ^ (2 * a - 1) * v 1] := by
  funext i
  fin_cases i <;>
    simp [ramifiedOrbitPointDerivative, ramifiedOrbitPointJacobian,
      Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]

theorem analyticAt_ramifiedOrbitPlaneMap (a : ℕ) (q : Fin 2 → ℂ) :
    AnalyticAt ℂ (ramifiedOrbitPlaneMap a) q := by
  rw [analyticAt_pi_iff]
  have hcoordinate (i : Fin 2) : AnalyticAt ℂ (fun p : Fin 2 → ℂ => p i) q :=
    (ContinuousLinearMap.proj (R := ℂ) i).analyticAt q
  intro i
  fin_cases i
  · exact ((hcoordinate 0).pow 2).add ((hcoordinate 1).pow (2 * a))
  · exact (analyticAt_const.mul ((hcoordinate 0).pow 3)).add
      ((analyticAt_const.mul (hcoordinate 0)).mul ((hcoordinate 1).pow (2 * a)))

/-- The displayed matrix is the strict derivative of the actual map. -/
theorem hasStrictFDerivAt_ramifiedOrbitPlaneMap (a : ℕ) (x y : ℂ) :
    HasStrictFDerivAt (ramifiedOrbitPlaneMap a)
      (ramifiedOrbitPointDerivative a x y) ![x, y] := by
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  all_goals simp only [ramifiedOrbitPlaneMap]
  · convert
      ((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![x, y]).pow 2).add
        ((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![x, y]).pow (2 * a)) using 1
    · funext q
      simp
    · ext v
      simp [ramifiedOrbitPointDerivative_apply]
  · convert
      (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![x, y]).pow 3).const_mul 2).add
        ((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![x, y]).mul
          ((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![x, y]).pow (2 * a)) |>.const_mul 3)
        using 1
    · funext q
      simp
      ring
    · ext v
      simp [ramifiedOrbitPointDerivative_apply]
      ring

theorem det_ramifiedOrbitPointJacobian (a : ℕ) (ha : 0 < a) (x y : ℂ) :
    Matrix.det (ramifiedOrbitPointJacobian a x y) = -6 * (a : ℂ) * y ^ (4 * a - 1) := by
  have hpower : y ^ (2 * a) * y ^ (2 * a - 1) = y ^ (4 * a - 1) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    Matrix.det (ramifiedOrbitPointJacobian a x y) =
        -6 * (a : ℂ) * (y ^ (2 * a) * y ^ (2 * a - 1)) := by
      simp only [ramifiedOrbitPointJacobian, Matrix.det_fin_two,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      ring
    _ = -6 * (a : ℂ) * y ^ (4 * a - 1) := by rw [hpower]

theorem det_ramifiedOrbitPointDerivative (a : ℕ) (ha : 0 < a) (x y : ℂ) :
    (ramifiedOrbitPointDerivative a x y).det = -6 * (a : ℂ) * y ^ (4 * a - 1) := by
  simpa only [ramifiedOrbitPointDerivative, LinearMap.det_toContinuousLinearMap,
    LinearMap.det_toLin'] using det_ramifiedOrbitPointJacobian a ha x y

/-- Invertibility at every point off the ramification axis. -/
@[expose] noncomputable def ramifiedOrbitPointDerivativeEquiv
    (a : ℕ) (ha : 0 < a) (x y : ℂ) (hy : y ≠ 0) :
    (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (ramifiedOrbitPointDerivative a x y).toContinuousLinearEquivOfDetNeZero <| by
    rw [det_ramifiedOrbitPointDerivative a ha]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr ha.ne'))
      (pow_ne_zero _ hy)

/-- The derivative with the variable point subtracted is invertible
under the same single-coordinate hypothesis. -/
@[expose] noncomputable def ramifiedOrbitNegativePointDerivativeEquiv
    (a : ℕ) (ha : 0 < a) (x y : ℂ) (hy : y ≠ 0) :
    (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (ramifiedOrbitPointDerivativeEquiv a ha x y hy).trans
    (ContinuousLinearEquiv.neg ℂ)

@[simp] theorem ramifiedOrbitPointDerivativeEquiv_coe
    (a : ℕ) (ha : 0 < a) (x y : ℂ) (hy : y ≠ 0) :
    (ramifiedOrbitPointDerivativeEquiv a ha x y hy).toContinuousLinearMap =
      ramifiedOrbitPointDerivative a x y := by rfl

@[simp] theorem ramifiedOrbitNegativePointDerivativeEquiv_coe
    (a : ℕ) (ha : 0 < a) (x y : ℂ) (hy : y ≠ 0) :
    (ramifiedOrbitNegativePointDerivativeEquiv a ha x y hy).toContinuousLinearMap =
      -ramifiedOrbitPointDerivative a x y := by rfl

theorem fderiv_ramifiedOrbitPlaneMap (a : ℕ) (x y : ℂ) :
    fderiv ℂ (ramifiedOrbitPlaneMap a) ![x, y] = ramifiedOrbitPointDerivative a x y :=
  (hasStrictFDerivAt_ramifiedOrbitPlaneMap a x y).hasFDerivAt.fderiv

theorem hasStrictFDerivAt_neg_ramifiedOrbitPlaneMap (a : ℕ) (x y : ℂ) :
    HasStrictFDerivAt (fun q => -ramifiedOrbitPlaneMap a q)
      (-ramifiedOrbitPointDerivative a x y) ![x, y] :=
  (hasStrictFDerivAt_ramifiedOrbitPlaneMap a x y).neg

theorem hasStrictFDerivAt_const_sub_ramifiedOrbitPlaneMap
    (a : ℕ) (v : Fin 2 → ℂ) (x y : ℂ) :
    HasStrictFDerivAt (fun q => v - ramifiedOrbitPlaneMap a q)
      (-ramifiedOrbitPointDerivative a x y) ![x, y] := by
  have hconst : HasStrictFDerivAt (fun _ : Fin 2 → ℂ => v)
      (0 : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) ![x, y] :=
    hasStrictFDerivAt_const _ _
  change HasStrictFDerivAt ((fun _ : Fin 2 → ℂ => v) - ramifiedOrbitPlaneMap a)
    (-ramifiedOrbitPointDerivative a x y) ![x, y]
  simpa only [zero_sub] using hconst.sub
    (hasStrictFDerivAt_ramifiedOrbitPlaneMap a x y)

/-- Subtracting the second point of a collision has an invertible strict
derivative whenever its second coordinate is nonzero. -/
theorem hasStrictFDerivAt_const_sub_ramifiedOrbitPlaneMap_equiv
    (a : ℕ) (ha : 0 < a) (v : Fin 2 → ℂ) (x y : ℂ) (hy : y ≠ 0) :
    HasStrictFDerivAt (fun q => v - ramifiedOrbitPlaneMap a q)
      (ramifiedOrbitNegativePointDerivativeEquiv a ha x y hy).toContinuousLinearMap
      ![x, y] := by
  simpa only [ramifiedOrbitNegativePointDerivativeEquiv_coe] using
    hasStrictFDerivAt_const_sub_ramifiedOrbitPlaneMap a v x y

theorem analyticAt_const_sub_ramifiedOrbitPlaneMap
    (a : ℕ) (v q : Fin 2 → ℂ) :
    AnalyticAt ℂ (fun p => v - ramifiedOrbitPlaneMap a p) q :=
  analyticAt_const.sub (analyticAt_ramifiedOrbitPlaneMap a q)

end OnLeConjecture.DTwo
