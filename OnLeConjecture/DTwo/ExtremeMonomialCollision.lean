/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TwoWeightSimpleCollision
public import OnLeConjecture.Analytic.WeightedOrderIdealAlgebra
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# A monomial residual in the extreme quadratic alternative

The initial map `(x²+y^(2a), 2x³+3xy^(2a), c y^rho)` has a simple
collision at `(xi,1),(-xi,1)`, where `xi²=-3/2`. The determinant
calculation and analytic persistence hold for every positive `rho`.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ DThree

@[expose] noncomputable def extremeMonomialPolynomials (a rho : ℕ) (c : ℂ) :
    Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ (2 * a),
    2 * MvPolynomial.X 0 ^ 3 + 3 * MvPolynomial.X 0 * MvPolynomial.X 1 ^ (2 * a),
    MvPolynomial.C c * MvPolynomial.X 1 ^ rho]

@[expose] def extremeMonomialDegrees (a rho : ℕ) : Fin 3 → ℕ := ![2 * a, 3 * a, rho]

@[expose] noncomputable def extremeMonomialDifference (a rho : ℕ) (c : ℂ)
    (q : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![q 0 ^ 2 + 1 - (q 1 ^ 2 + q 2 ^ (2 * a)),
    2 * q 0 ^ 3 + 3 * q 0 - (2 * q 1 ^ 3 + 3 * q 1 * q 2 ^ (2 * a)),
    c - c * q 2 ^ rho]

theorem extremeMonomial_difference_eq (a rho : ℕ) (c : ℂ) :
    weightedInitialDifference (weightedPolynomialMap (extremeMonomialPolynomials a rho c)) =
      extremeMonomialDifference a rho c := by
  funext q i
  fin_cases i <;> simp [weightedInitialDifference, weightedPolynomialMap,
    extremeMonomialPolynomials, extremeMonomialDifference, residueFirstChartPoint,
    residueSecondChartPoint]

theorem extremeMonomial_homogeneous (a rho : ℕ) (c : ℂ) (i : Fin 3) :
    (extremeMonomialPolynomials a rho c i).IsWeightedHomogeneous ![a, 1]
      (extremeMonomialDegrees a rho i) := by
  have hx := MvPolynomial.isWeightedHomogeneous_X ℂ (![a, 1] : Fin 2 → ℕ) 0
  have hy := MvPolynomial.isWeightedHomogeneous_X ℂ (![a, 1] : Fin 2 → ℕ) 1
  change (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous ![a, 1] a at hx
  change (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous ![a, 1] 1 at hy
  fin_cases i
  · exact (hx.pow 2).add (by simpa using hy.pow (2 * a))
  · have hfirst := (hx.pow 3).C_mul 2
    have hsecond := (hx.C_mul 3).mul (hy.pow (2 * a))
    have hdegree : a + (2 * a) • 1 = 3 • a := by simp; omega
    rw [hdegree] at hsecond
    simpa [extremeMonomialPolynomials, extremeMonomialDegrees, nsmul_eq_mul, map_ofNat] using
      hfirst.add hsecond
  · simpa [extremeMonomialPolynomials, extremeMonomialDegrees, nsmul_eq_mul] using
      (hy.pow rho).C_mul c

theorem extremeMonomial_analyticAt (a rho : ℕ) (c : ℂ) (q : Fin 3 → ℂ) :
    AnalyticAt ℂ (extremeMonomialDifference a rho c) q := by
  have hc (i : Fin 3) : AnalyticAt ℂ (fun p : Fin 3 → ℂ => p i) q :=
    (ContinuousLinearMap.proj (R := ℂ) i).analyticAt q
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · change AnalyticAt ℂ (fun p : Fin 3 → ℂ => p 0 ^ 2 + 1 -
      (p 1 ^ 2 + p 2 ^ (2 * a))) q
    exact (((hc 0).pow 2).add analyticAt_const).sub
      (((hc 1).pow 2).add ((hc 2).pow (2 * a)))
  · change AnalyticAt ℂ (fun p : Fin 3 → ℂ => 2 * p 0 ^ 3 + 3 * p 0 -
      (2 * p 1 ^ 3 + 3 * p 1 * p 2 ^ (2 * a))) q
    exact ((analyticAt_const.mul ((hc 0).pow 3)).add (analyticAt_const.mul (hc 0))).sub
      ((analyticAt_const.mul ((hc 1).pow 3)).add
        ((analyticAt_const.mul (hc 1)).mul ((hc 2).pow (2 * a))))
  · change AnalyticAt ℂ (fun p : Fin 3 → ℂ => c - c * p 2 ^ rho) q
    exact analyticAt_const.sub (analyticAt_const.mul ((hc 2).pow rho))

@[expose] noncomputable def extremeMonomialMatrix (a rho : ℕ) (c xi : ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![2 * xi, 2 * xi, -(2 * a : ℕ);
    6 * xi ^ 2 + 3, -(6 * xi ^ 2 + 3), 3 * xi * (2 * a : ℕ);
    0, 0, -c * (rho : ℕ)]

@[expose] noncomputable def extremeMonomialDerivative (a rho : ℕ) (c xi : ℂ) :
    (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ) :=
  (Matrix.toLin' (extremeMonomialMatrix a rho c xi)).toContinuousLinearMap

theorem extremeMonomial_hasStrictFDerivAt (a rho : ℕ) (c xi : ℂ) :
    HasStrictFDerivAt (extremeMonomialDifference a rho c)
      (extremeMonomialDerivative a rho c xi) ![xi, -xi, 1] := by
  have hd (i : Fin 3) := hasStrictFDerivAt_apply (𝕜 := ℂ) i ![xi, -xi, 1]
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  · convert (((hd 0).pow 2).add_const 1).sub
      (((hd 1).pow 2).add ((hd 2).pow (2 * a))) using 1
    · rfl
    · ext v
      simp [extremeMonomialDerivative, extremeMonomialMatrix, Matrix.toLin'_apply,
        dotProduct, Fin.sum_univ_succ]
      ring
  · convert ((((hd 0).pow 3).const_mul 2).add ((hd 0).const_mul 3)).sub
      ((((hd 1).pow 3).const_mul 2).add
        (((hd 1).const_mul 3).mul ((hd 2).pow (2 * a)))) using 1
    · rfl
    · ext v
      simp [extremeMonomialDerivative, extremeMonomialMatrix, Matrix.toLin'_apply,
        dotProduct, Fin.sum_univ_succ]
      ring
  · convert (hasStrictFDerivAt_const (𝕜 := ℂ) c ![xi, -xi, 1]).sub
      (((hd 2).pow rho).const_mul c) using 1
    · rfl
    · ext v
      simp [extremeMonomialDerivative, extremeMonomialMatrix, Matrix.toLin'_apply,
        dotProduct, Fin.sum_univ_succ]
      ring

theorem extremeMonomial_derivative_invertible
    (a rho : ℕ) (hrho : 0 < rho) (c xi : ℂ) (hc : c ≠ 0) (hxi : xi ^ 2 = -3 / 2) :
    (extremeMonomialDerivative a rho c xi).IsInvertible := by
  have hx : xi ≠ 0 := by intro hz; norm_num [hz] at hxi
  have hdet : (extremeMonomialDerivative a rho c xi).det = -24 * c * (rho : ℂ) * xi := by
    rw [extremeMonomialDerivative, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin']
    simp [extremeMonomialMatrix, Matrix.det_fin_three, hxi]
    ring
  have hn : (extremeMonomialDerivative a rho c xi).det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hc)
      (Nat.cast_ne_zero.mpr hrho.ne')) hx
  exact ⟨(extremeMonomialDerivative a rho c xi).toContinuousLinearEquivOfDetNeZero hn,
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _⟩

/-- The pure monomial residual excludes injectivity for all positive
weights and positive residual degrees. -/
theorem extremeMonomial_orderTails_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (a rho : ℕ) (ha : 0 < a) (hrho : 0 < rho)
    (c : ℂ) (hc : c ≠ 0)
    (htail : ∀ i, g.1.component i - coordinatePolynomialAlgHom 2
      (extremeMonomialPolynomials a rho c i) ∈
        weightedOrderIdeal a (extremeMonomialDegrees a rho i + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨xi, hxi⟩ := IsAlgClosed.exists_pow_nat_eq (-3 / 2 : ℂ) (by norm_num : 0 < 2)
  have hx : xi ≠ 0 := by intro hz; norm_num [hz] at hxi
  have hzero : extremeMonomialDifference a rho c ![xi, -xi, 1] = 0 := by
    ext i
    fin_cases i
    · simp [extremeMonomialDifference]
    · change 2 * xi ^ 3 + 3 * xi - (2 * (-xi) ^ 3 + 3 * (-xi) * 1 ^ (2 * a)) = 0
      simp only [one_pow, mul_one]
      linear_combination (4 * xi) * hxi
    · simp [extremeMonomialDifference]
  apply twoWeight_simple_collision_not_hasInjectiveRepresentative g a 1 ha (by omega)
    (extremeMonomialDegrees a rho) (extremeMonomialPolynomials a rho c)
    (extremeMonomial_homogeneous a rho c) _ xi (-xi) 1 _ _ _
    (extremeMonomialDerivative a rho c xi) _
    (extremeMonomial_derivative_invertible a rho hrho c xi hc hxi)
  · intro i
    rw [← weightedOrderIdeal_eq_twoWeightOrderIdeal a _ ha]
    exact htail i
  · left
    intro hh
    apply hx
    linear_combination (1 / 2 : ℂ) * hh
  · rw [extremeMonomial_difference_eq]
    exact extremeMonomial_analyticAt a rho c _
  · rwa [extremeMonomial_difference_eq]
  · rw [extremeMonomial_difference_eq]
    exact extremeMonomial_hasStrictFDerivAt a rho c xi

end OnLeConjecture.DTwo
