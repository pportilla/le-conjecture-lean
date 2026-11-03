/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineDegreeCertificate
public import OnLeConjecture.DThree.HGlobalOrders
public import Mathlib.FieldTheory.KummerPolynomial

/-!
# Kummer order certificates for the C9 generic fibre

In the chart `x ≠ 0`, the two cubic equations defining C9 adjoin cubic
roots of two rational functions of `lambda = X/x`.  This file proves the
valuation calculation used in the article.  At a simple root of the first
quadratic, the first function has order one and the second has order zero.
The roles are reversed at a simple root of the second quadratic.

Consequently the two rational functions are independent modulo cubes.  This
is the field theoretic input for the degree nine Kummer extension.  The
scheme theoretic passage from that extension to the projective C9 curve is
not part of this file.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open scoped WithZero

/-- The first quadratic factor in the generic C9 equation. -/
@[expose]
noncomputable def eCNineFirstKummerQuadratic : ℂ[X] :=
  X ^ 2 + C 2 * X + C 3

/-- The second quadratic factor in the generic C9 equation. -/
@[expose]
noncomputable def eCNineSecondKummerQuadratic : ℂ[X] :=
  C 3 * X ^ 2 + C 2 * X + C 1

/-- The numerator of the first Kummer class. -/
@[expose]
noncomputable def eCNineFirstKummerNumerator : ℂ[X] :=
  (X - C 1) * eCNineFirstKummerQuadratic

/-- The numerator of the second Kummer class. -/
@[expose]
noncomputable def eCNineSecondKummerNumerator : ℂ[X] :=
  (C 1 - X) * eCNineSecondKummerQuadratic

/-- The first rational function whose cubic root is adjoined on C9. -/
@[expose]
noncomputable def eCNineFirstKummerFunction : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) eCNineFirstKummerNumerator /
    algebraMap ℂ[X] (RatFunc ℂ) (C 12)

/-- The second rational function whose cubic root is adjoined on C9. -/
@[expose]
noncomputable def eCNineSecondKummerFunction : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) eCNineSecondKummerNumerator /
    algebraMap ℂ[X] (RatFunc ℂ) (C 12)

/-- The first cubic Kummer polynomial over `ℂ(lambda)`. -/
@[expose]
noncomputable def eCNineFirstKummerPolynomial : (RatFunc ℂ)[X] :=
  X ^ 3 - C eCNineFirstKummerFunction

/-- The second cubic Kummer polynomial over `ℂ(lambda)`. -/
@[expose]
noncomputable def eCNineSecondKummerPolynomial : (RatFunc ℂ)[X] :=
  X ^ 3 - C eCNineSecondKummerFunction

@[simp]
theorem eCNineFirstKummerQuadratic_eval (z : ℂ) :
    eCNineFirstKummerQuadratic.eval z = z ^ 2 + 2 * z + 3 := by
  simp [eCNineFirstKummerQuadratic]

@[simp]
theorem eCNineSecondKummerQuadratic_eval (z : ℂ) :
    eCNineSecondKummerQuadratic.eval z = 3 * z ^ 2 + 2 * z + 1 := by
  simp [eCNineSecondKummerQuadratic]

theorem eCNineFirstKummerQuadratic_ne_zero :
    eCNineFirstKummerQuadratic ≠ 0 := by
  intro hzero
  have heval := congrArg (fun p : ℂ[X] ↦ p.eval 0) hzero
  norm_num [eCNineFirstKummerQuadratic] at heval

theorem eCNineSecondKummerQuadratic_ne_zero :
    eCNineSecondKummerQuadratic ≠ 0 := by
  intro hzero
  have heval := congrArg (fun p : ℂ[X] ↦ p.eval 0) hzero
  norm_num [eCNineSecondKummerQuadratic] at heval

/-- The first quadratic has a root that is distinct from one and minus one,
and the second quadratic does not vanish there. -/
theorem eCNine_exists_first_kummer_root :
    ∃ alpha : ℂ,
      eCNineFirstKummerQuadratic.IsRoot alpha ∧
      alpha ≠ 1 ∧ alpha ≠ -1 ∧
      ¬ eCNineSecondKummerQuadratic.IsRoot alpha := by
  have hdegree : eCNineFirstKummerQuadratic.degree ≠ 0 := by
    intro hdegree
    have hlt : eCNineFirstKummerQuadratic.degree < (2 : WithBot ℕ) := by
      rw [hdegree]
      norm_num
    have hcoeff := Polynomial.coeff_eq_zero_of_degree_lt hlt
    norm_num [eCNineFirstKummerQuadratic] at hcoeff
  obtain ⟨alpha, halpha⟩ :=
    IsAlgClosed.exists_root eCNineFirstKummerQuadratic hdegree
  have halphaEq : alpha ^ 2 + 2 * alpha + 3 = 0 := by
    simpa [Polynomial.IsRoot] using halpha
  have halphaOne : alpha ≠ 1 := by
    intro h
    rw [h] at halphaEq
    norm_num at halphaEq
  have halphaNegOne : alpha ≠ -1 := by
    intro h
    rw [h] at halphaEq
    norm_num at halphaEq
  have hsecond : ¬ eCNineSecondKummerQuadratic.IsRoot alpha := by
    intro hroot
    have hsecondEq : 3 * alpha ^ 2 + 2 * alpha + 1 = 0 := by
      simpa [Polynomial.IsRoot] using hroot
    have halphaNegTwo : alpha = -2 := by
      linear_combination (3 * halphaEq - hsecondEq) / 4
    rw [halphaNegTwo] at halphaEq
    norm_num at halphaEq
  exact ⟨alpha, halpha, halphaOne, halphaNegOne, hsecond⟩

/-- The second quadratic has a root that is distinct from one and minus one,
and the first quadratic does not vanish there. -/
theorem eCNine_exists_second_kummer_root :
    ∃ beta : ℂ,
      eCNineSecondKummerQuadratic.IsRoot beta ∧
      beta ≠ 1 ∧ beta ≠ -1 ∧
      ¬ eCNineFirstKummerQuadratic.IsRoot beta := by
  have hdegree : eCNineSecondKummerQuadratic.degree ≠ 0 := by
    intro hdegree
    have hlt : eCNineSecondKummerQuadratic.degree < (2 : WithBot ℕ) := by
      rw [hdegree]
      norm_num
    have hcoeff := Polynomial.coeff_eq_zero_of_degree_lt hlt
    norm_num [eCNineSecondKummerQuadratic, Polynomial.coeff_one] at hcoeff
  obtain ⟨beta, hbeta⟩ :=
    IsAlgClosed.exists_root eCNineSecondKummerQuadratic hdegree
  have hbetaEq : 3 * beta ^ 2 + 2 * beta + 1 = 0 := by
    simpa [Polynomial.IsRoot] using hbeta
  have hbetaOne : beta ≠ 1 := by
    intro h
    rw [h] at hbetaEq
    norm_num at hbetaEq
  have hbetaNegOne : beta ≠ -1 := by
    intro h
    rw [h] at hbetaEq
    norm_num at hbetaEq
  have hfirst : ¬ eCNineFirstKummerQuadratic.IsRoot beta := by
    intro hroot
    have hfirstEq : beta ^ 2 + 2 * beta + 3 = 0 := by
      simpa [Polynomial.IsRoot] using hroot
    have hbetaNegTwo : beta = -2 := by
      linear_combination (3 * hfirstEq - hbetaEq) / 4
    rw [hbetaNegTwo] at hbetaEq
    norm_num at hbetaEq
  exact ⟨beta, hbeta, hbetaOne, hbetaNegOne, hfirst⟩

/-- A root of the first quadratic is simple. -/
theorem eCNineFirstKummerQuadratic_rootMultiplicity
    {alpha : ℂ} (halpha : eCNineFirstKummerQuadratic.IsRoot alpha)
    (halphaNegOne : alpha ≠ -1) :
    eCNineFirstKummerQuadratic.rootMultiplicity alpha = 1 := by
  have hpositive : 0 <
      eCNineFirstKummerQuadratic.rootMultiplicity alpha :=
    (Polynomial.rootMultiplicity_pos
      eCNineFirstKummerQuadratic_ne_zero).mpr halpha
  have hnotLarge : ¬ 1 <
      eCNineFirstKummerQuadratic.rootMultiplicity alpha := by
    intro hlarge
    have hderivative :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot
        eCNineFirstKummerQuadratic_ne_zero).mp hlarge |>.2
    have hderivativeEq : 2 * alpha + 2 = 0 := by
      calc
        2 * alpha + 2 =
            eCNineFirstKummerQuadratic.derivative.eval alpha := by
          simp only [eCNineFirstKummerQuadratic, derivative_add,
            derivative_X_sq, derivative_mul, derivative_C, derivative_X,
            eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one]
          ring
        _ = 0 := hderivative
    apply halphaNegOne
    linear_combination hderivativeEq / 2
  omega

/-- A root of the second quadratic is simple. -/
theorem eCNineSecondKummerQuadratic_rootMultiplicity
    {beta : ℂ} (hbeta : eCNineSecondKummerQuadratic.IsRoot beta) :
    eCNineSecondKummerQuadratic.rootMultiplicity beta = 1 := by
  have hpositive : 0 <
      eCNineSecondKummerQuadratic.rootMultiplicity beta :=
    (Polynomial.rootMultiplicity_pos
      eCNineSecondKummerQuadratic_ne_zero).mpr hbeta
  have hnotLarge : ¬ 1 <
      eCNineSecondKummerQuadratic.rootMultiplicity beta := by
    intro hlarge
    have hderivative :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot
        eCNineSecondKummerQuadratic_ne_zero).mp hlarge |>.2
    have hderivativeEq : 6 * beta + 2 = 0 := by
      calc
        6 * beta + 2 =
            eCNineSecondKummerQuadratic.derivative.eval beta := by
          simp only [eCNineSecondKummerQuadratic, derivative_add,
            derivative_X_sq, derivative_mul, derivative_C, derivative_X,
            eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one]
          ring
        _ = 0 := hderivative
    have hbetaValue : beta = -(1 / 3 : ℂ) := by
      linear_combination hderivativeEq / 6
    have hrootEq : 3 * beta ^ 2 + 2 * beta + 1 = 0 := by
      simpa [Polynomial.IsRoot] using hbeta
    rw [hbetaValue] at hrootEq
    norm_num at hrootEq
  omega

theorem eCNineFirstKummerNumerator_ne_zero :
    eCNineFirstKummerNumerator ≠ 0 := by
  rw [eCNineFirstKummerNumerator]
  exact mul_ne_zero (X_sub_C_ne_zero 1)
    eCNineFirstKummerQuadratic_ne_zero

theorem eCNineSecondKummerNumerator_ne_zero :
    eCNineSecondKummerNumerator ≠ 0 := by
  rw [eCNineSecondKummerNumerator]
  apply mul_ne_zero
  · intro hzero
    have heval := congrArg (fun p : ℂ[X] ↦ p.eval 0) hzero
    norm_num at heval
  · exact eCNineSecondKummerQuadratic_ne_zero

/-- At the selected root of the first quadratic, the two numerators have
multiplicities one and zero. -/
theorem eCNine_kummer_numerator_multiplicities_at_first_root
    {alpha : ℂ}
    (halpha : eCNineFirstKummerQuadratic.IsRoot alpha)
    (halphaOne : alpha ≠ 1) (halphaNegOne : alpha ≠ -1)
    (hsecond : ¬ eCNineSecondKummerQuadratic.IsRoot alpha) :
    eCNineFirstKummerNumerator.rootMultiplicity alpha = 1 ∧
      eCNineSecondKummerNumerator.rootMultiplicity alpha = 0 := by
  have hlinearFirst : ¬ (X - C (1 : ℂ)).IsRoot alpha := by
    simpa [Polynomial.IsRoot] using sub_ne_zero.mpr halphaOne
  have hlinearSecond : ¬ (C (1 : ℂ) - X).IsRoot alpha := by
    simpa [Polynomial.IsRoot] using sub_ne_zero.mpr (Ne.symm halphaOne)
  constructor
  · rw [eCNineFirstKummerNumerator,
      Polynomial.rootMultiplicity_mul eCNineFirstKummerNumerator_ne_zero,
      Polynomial.rootMultiplicity_eq_zero hlinearFirst,
      eCNineFirstKummerQuadratic_rootMultiplicity halpha halphaNegOne]
  · rw [eCNineSecondKummerNumerator,
      Polynomial.rootMultiplicity_mul eCNineSecondKummerNumerator_ne_zero,
      Polynomial.rootMultiplicity_eq_zero hlinearSecond,
      Polynomial.rootMultiplicity_eq_zero hsecond]

/-- At the selected root of the second quadratic, the two numerators have
multiplicities zero and one. -/
theorem eCNine_kummer_numerator_multiplicities_at_second_root
    {beta : ℂ}
    (hbeta : eCNineSecondKummerQuadratic.IsRoot beta)
    (hbetaOne : beta ≠ 1)
    (hfirst : ¬ eCNineFirstKummerQuadratic.IsRoot beta) :
    eCNineFirstKummerNumerator.rootMultiplicity beta = 0 ∧
      eCNineSecondKummerNumerator.rootMultiplicity beta = 1 := by
  have hlinearFirst : ¬ (X - C (1 : ℂ)).IsRoot beta := by
    simpa [Polynomial.IsRoot] using sub_ne_zero.mpr hbetaOne
  have hlinearSecond : ¬ (C (1 : ℂ) - X).IsRoot beta := by
    simpa [Polynomial.IsRoot] using sub_ne_zero.mpr (Ne.symm hbetaOne)
  constructor
  · rw [eCNineFirstKummerNumerator,
      Polynomial.rootMultiplicity_mul eCNineFirstKummerNumerator_ne_zero,
      Polynomial.rootMultiplicity_eq_zero hlinearFirst,
      Polynomial.rootMultiplicity_eq_zero hfirst]
  · rw [eCNineSecondKummerNumerator,
      Polynomial.rootMultiplicity_mul eCNineSecondKummerNumerator_ne_zero,
      Polynomial.rootMultiplicity_eq_zero hlinearSecond,
      eCNineSecondKummerQuadratic_rootMultiplicity hbeta]

theorem eCNineFirstKummerFunction_ne_zero :
    eCNineFirstKummerFunction ≠ 0 := by
  rw [eCNineFirstKummerFunction]
  exact div_ne_zero
    (RatFunc.algebraMap_ne_zero eCNineFirstKummerNumerator_ne_zero)
    (RatFunc.algebraMap_ne_zero (by norm_num : (C (12 : ℂ) : ℂ[X]) ≠ 0))

theorem eCNineSecondKummerFunction_ne_zero :
    eCNineSecondKummerFunction ≠ 0 := by
  rw [eCNineSecondKummerFunction]
  exact div_ne_zero
    (RatFunc.algebraMap_ne_zero eCNineSecondKummerNumerator_ne_zero)
    (RatFunc.algebraMap_ne_zero (by norm_num : (C (12 : ℂ) : ℂ[X]) ≠ 0))

/-- The finite orders of the two Kummer functions at a root of the first
quadratic are one and zero. -/
theorem eCNine_kummer_function_orders_at_first_root
    {alpha : ℂ}
    (halpha : eCNineFirstKummerQuadratic.IsRoot alpha)
    (halphaOne : alpha ≠ 1) (halphaNegOne : alpha ≠ -1)
    (hsecond : ¬ eCNineSecondKummerQuadratic.IsRoot alpha) :
    hFiniteOrderAt alpha eCNineFirstKummerFunction =
        WithZero.exp (1 : ℤ) ∧
      hFiniteOrderAt alpha eCNineSecondKummerFunction = 1 := by
  have hmultiplicity :=
    eCNine_kummer_numerator_multiplicities_at_first_root
      halpha halphaOne halphaNegOne hsecond
  constructor
  · rw [eCNineFirstKummerFunction, map_div₀,
      h_finite_order_polynomial_eq_rootMultiplicity alpha
        eCNineFirstKummerNumerator eCNineFirstKummerNumerator_ne_zero,
      h_finite_order_polynomial_of_eval_ne_zero alpha (C 12) (by norm_num),
      hmultiplicity.1, div_one]
    norm_num
  · rw [eCNineSecondKummerFunction, map_div₀,
      h_finite_order_polynomial_eq_rootMultiplicity alpha
        eCNineSecondKummerNumerator eCNineSecondKummerNumerator_ne_zero,
      h_finite_order_polynomial_of_eval_ne_zero alpha (C 12) (by norm_num),
      hmultiplicity.2, div_one]
    simp

/-- The finite orders of the two Kummer functions at a root of the second
quadratic are zero and one. -/
theorem eCNine_kummer_function_orders_at_second_root
    {beta : ℂ}
    (hbeta : eCNineSecondKummerQuadratic.IsRoot beta)
    (hbetaOne : beta ≠ 1)
    (hfirst : ¬ eCNineFirstKummerQuadratic.IsRoot beta) :
    hFiniteOrderAt beta eCNineFirstKummerFunction = 1 ∧
      hFiniteOrderAt beta eCNineSecondKummerFunction =
        WithZero.exp (1 : ℤ) := by
  have hmultiplicity :=
    eCNine_kummer_numerator_multiplicities_at_second_root
      hbeta hbetaOne hfirst
  constructor
  · rw [eCNineFirstKummerFunction, map_div₀,
      h_finite_order_polynomial_eq_rootMultiplicity beta
        eCNineFirstKummerNumerator eCNineFirstKummerNumerator_ne_zero,
      h_finite_order_polynomial_of_eval_ne_zero beta (C 12) (by norm_num),
      hmultiplicity.1, div_one]
    simp
  · rw [eCNineSecondKummerFunction, map_div₀,
      h_finite_order_polynomial_eq_rootMultiplicity beta
        eCNineSecondKummerNumerator eCNineSecondKummerNumerator_ne_zero,
      h_finite_order_polynomial_of_eval_ne_zero beta (C 12) (by norm_num),
      hmultiplicity.2, div_one]
    norm_num

/-- There are two points of the parameter line at which the two local order
vectors are `(1,0)` and `(0,1)`. -/
theorem eCNine_exists_kummer_order_points :
    ∃ alpha beta : ℂ,
      alpha ≠ beta ∧
      hFiniteOrderAt alpha eCNineFirstKummerFunction =
        WithZero.exp (1 : ℤ) ∧
      hFiniteOrderAt alpha eCNineSecondKummerFunction = 1 ∧
      hFiniteOrderAt beta eCNineFirstKummerFunction = 1 ∧
      hFiniteOrderAt beta eCNineSecondKummerFunction =
        WithZero.exp (1 : ℤ) := by
  obtain ⟨alpha, halpha, halphaOne, halphaNegOne, hsecond⟩ :=
    eCNine_exists_first_kummer_root
  obtain ⟨beta, hbeta, hbetaOne, _hbetaNegOne, hfirst⟩ :=
    eCNine_exists_second_kummer_root
  have halphaOrders := eCNine_kummer_function_orders_at_first_root
    halpha halphaOne halphaNegOne hsecond
  have hbetaOrders := eCNine_kummer_function_orders_at_second_root
    hbeta hbetaOne hfirst
  have hne : alpha ≠ beta := by
    intro heq
    apply hsecond
    rwa [heq]
  exact ⟨alpha, beta, hne, halphaOrders.1, halphaOrders.2,
    hbetaOrders.1, hbetaOrders.2⟩

/-- A rational function with order one at a finite point cannot be a cube. -/
theorem ratFunc_not_cube_of_finite_order_one
    (a : ℂ) (f : RatFunc ℂ)
    (horder : hFiniteOrderAt a f = WithZero.exp (1 : ℤ)) :
    ∀ z : RatFunc ℂ, z ^ 3 ≠ f := by
  intro z hz
  have heq : (hFiniteOrderAt a z) ^ 3 = WithZero.exp (1 : ℤ) := by
    rw [← map_pow, hz, horder]
  have hlog := congrArg WithZero.log heq
  simp only [WithZero.log_pow, WithZero.log_exp] at hlog
  have hdiv : (3 : ℤ) ∣ 1 := by
    exact ⟨(hFiniteOrderAt a z).log, hlog.symm⟩
  norm_num at hdiv

/-- The two functions are independent modulo cubes for exponents in
`{0,1,2}`. -/
theorem ratFunc_independent_mod_cubes_of_order_vectors
    (a b : ℂ) (f g : RatFunc ℂ)
    (hfa : hFiniteOrderAt a f = WithZero.exp (1 : ℤ))
    (hga : hFiniteOrderAt a g = 1)
    (hfb : hFiniteOrderAt b f = 1)
    (hgb : hFiniteOrderAt b g = WithZero.exp (1 : ℤ))
    {i j : ℕ} (hi : i < 3) (hj : j < 3)
    (hcube : ∃ z : RatFunc ℂ, z ^ 3 = f ^ i * g ^ j) :
    i = 0 ∧ j = 0 := by
  obtain ⟨z, hz⟩ := hcube
  have heqA : (hFiniteOrderAt a z) ^ 3 =
      (WithZero.exp (1 : ℤ)) ^ i := by
    rw [← map_pow, hz, map_mul, map_pow, map_pow, hfa, hga]
    simp
  have hlogA := congrArg WithZero.log heqA
  simp only [WithZero.log_pow, WithZero.log_exp] at hlogA
  have hdivA : (3 : ℤ) ∣ (i : ℤ) := by
    exact ⟨(hFiniteOrderAt a z).log, by simpa using hlogA.symm⟩
  have hiZero : i = 0 := by
    omega
  have heqB : (hFiniteOrderAt b z) ^ 3 =
      (WithZero.exp (1 : ℤ)) ^ j := by
    rw [← map_pow, hz, map_mul, map_pow, map_pow, hfb, hgb]
    simp
  have hlogB := congrArg WithZero.log heqB
  simp only [WithZero.log_pow, WithZero.log_exp] at hlogB
  have hdivB : (3 : ℤ) ∣ (j : ℤ) := by
    exact ⟨(hFiniteOrderAt b z).log, by simpa using hlogB.symm⟩
  have hjZero : j = 0 := by
    omega
  exact ⟨hiZero, hjZero⟩

theorem eCNineFirstKummerFunction_not_cube :
    ∀ z : RatFunc ℂ, z ^ 3 ≠ eCNineFirstKummerFunction := by
  obtain ⟨alpha, _beta, _hne, hfirst, _hsecond, _hthird, _hfourth⟩ :=
    eCNine_exists_kummer_order_points
  exact ratFunc_not_cube_of_finite_order_one alpha
    eCNineFirstKummerFunction hfirst

theorem eCNineSecondKummerFunction_not_cube :
    ∀ z : RatFunc ℂ, z ^ 3 ≠ eCNineSecondKummerFunction := by
  obtain ⟨_alpha, beta, _hne, _hfirst, _hsecond, _hthird, hfourth⟩ :=
    eCNine_exists_kummer_order_points
  exact ratFunc_not_cube_of_finite_order_one beta
    eCNineSecondKummerFunction hfourth

/-- The two C9 Kummer classes are independent in
`RatFunc ℂˣ/(RatFunc ℂˣ)³`. -/
theorem eCNineKummerFunctions_independent_mod_cubes
    {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    (∃ z : RatFunc ℂ,
      z ^ 3 = eCNineFirstKummerFunction ^ i *
        eCNineSecondKummerFunction ^ j) ↔
      i = 0 ∧ j = 0 := by
  constructor
  · obtain ⟨alpha, beta, _hne, hfirst, hsecond, hthird, hfourth⟩ :=
      eCNine_exists_kummer_order_points
    exact ratFunc_independent_mod_cubes_of_order_vectors
      alpha beta eCNineFirstKummerFunction eCNineSecondKummerFunction
      hfirst hsecond hthird hfourth hi hj
  · rintro ⟨rfl, rfl⟩
    exact ⟨1, by simp⟩

/-- The first cubic Kummer polynomial is irreducible over `ℂ(lambda)`. -/
theorem eCNineFirstKummerPolynomial_irreducible :
    Irreducible eCNineFirstKummerPolynomial := by
  rw [eCNineFirstKummerPolynomial]
  exact X_pow_sub_C_irreducible_of_prime (by decide)
    eCNineFirstKummerFunction_not_cube

/-- The second cubic Kummer polynomial is irreducible over `ℂ(lambda)`. -/
theorem eCNineSecondKummerPolynomial_irreducible :
    Irreducible eCNineSecondKummerPolynomial := by
  rw [eCNineSecondKummerPolynomial]
  exact X_pow_sub_C_irreducible_of_prime (by decide)
    eCNineSecondKummerFunction_not_cube

end OnLeConjecture.DThree
