/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HProjectiveSectionZero

/-!
# The zero at infinity of an `H` pole profile

The common denominator used for the rational conic pullback has degree
`a + 2 * b`.  This file computes the order at infinity of a represented
section.  In particular, strict loss of numerator degree gives a positive
order at infinity.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open scoped WithZero

variable {K : Type*} [Field K] [CharZero K]

/-! ## Reciprocal substitution -/

/-- Evaluation of a polynomial at the reciprocal of the rational parameter. -/
@[expose]
noncomputable def hReciprocalPolynomialRingHom :
    K[X] →+* RatFunc K :=
  Polynomial.eval₂RingHom (algebraMap K (RatFunc K)) (1 / RatFunc.X)

omit [CharZero K] in
/-- The reciprocal of the rational parameter is transcendental. -/
theorem h_reciprocal_parameter_transcendental :
    Transcendental K (1 / (RatFunc.X : RatFunc K)) := by
  rw [one_div]
  rw [Transcendental, IsAlgebraic.inv_iff]
  exact RatFunc.transcendental_X

omit [CharZero K] in
/-- Polynomial substitution at the reciprocal parameter is injective. -/
theorem h_reciprocalPolynomialRingHom_injective :
    Function.Injective (hReciprocalPolynomialRingHom (K := K)) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  apply (transcendental_iff.mp
    (h_reciprocal_parameter_transcendental (K := K)) p)
  change Polynomial.eval₂ (algebraMap K (RatFunc K))
      (1 / RatFunc.X) p = 0 at hp
  simpa only [Polynomial.aeval_def] using hp

omit [CharZero K] in
theorem h_reciprocalPolynomialRingHom_nonzeroDivisors :
    nonZeroDivisors K[X] ≤
      (nonZeroDivisors (RatFunc K)).comap
        (hReciprocalPolynomialRingHom (K := K)) := by
  intro p hp
  rw [mem_nonZeroDivisors_iff_ne_zero] at hp
  change hReciprocalPolynomialRingHom p ∈
    nonZeroDivisors (RatFunc K)
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hzero
  apply hp
  exact h_reciprocalPolynomialRingHom_injective (by simpa using hzero)

/-- The ring endomorphism of `K(m)` induced by `m ↦ 1 / m`. -/
@[expose]
noncomputable def hReciprocalRatFuncRingHom :
    RatFunc K →+* RatFunc K :=
  RatFunc.liftRingHom (hReciprocalPolynomialRingHom (K := K))
    h_reciprocalPolynomialRingHom_nonzeroDivisors

omit [CharZero K] in
@[simp]
theorem h_reciprocalRatFuncRingHom_X :
    hReciprocalRatFuncRingHom (K := K) RatFunc.X = 1 / RatFunc.X := by
  rw [← RatFunc.algebraMap_X, hReciprocalRatFuncRingHom,
    RatFunc.liftRingHom_algebraMap]
  simp [hReciprocalPolynomialRingHom]

omit [CharZero K] in
@[simp]
theorem h_reciprocalRatFuncRingHom_algebraMap (p : K[X]) :
    hReciprocalRatFuncRingHom (K := K)
        (algebraMap K[X] (RatFunc K) p) =
      Polynomial.eval₂ (algebraMap K (RatFunc K))
        (1 / RatFunc.X) p := by
  rw [hReciprocalRatFuncRingHom, RatFunc.liftRingHom_algebraMap]
  rfl

omit [CharZero K] in
@[simp]
theorem h_reciprocalRatFuncRingHom_algebraMap_scalar (c : K) :
    hReciprocalRatFuncRingHom (K := K)
        (algebraMap K (RatFunc K) c) =
      algebraMap K (RatFunc K) c := by
  change hReciprocalRatFuncRingHom (K := K)
      (algebraMap K[X] (RatFunc K) (Polynomial.C c)) = _
  rw [h_reciprocalRatFuncRingHom_algebraMap]
  simp

omit [CharZero K] in
/-- Reciprocal substitution commutes with evaluation of a bivariate form. -/
theorem h_reciprocalRatFuncRingHom_hFormEval
    (x w : RatFunc K) (F : MvPolynomial (Fin 2) K) :
    hReciprocalRatFuncRingHom (K := K) (hFormEval x w F) =
      hFormEval (hReciprocalRatFuncRingHom x)
        (hReciprocalRatFuncRingHom w) F := by
  simp only [hFormEval]
  rw [MvPolynomial.hom_eval₂]
  congr 1
  · ext c
    change hReciprocalRatFuncRingHom (K := K)
        (algebraMap K (RatFunc K) c) = algebraMap K (RatFunc K) c
    exact h_reciprocalRatFuncRingHom_algebraMap_scalar c
  · funext i
    split <;> simp_all

omit [CharZero K] in
/-- Reciprocal substitution sends the conic coordinate `X` to its expression
in the chart at parameter infinity. -/
theorem h_reciprocalRatFuncRingHom_hConicParamX :
    hReciprocalRatFuncRingHom (K := K) (hConicParamX (K := K)) =
      hMinusParamX := by
  simp only [hConicParamX, hConicParamXNumerator,
    hConicParamDenominator, hMinusParamX, hMinusParamXNumerator,
    hMinusParamDenominator, map_div₀,
    h_reciprocalRatFuncRingHom_algebraMap]
  simp [Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X,
    RatFunc.algebraMap_X, map_ofNat]
  field_simp [RatFunc.X_ne_zero]
  ring

/-- Reciprocal substitution sends `w` to its regular expression in the chart
at parameter infinity. -/
theorem h_reciprocalRatFuncRingHom_hConicParamW :
    hReciprocalRatFuncRingHom (K := K) (hConicParamW (K := K)) =
      hMinusParamW := by
  simp only [hConicParamW, hConicParamOneFactor,
    hConicParamWFactor, hConicParamFunctionDenominator,
    hConicParamDenominator, hMinusParamW, hMinusParamWNumerator,
    hMinusParamFunctionDenominator, hMinusParamDenominator,
    map_div₀, h_reciprocalRatFuncRingHom_algebraMap]
  simp [Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X,
    RatFunc.algebraMap_X, map_ofNat]
  field_simp [RatFunc.X_ne_zero]
  ring

/-- Reciprocal substitution sends `W` to its regular expression in the chart
at parameter infinity. -/
theorem h_reciprocalRatFuncRingHom_hConicParamCapitalW :
    hReciprocalRatFuncRingHom (K := K)
        (hConicParamCapitalW (K := K)) =
      hMinusParamCapitalW := by
  simp only [hConicParamCapitalW, hConicParamOneFactor,
    hConicParamCapitalWFactor, hConicParamFunctionDenominator,
    hConicParamDenominator, hMinusParamCapitalW,
    hMinusParamCapitalWNumerator, hMinusParamFunctionDenominator,
    hMinusParamDenominator, map_div₀,
    h_reciprocalRatFuncRingHom_algebraMap]
  simp [Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X,
    RatFunc.algebraMap_X, map_ofNat]
  field_simp [RatFunc.X_ne_zero]
  ring

/-- Reciprocal substitution identifies the conic difference with the regular
expression in the chart at parameter infinity. -/
theorem h_reciprocalRatFuncRingHom_hConicDifference
    (F : MvPolynomial (Fin 2) K) :
    hReciprocalRatFuncRingHom (K := K) (hConicDifference F) =
      hFormEval 1 (hMinusParamW (K := K)) F -
        hFormEval (hMinusParamX (K := K))
          hMinusParamCapitalW F := by
  simp only [hConicDifference, hFirstConicPullback,
    hSecondConicPullback, map_sub,
    h_reciprocalRatFuncRingHom_hFormEval, map_one,
    h_reciprocalRatFuncRingHom_hConicParamX,
    h_reciprocalRatFuncRingHom_hConicParamW,
    h_reciprocalRatFuncRingHom_hConicParamCapitalW]

/-! ## Orders at infinity -/

omit [CharZero K] in
/-- The order at infinity of a polynomial is the negative of its degree. -/
theorem h_order_at_infinity_algebraMap_polynomial
    (p : K[X]) (hp : p ≠ 0) :
    hOrderAtInfinity (algebraMap K[X] (RatFunc K) p) =
      WithZero.exp (-(p.natDegree : ℤ)) := by
  rw [h_order_at_infinity_eq_natDegree_sub _
    (RatFunc.algebraMap_ne_zero hp), RatFunc.denom_algebraMap,
    RatFunc.num_algebraMap, Polynomial.natDegree_one]
  congr
  omega

/-- The order at infinity of a rational function written with the fixed pole
profile denominator is the degree of that denominator minus the numerator
degree. -/
theorem h_order_at_infinity_of_pole_profile_representation
    (a b : ℕ) {f : RatFunc K} {p : K[X]}
    (hp : p ≠ 0)
    (hrepresentation :
      f = algebraMap K[X] (RatFunc K) p /
        algebraMap K[X] (RatFunc K) (hPoleProfileDenominator a b)) :
    hOrderAtInfinity f =
      WithZero.exp (((a + 2 * b : ℕ) : ℤ) - p.natDegree) := by
  rw [hrepresentation, map_div₀,
    h_order_at_infinity_algebraMap_polynomial p hp,
    h_order_at_infinity_algebraMap_polynomial
      (hPoleProfileDenominator (K := K) a b)
      (h_pole_profile_denominator_ne_zero a b),
    h_pole_profile_denominator_natDegree]
  calc
    WithZero.exp (-(p.natDegree : ℤ)) /
        WithZero.exp (-((a + 2 * b : ℕ) : ℤ)) =
      WithZero.exp (-(p.natDegree : ℤ) -
        -((a + 2 * b : ℕ) : ℤ)) :=
        (WithZero.exp_sub _ _).symm
    _ = WithZero.exp (((a + 2 * b : ℕ) : ℤ) - p.natDegree) := by
      apply congrArg WithZero.exp
      ring

/-- A strict loss of numerator degree produces a positive order at the point
at infinity of the parameter line. -/
theorem h_order_at_infinity_positive_of_pole_profile_degree_drop
    (a b : ℕ) {f : RatFunc K} {p : K[X]}
    (hp : p ≠ 0)
    (hdegree : p.natDegree < a + 2 * b)
    (hrepresentation :
      f = algebraMap K[X] (RatFunc K) p /
        algebraMap K[X] (RatFunc K) (hPoleProfileDenominator a b)) :
    ∃ k : ℕ, 1 ≤ k ∧
      hOrderAtInfinity f = WithZero.exp (k : ℤ) := by
  let k := a + 2 * b - p.natDegree
  refine ⟨k, by omega, ?_⟩
  rw [h_order_at_infinity_of_pole_profile_representation a b hp
    hrepresentation]
  apply congrArg WithZero.exp
  simp only [k]
  omega

end OnLeConjecture.DThree
