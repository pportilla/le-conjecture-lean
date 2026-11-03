/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HHardOddPoleExclusion
public import OnLeConjecture.DThree.HFiniteBoundaryCollision

/-!
# The finite boundary alternative for the odd H norm

At a root of `m² + 2`, multiplication by the conic denominator gives a
finite weighted fibre pair. The same rescaling turns the hard norm into the
product of the four sign differences of the odd hard form. A numerator root
therefore gives a projective collision.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- Rescaling by the fourth power of the conic denominator preserves the
displayed hard norm formula. -/
theorem hHardOdd_finite_boundary_scaled_norm_identity
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ) :
    let d : RatFunc ℂ :=
      algebraMap ℂ[X] (RatFunc ℂ) hConicParamDenominator
    let B := d ^ N * hConicDifference Rzero
    d ^ (4 * N) * hHardOddNorm Rzero coefficient N =
      (B ^ 2 + algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2) *
          ((d ^ 2 * hConicParamW) ^ N -
            (d ^ 2 * hConicParamCapitalW) ^ N)) ^ 2 -
        algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2) *
          B ^ 2 * (d ^ 2 * hConicParamW) ^ N := by
  simp only [hHardOddNorm]
  ring

/-- A finite boundary root of the hard norm numerator gives a projective
off diagonal fibre pair for the odd hard form. -/
theorem exists_hard_odd_finite_boundary_fibre_of_norm_numerator_root
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient z : ℂ) (N : ℕ)
    (hNodd : Odd N)
    (hRzero : Rzero.IsWeightedHomogeneous hFormWeight N)
    (numerator : ℂ[X])
    (hrepresentation :
      hHardOddNorm Rzero coefficient N =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (2 * N) (4 * N)))
    (hz : z ^ 2 + 2 = 0) (hroot : numerator.IsRoot z) :
    ∃ x t X T : ℂ,
      x ≠ X ∧
      hP x (t ^ 2) = hP X (T ^ 2) ∧
      hQ x (t ^ 2) = hQ X (T ^ 2) ∧
      hFormEval x (t ^ 2) Rzero + coefficient * t ^ N =
        hFormEval X (T ^ 2) Rzero + coefficient * T ^ N := by
  let d : RatFunc ℂ :=
    algebraMap ℂ[X] (RatFunc ℂ) hConicParamDenominator
  let firstW : RatFunc ℂ :=
    algebraMap ℂ[X] (RatFunc ℂ)
        (-hConicParamOneFactor * hConicParamWFactor) /
      algebraMap ℂ[X] (RatFunc ℂ) hFiniteBoundaryLinear
  let secondW : RatFunc ℂ :=
    algebraMap ℂ[X] (RatFunc ℂ)
        (-hConicParamOneFactor * hConicParamCapitalWFactor) /
      algebraMap ℂ[X] (RatFunc ℂ) hFiniteBoundaryLinear
  let B : RatFunc ℂ := d ^ N * hConicDifference Rzero
  have hlinear := h_finite_boundary_linear_ne_zero hz
  have hdRegular : HRatFuncRegularAt z d := by
    exact hRatFuncRegularAt_algebraMap z hConicParamDenominator
  have hxRegular : HRatFuncRegularAt z
      (algebraMap ℂ[X] (RatFunc ℂ) hConicParamXNumerator) := by
    exact hRatFuncRegularAt_algebraMap z hConicParamXNumerator
  have hfirstWRegular : HRatFuncRegularAt z firstW := by
    exact hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd
        (-hConicParamOneFactor * hConicParamWFactor)
          hFiniteBoundaryLinear) hlinear
  have hsecondWRegular : HRatFuncRegularAt z secondW := by
    exact hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd
        (-hConicParamOneFactor * hConicParamCapitalWFactor)
          hFiniteBoundaryLinear) hlinear
  have hBidentity : B =
      hFormEval d firstW Rzero -
        hFormEval
          (algebraMap ℂ[X] (RatFunc ℂ) hConicParamXNumerator)
            secondW Rzero := by
    dsimp only [B, d, firstW, secondW]
    simpa only [hFiniteBoundaryLinear] using
      h_scaled_infinity_conic_difference Rzero N hRzero
  have hBRegular : HRatFuncRegularAt z B := by
    rw [hBidentity]
    exact hRatFuncRegularAt_sub
      (hRatFuncRegularAt_hFormEval z d firstW Rzero
        hdRegular hfirstWRegular)
      (hRatFuncRegularAt_hFormEval z
        (algebraMap ℂ[X] (RatFunc ℂ) hConicParamXNumerator)
          secondW Rzero hxRegular hsecondWRegular)
  have hfirstWidentity : d ^ 2 * hConicParamW = firstW := by
    dsimp only [d, firstW]
    simpa only [hFiniteBoundaryLinear] using
      (h_conic_param_denominator_sq_mul_w (K := ℂ))
  have hsecondWidentity :
      d ^ 2 * hConicParamCapitalW = secondW := by
    dsimp only [d, secondW]
    simpa only [hFiniteBoundaryLinear] using
      (h_conic_param_denominator_sq_mul_capitalW (K := ℂ))
  have hdenominatorEval :
      (hFiniteBoundaryLinear ^ (2 * N)).eval z ≠ 0 := by
    simpa [Polynomial.eval_pow] using pow_ne_zero (2 * N) hlinear
  have hscaledRepresentation :
      d ^ (4 * N) * hHardOddNorm Rzero coefficient N =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hFiniteBoundaryLinear ^ (2 * N)) := by
    rw [hrepresentation, hPoleProfileDenominator]
    dsimp only [d, hFiniteBoundaryLinear]
    simp only [map_mul, map_pow]
    have hd : algebraMap ℂ[X] (RatFunc ℂ)
        (hConicParamDenominator (K := ℂ)) ≠ 0 :=
      RatFunc.algebraMap_ne_zero h_conic_param_denominator_ne_zero
    have hell : algebraMap ℂ[X] (RatFunc ℂ)
        (3 * (Polynomial.X + 1)) ≠ 0 :=
      RatFunc.algebraMap_ne_zero
        (h_conic_profile_linear_ne_zero (K := ℂ))
    field_simp [hd, hell]
  have hscaledZero : RatFunc.eval (RingHom.id ℂ) z
      (d ^ (4 * N) * hHardOddNorm Rzero coefficient N) = 0 := by
    have heval := congrArg (RatFunc.eval (RingHom.id ℂ) z)
      hscaledRepresentation
    rw [h_ratFunc_eval_algebraMap_div z numerator
      (hFiniteBoundaryLinear ^ (2 * N)) hdenominatorEval] at heval
    have hnumerator : numerator.eval z = 0 := hroot
    rw [hnumerator, zero_div] at heval
    exact heval
  have hscaledIdentity := hHardOdd_finite_boundary_scaled_norm_identity
    Rzero coefficient N
  have hformulaZero :
      (RatFunc.eval (RingHom.id ℂ) z B ^ 2 +
          coefficient ^ 2 *
            (RatFunc.eval (RingHom.id ℂ) z firstW ^ N -
              RatFunc.eval (RingHom.id ℂ) z secondW ^ N)) ^ 2 -
        (4 * coefficient ^ 2) *
          RatFunc.eval (RingHom.id ℂ) z B ^ 2 *
            RatFunc.eval (RingHom.id ℂ) z firstW ^ N = 0 := by
    rw [hscaledIdentity, hfirstWidentity, hsecondWidentity] at hscaledZero
    let cTwo : RatFunc ℂ :=
      algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2)
    let cFour : RatFunc ℂ :=
      algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2)
    have hcTwo : HRatFuncRegularAt z cTwo := by
      change HRatFuncRegularAt z (RatFunc.C (coefficient ^ 2))
      exact hRatFuncRegularAt_C z _
    have hcFour : HRatFuncRegularAt z cFour := by
      change HRatFuncRegularAt z (RatFunc.C (4 * coefficient ^ 2))
      exact hRatFuncRegularAt_C z _
    have hBsq := hRatFuncRegularAt_pow hBRegular 2
    have hwpow := hRatFuncRegularAt_pow hfirstWRegular N
    have hWpow := hRatFuncRegularAt_pow hsecondWRegular N
    have hpowers := hRatFuncRegularAt_sub hwpow hWpow
    have hscaledPowers := hRatFuncRegularAt_mul hcTwo hpowers
    have hmiddle := hRatFuncRegularAt_add hBsq hscaledPowers
    have hleft := hRatFuncRegularAt_pow hmiddle 2
    have hright := hRatFuncRegularAt_mul
      (hRatFuncRegularAt_mul hcFour hBsq) hwpow
    have hcTwoEval : RatFunc.eval (RingHom.id ℂ) z
        (algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2)) =
          coefficient ^ 2 := by
      change RatFunc.eval (RingHom.id ℂ) z
        (RatFunc.C (coefficient ^ 2)) = coefficient ^ 2
      rw [RatFunc.eval_C]
      rfl
    have hcFourEval : RatFunc.eval (RingHom.id ℂ) z
        (algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2)) =
          4 * coefficient ^ 2 := by
      change RatFunc.eval (RingHom.id ℂ) z
        (RatFunc.C (4 * coefficient ^ 2)) = 4 * coefficient ^ 2
      rw [RatFunc.eval_C]
      rfl
    rw [h_ratFunc_eval_sub z _ _ hleft hright,
      h_ratFunc_eval_pow z _ hmiddle,
      h_ratFunc_eval_add_regular z _ _ hBsq hscaledPowers,
      h_ratFunc_eval_pow z B hBRegular,
      h_ratFunc_eval_mul_regular z _ _ hcTwo hpowers,
      h_ratFunc_eval_sub z _ _ hwpow hWpow,
      h_ratFunc_eval_pow z firstW hfirstWRegular,
      h_ratFunc_eval_pow z secondW hsecondWRegular,
      h_ratFunc_eval_mul_regular z _ _
        (hRatFuncRegularAt_mul hcFour hBsq) hwpow,
      h_ratFunc_eval_mul_regular z _ _ hcFour hBsq,
      h_ratFunc_eval_pow z B hBRegular,
      h_ratFunc_eval_pow z firstW hfirstWRegular,
      hcTwoEval, hcFourEval] at hscaledZero
    exact hscaledZero
  obtain ⟨t, T, ht, hT, hsection⟩ :=
    exists_signs_hard_difference_zero_of_formula_zero
      coefficient (RatFunc.eval (RingHom.id ℂ) z B)
        (RatFunc.eval (RingHom.id ℂ) z firstW)
        (RatFunc.eval (RingHom.id ℂ) z secondW) N hNodd
          hformulaZero
  have hfirstWEval : RatFunc.eval (RingHom.id ℂ) z firstW =
      hFiniteBoundaryW z 0 := by
    dsimp only [firstW, hFiniteBoundaryW]
    rw [h_ratFunc_eval_algebraMap_div z
      (-hConicParamOneFactor * hConicParamWFactor)
        hFiniteBoundaryLinear hlinear]
    simp only [add_zero]
  have hsecondWEval : RatFunc.eval (RingHom.id ℂ) z secondW =
      hFiniteBoundaryCapitalW z 0 := by
    dsimp only [secondW, hFiniteBoundaryCapitalW]
    rw [h_ratFunc_eval_algebraMap_div z
      (-hConicParamOneFactor * hConicParamCapitalWFactor)
        hFiniteBoundaryLinear hlinear]
    simp only [add_zero]
  have hBEval : RatFunc.eval (RingHom.id ℂ) z B =
      hFormEval (hFiniteBoundaryFirstX z 0)
          (hFiniteBoundaryW z 0) Rzero -
        hFormEval (hFiniteBoundarySecondX z 0)
          (hFiniteBoundaryCapitalW z 0) Rzero := by
    rw [hBidentity,
      h_ratFunc_eval_sub z _ _
        (hRatFuncRegularAt_hFormEval z d firstW Rzero
          hdRegular hfirstWRegular)
        (hRatFuncRegularAt_hFormEval z
          (algebraMap ℂ[X] (RatFunc ℂ) hConicParamXNumerator)
            secondW Rzero hxRegular hsecondWRegular),
      h_ratFunc_eval_hFormEval z d firstW Rzero
        hdRegular hfirstWRegular,
      h_ratFunc_eval_hFormEval z
        (algebraMap ℂ[X] (RatFunc ℂ) hConicParamXNumerator)
          secondW Rzero hxRegular hsecondWRegular,
      h_ratFunc_eval_algebraMap_id,
      h_ratFunc_eval_algebraMap_id z hConicParamXNumerator,
      hfirstWEval, hsecondWEval]
    simp only [hFiniteBoundaryFirstX,
      hFiniteBoundarySecondX, add_zero]
  have hfibre := h_finite_boundary_fibre_at z hlinear
  have ht' : t ^ 2 = hFiniteBoundaryW z 0 := by
    rw [← hfirstWEval]
    exact ht
  have hT' : T ^ 2 = hFiniteBoundaryCapitalW z 0 := by
    rw [← hsecondWEval]
    exact hT
  have hfibre' :
      hP (hFiniteBoundaryFirstX z 0) (t ^ 2) =
          hP (hFiniteBoundarySecondX z 0) (T ^ 2) ∧
        hQ (hFiniteBoundaryFirstX z 0) (t ^ 2) =
          hQ (hFiniteBoundarySecondX z 0) (T ^ 2) := by
    rw [ht', hT']
    simpa [hFiniteBoundaryFirstX, hFiniteBoundaryW,
      hFiniteBoundarySecondX, hFiniteBoundaryCapitalW] using hfibre
  have hdistinct : hFiniteBoundaryFirstX z 0 ≠
      hFiniteBoundarySecondX z 0 := by
    have hfirst : hFiniteBoundaryFirstX z 0 = 0 := by
      simpa [hFiniteBoundaryFirstX, hConicParamDenominator] using hz
    have hsecond : hFiniteBoundarySecondX z 0 ≠ 0 := by
      simpa only [hFiniteBoundarySecondX, add_zero,
        hConicParamXNumerator, Polynomial.eval_neg, Polynomial.eval_add,
        Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat] using
          h_conic_param_x_numerator_at_infinity_ne_zero (K := ℂ) hz
    rw [hfirst]
    exact hsecond.symm
  have hthird :
      hFormEval (hFiniteBoundaryFirstX z 0) (t ^ 2) Rzero +
          coefficient * t ^ N =
        hFormEval (hFiniteBoundarySecondX z 0) (T ^ 2) Rzero +
          coefficient * T ^ N := by
    rw [hBEval] at hsection
    rw [ht', hT']
    linear_combination hsection
  exact ⟨hFiniteBoundaryFirstX z 0, t,
    hFiniteBoundarySecondX z 0, T, hdistinct,
      hfibre'.1, hfibre'.2, hthird⟩

end OnLeConjecture.DThree
