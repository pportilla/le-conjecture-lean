/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HHardOddInfinityBranch
public import OnLeConjecture.DThree.HHardOddFiniteBoundary

/-!
# Ordinary hard H branches at the finite parametrization boundary

At a root of the conic parameter denominator, multiplying by its homogeneous
weight gives finite analytic source coordinates. The scaled hard norm is the
product of the four analytic sign differences in these coordinates.
-/

public section

noncomputable section

open Filter Set
open scoped Topology Polynomial

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- Evaluation of the scaled hard norm at finite boundary coordinates has
the scalar hard norm formula. -/
theorem h_finite_boundary_scaled_hHardOddNorm_eval_eq_formula
    (Rzero : Form ℂ) (coefficient m : ℂ) (N : ℕ)
    (hRzero : Rzero.IsWeightedHomogeneous hFormWeight N)
    (hlinear : hFiniteBoundaryLinear.eval m ≠ 0) :
    let d : RatFunc ℂ :=
      algebraMap ℂ[X] (RatFunc ℂ) hConicParamDenominator
    RatFunc.eval (RingHom.id ℂ) m
        (d ^ (4 * N) * hHardOddNorm Rzero coefficient N) =
      ((hFormEval (hConicParamDenominator.eval m)
              ((-hConicParamOneFactor * hConicParamWFactor).eval m /
                hFiniteBoundaryLinear.eval m) Rzero -
            hFormEval (hConicParamXNumerator.eval m)
              ((-hConicParamOneFactor * hConicParamCapitalWFactor).eval m /
                hFiniteBoundaryLinear.eval m) Rzero) ^ 2 +
          coefficient ^ 2 *
            (((-hConicParamOneFactor * hConicParamWFactor).eval m /
                hFiniteBoundaryLinear.eval m) ^ N -
              ((-hConicParamOneFactor *
                    hConicParamCapitalWFactor).eval m /
                hFiniteBoundaryLinear.eval m) ^ N)) ^ 2 -
        (4 * coefficient ^ 2) *
          (hFormEval (hConicParamDenominator.eval m)
                ((-hConicParamOneFactor * hConicParamWFactor).eval m /
                  hFiniteBoundaryLinear.eval m) Rzero -
              hFormEval (hConicParamXNumerator.eval m)
                ((-hConicParamOneFactor *
                      hConicParamCapitalWFactor).eval m /
                  hFiniteBoundaryLinear.eval m) Rzero) ^ 2 *
          ((-hConicParamOneFactor * hConicParamWFactor).eval m /
            hFiniteBoundaryLinear.eval m) ^ N := by
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
  have hdRegular : HRatFuncRegularAt m d :=
    hRatFuncRegularAt_algebraMap m hConicParamDenominator
  have hxRegular : HRatFuncRegularAt m
      (algebraMap ℂ[X] (RatFunc ℂ) hConicParamXNumerator) :=
    hRatFuncRegularAt_algebraMap m hConicParamXNumerator
  have hfirstWRegular : HRatFuncRegularAt m firstW :=
    hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd
        (-hConicParamOneFactor * hConicParamWFactor)
          hFiniteBoundaryLinear) hlinear
  have hsecondWRegular : HRatFuncRegularAt m secondW :=
    hRatFuncRegularAt_of_denom_dvd
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
  have hBRegular : HRatFuncRegularAt m B := by
    rw [hBidentity]
    exact hRatFuncRegularAt_sub
      (hRatFuncRegularAt_hFormEval m d firstW Rzero
        hdRegular hfirstWRegular)
      (hRatFuncRegularAt_hFormEval m
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
  have hscaledIdentity := hHardOdd_finite_boundary_scaled_norm_identity
    Rzero coefficient N
  change d ^ (4 * N) * hHardOddNorm Rzero coefficient N =
      (B ^ 2 + algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2) *
          ((d ^ 2 * hConicParamW) ^ N -
            (d ^ 2 * hConicParamCapitalW) ^ N)) ^ 2 -
        algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2) *
          B ^ 2 * (d ^ 2 * hConicParamW) ^ N at hscaledIdentity
  rw [hfirstWidentity, hsecondWidentity] at hscaledIdentity
  have hcTwo : HRatFuncRegularAt m
      (algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2)) := by
    change HRatFuncRegularAt m (RatFunc.C (coefficient ^ 2))
    exact hRatFuncRegularAt_C m _
  have hcFour : HRatFuncRegularAt m
      (algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2)) := by
    change HRatFuncRegularAt m (RatFunc.C (4 * coefficient ^ 2))
    exact hRatFuncRegularAt_C m _
  have hBsq := hRatFuncRegularAt_pow hBRegular 2
  have hwpow := hRatFuncRegularAt_pow hfirstWRegular N
  have hWpow := hRatFuncRegularAt_pow hsecondWRegular N
  have hpowers := hRatFuncRegularAt_sub hwpow hWpow
  have hscaledPowers := hRatFuncRegularAt_mul hcTwo hpowers
  have hmiddle := hRatFuncRegularAt_add hBsq hscaledPowers
  have hleft := hRatFuncRegularAt_pow hmiddle 2
  have hright := hRatFuncRegularAt_mul
    (hRatFuncRegularAt_mul hcFour hBsq) hwpow
  have heval := congrArg (RatFunc.eval (RingHom.id ℂ) m)
    hscaledIdentity
  have hcTwoEval : RatFunc.eval (RingHom.id ℂ) m
      (algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2)) =
        coefficient ^ 2 := by
    change RatFunc.eval (RingHom.id ℂ) m
      (RatFunc.C (coefficient ^ 2)) = coefficient ^ 2
    rw [RatFunc.eval_C]
    rfl
  have hcFourEval : RatFunc.eval (RingHom.id ℂ) m
      (algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2)) =
        4 * coefficient ^ 2 := by
    change RatFunc.eval (RingHom.id ℂ) m
      (RatFunc.C (4 * coefficient ^ 2)) = 4 * coefficient ^ 2
    rw [RatFunc.eval_C]
    rfl
  rw [h_ratFunc_eval_sub m _ _ hleft hright,
    h_ratFunc_eval_pow m _ hmiddle,
    h_ratFunc_eval_add_regular m _ _ hBsq hscaledPowers,
    h_ratFunc_eval_pow m B hBRegular,
    h_ratFunc_eval_mul_regular m _ _ hcTwo hpowers,
    h_ratFunc_eval_sub m _ _ hwpow hWpow,
    h_ratFunc_eval_pow m firstW hfirstWRegular,
    h_ratFunc_eval_pow m secondW hsecondWRegular,
    h_ratFunc_eval_mul_regular m _ _
      (hRatFuncRegularAt_mul hcFour hBsq) hwpow,
    h_ratFunc_eval_mul_regular m _ _ hcFour hBsq,
    h_ratFunc_eval_pow m B hBRegular,
    h_ratFunc_eval_pow m firstW hfirstWRegular,
    hcTwoEval, hcFourEval] at heval
  have hfirstWEval : RatFunc.eval (RingHom.id ℂ) m firstW =
      (-hConicParamOneFactor * hConicParamWFactor).eval m /
        hFiniteBoundaryLinear.eval m := by
    dsimp only [firstW]
    exact h_ratFunc_eval_algebraMap_div m
      (-hConicParamOneFactor * hConicParamWFactor)
        hFiniteBoundaryLinear hlinear
  have hsecondWEval : RatFunc.eval (RingHom.id ℂ) m secondW =
      (-hConicParamOneFactor * hConicParamCapitalWFactor).eval m /
        hFiniteBoundaryLinear.eval m := by
    dsimp only [secondW]
    exact h_ratFunc_eval_algebraMap_div m
      (-hConicParamOneFactor * hConicParamCapitalWFactor)
        hFiniteBoundaryLinear hlinear
  have hBEval : RatFunc.eval (RingHom.id ℂ) m B =
      hFormEval (hConicParamDenominator.eval m)
          ((-hConicParamOneFactor * hConicParamWFactor).eval m /
            hFiniteBoundaryLinear.eval m) Rzero -
        hFormEval (hConicParamXNumerator.eval m)
          ((-hConicParamOneFactor * hConicParamCapitalWFactor).eval m /
            hFiniteBoundaryLinear.eval m) Rzero := by
    rw [hBidentity,
      h_ratFunc_eval_sub m _ _
        (hRatFuncRegularAt_hFormEval m d firstW Rzero
          hdRegular hfirstWRegular)
        (hRatFuncRegularAt_hFormEval m
          (algebraMap ℂ[X] (RatFunc ℂ) hConicParamXNumerator)
            secondW Rzero hxRegular hsecondWRegular),
      h_ratFunc_eval_hFormEval m d firstW Rzero
        hdRegular hfirstWRegular,
      h_ratFunc_eval_hFormEval m
        (algebraMap ℂ[X] (RatFunc ℂ) hConicParamXNumerator)
          secondW Rzero hxRegular hsecondWRegular,
      h_ratFunc_eval_algebraMap_id,
      h_ratFunc_eval_algebraMap_id m hConicParamXNumerator,
      hfirstWEval, hsecondWEval]
  rw [hfirstWEval, hsecondWEval, hBEval] at heval
  change RatFunc.eval (RingHom.id ℂ) m
      (d ^ (4 * N) * hHardOddNorm Rzero coefficient N) = _
  exact heval

/-- The hard norm representation after cancelling the conic denominator at
the finite boundary. -/
theorem hHardOdd_finite_boundary_scaled_representation
    (Rzero : Form ℂ) (coefficient : ℂ) (N : ℕ)
    (numerator : ℂ[X])
    (hrepresentation :
      hHardOddNorm Rzero coefficient N =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (2 * N) (4 * N))) :
    let d : RatFunc ℂ :=
      algebraMap ℂ[X] (RatFunc ℂ) hConicParamDenominator
    d ^ (4 * N) * hHardOddNorm Rzero coefficient N =
      algebraMap ℂ[X] (RatFunc ℂ) numerator /
        algebraMap ℂ[X] (RatFunc ℂ)
          (hFiniteBoundaryLinear ^ (2 * N)) := by
  let d : RatFunc ℂ :=
    algebraMap ℂ[X] (RatFunc ℂ) hConicParamDenominator
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

set_option maxHeartbeats 600000 in
-- The scalar formula produces a large rational expression during elaboration.
/-- A numerator root at the finite boundary selects square roots for which
the hard section difference vanishes. -/
theorem exists_hard_odd_finite_boundary_signs_of_norm_numerator_root
    (Rzero : Form ℂ) (coefficient z : ℂ) (N : ℕ)
    (hNodd : Odd N)
    (hRzero : Rzero.IsWeightedHomogeneous hFormWeight N)
    (numerator : ℂ[X])
    (hrepresentation :
      hHardOddNorm Rzero coefficient N =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (2 * N) (4 * N)))
    (hz : z ^ 2 + 2 = 0) (hroot : numerator.IsRoot z) :
    ∃ s S : ℂ,
      s ^ 2 = hFiniteBoundaryW z 0 ∧
      S ^ 2 = hFiniteBoundaryCapitalW z 0 ∧
      hFormEval (hFiniteBoundaryFirstX z 0)
            (hFiniteBoundaryW z 0) Rzero -
          hFormEval (hFiniteBoundarySecondX z 0)
            (hFiniteBoundaryCapitalW z 0) Rzero +
        coefficient * (s ^ N - S ^ N) = 0 := by
  let d : RatFunc ℂ :=
    algebraMap ℂ[X] (RatFunc ℂ) hConicParamDenominator
  have hlinear := h_finite_boundary_linear_ne_zero hz
  have hdenominatorEval :
      (hFiniteBoundaryLinear ^ (2 * N)).eval z ≠ 0 := by
    simpa only [Polynomial.eval_pow] using
      pow_ne_zero (2 * N) hlinear
  have hscaledRepresentation :=
    hHardOdd_finite_boundary_scaled_representation
      Rzero coefficient N numerator hrepresentation
  have hscaledZero : RatFunc.eval (RingHom.id ℂ) z
      (d ^ (4 * N) * hHardOddNorm Rzero coefficient N) = 0 := by
    have heval := congrArg (RatFunc.eval (RingHom.id ℂ) z)
      hscaledRepresentation
    rw [h_ratFunc_eval_algebraMap_div z numerator
      (hFiniteBoundaryLinear ^ (2 * N)) hdenominatorEval] at heval
    rw [show numerator.eval z = 0 by exact hroot, zero_div] at heval
    exact heval
  let A : ℂ :=
    hFormEval (hConicParamDenominator.eval z)
        ((-hConicParamOneFactor * hConicParamWFactor).eval z /
          hFiniteBoundaryLinear.eval z) Rzero -
      hFormEval (hConicParamXNumerator.eval z)
        ((-hConicParamOneFactor * hConicParamCapitalWFactor).eval z /
          hFiniteBoundaryLinear.eval z) Rzero
  let w : ℂ :=
    (-hConicParamOneFactor * hConicParamWFactor).eval z /
      hFiniteBoundaryLinear.eval z
  let W : ℂ :=
    (-hConicParamOneFactor * hConicParamCapitalWFactor).eval z /
      hFiniteBoundaryLinear.eval z
  have hformula :=
    h_finite_boundary_scaled_hHardOddNorm_eval_eq_formula
      Rzero coefficient z N hRzero hlinear
  dsimp only at hformula
  dsimp only [d] at hscaledZero
  rw [hscaledZero] at hformula
  have hformulaZero :
      (A ^ 2 + coefficient ^ 2 * (w ^ N - W ^ N)) ^ 2 -
        (4 * coefficient ^ 2) * A ^ 2 * w ^ N = 0 := by
    simpa only [A, w, W] using hformula.symm
  obtain ⟨s, S, hs, hS, hsection⟩ :=
    exists_signs_hard_difference_zero_of_formula_zero coefficient
      A w W N hNodd hformulaZero
  exact ⟨s, S, by simpa only [hFiniteBoundaryW, add_zero] using hs,
    by simpa only [hFiniteBoundaryCapitalW, add_zero] using hS,
    by simpa only [hFiniteBoundaryFirstX, hFiniteBoundaryW,
      hFiniteBoundarySecondX, hFiniteBoundaryCapitalW, A, w, W, add_zero]
      using hsection⟩

/-- Ordinary homogeneity normalizes an arbitrary pair by the first second
coordinate. -/
theorem normalized_ordinary_form_difference_general
    (R : Form ℂ) (N : ℕ) (hR : R.IsHomogeneous N)
    (x y X Y : ℂ) (hy : y ≠ 0) :
    MvPolynomial.eval ![x / y, 1] R -
        MvPolynomial.eval ![X / y, Y / y] R =
      (MvPolynomial.eval ![x, y] R -
        MvPolynomial.eval ![X, Y] R) / y ^ N := by
  have hweights : (![1, 1] : Fin 2 → ℕ) = 1 := by
    funext i
    fin_cases i
    all_goals rfl
  have hRweighted : R.IsWeightedHomogeneous ![1, 1] N := by
    rw [hweights]
    exact hR
  have hfirst := eval_weighted_smul_of_isWeightedHomogeneous
    hRweighted y ![x / y, 1]
  have hsecond := eval_weighted_smul_of_isWeightedHomogeneous
    hRweighted y ![X / y, Y / y]
  have hfirstCoordinates :
      (fun i : Fin 2 ↦ y ^ (![1, 1] : Fin 2 → ℕ) i *
        (![x / y, 1] : Fin 2 → ℂ) i) = ![x, y] := by
    funext i
    fin_cases i
    · simp [mul_div_cancel₀ x hy]
    · simp
  have hsecondCoordinates :
      (fun i : Fin 2 ↦ y ^ (![1, 1] : Fin 2 → ℕ) i *
        (![X / y, Y / y] : Fin 2 → ℂ) i) = ![X, Y] := by
    funext i
    fin_cases i
    · simp [mul_div_cancel₀ X hy]
    · simp [mul_div_cancel₀ Y hy]
  rw [hfirstCoordinates] at hfirst
  rw [hsecondCoordinates] at hsecond
  apply (eq_div_iff (pow_ne_zero N hy)).2
  calc
    (MvPolynomial.eval ![x / y, 1] R -
          MvPolynomial.eval ![X / y, Y / y] R) * y ^ N =
        y ^ N * MvPolynomial.eval ![x / y, 1] R -
          y ^ N * MvPolynomial.eval ![X / y, Y / y] R := by ring
    _ = MvPolynomial.eval ![x, y] R -
        MvPolynomial.eval ![X, Y] R := by
      rw [← hfirst, ← hsecond]

/-- A finite boundary numerator root gives ordinary source branch data. -/
theorem exists_hHardOddOrdinarySourceBranchData_of_finite_boundary_root
    (R Rzero : Form ℂ) (coefficient : ℂ) (N : ℕ)
    (hR : R.IsHomogeneous N)
    (hdecomposition :
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N)
    (hNodd : Odd N)
    (hRzero : Rzero.IsWeightedHomogeneous hFormWeight N)
    (numerator : ℂ[X]) (hnumerator : numerator ≠ 0)
    (z : ℂ) (hz : z ^ 2 + 2 = 0) (hroot : numerator.IsRoot z)
    (hrepresentation :
      hHardOddNorm Rzero coefficient N =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (2 * N) (4 * N))) :
    Nonempty (HHardOddOrdinarySourceBranchData R) := by
  have hlinear := h_finite_boundary_linear_ne_zero hz
  have hwNumerator :
      (-hConicParamOneFactor * hConicParamWFactor).eval z ≠ 0 := by
    simpa only [Polynomial.eval_mul, Polynomial.eval_neg,
      hConicParamOneFactor, hConicParamWFactor,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_ofNat] using
      h_conic_param_w_numerator_at_infinity_ne_zero (K := ℂ) hz
  have hcapitalWNumerator :
      (-hConicParamOneFactor * hConicParamCapitalWFactor).eval z ≠ 0 := by
    simpa only [Polynomial.eval_mul, Polynomial.eval_neg,
      hConicParamOneFactor, hConicParamCapitalWFactor,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_ofNat] using
      h_conic_param_capitalW_numerator_at_infinity_ne_zero (K := ℂ) hz
  have hw0 : hFiniteBoundaryW z 0 ≠ 0 := by
    simpa only [hFiniteBoundaryW, add_zero] using
      div_ne_zero hwNumerator hlinear
  have hcapitalW0 : hFiniteBoundaryCapitalW z 0 ≠ 0 := by
    simpa only [hFiniteBoundaryCapitalW, add_zero] using
      div_ne_zero hcapitalWNumerator hlinear
  have hfirstX0 : hFiniteBoundaryFirstX z 0 = 0 := by
    simp only [hFiniteBoundaryFirstX, add_zero, hConicParamDenominator,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    exact hz
  have hsecondX0 : hFiniteBoundarySecondX z 0 ≠ 0 := by
    simpa only [hFiniteBoundarySecondX, add_zero,
      hConicParamXNumerator, Polynomial.eval_neg, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat] using
      h_conic_param_x_numerator_at_infinity_ne_zero (K := ℂ) hz
  obtain ⟨s, S, hs, hS, hsection⟩ :=
    exists_hard_odd_finite_boundary_signs_of_norm_numerator_root
      Rzero coefficient z N hNodd hRzero numerator hrepresentation hz hroot
  have hs0 : s ≠ 0 := by
    intro hsZero
    apply hw0
    rw [← hs, hsZero, zero_pow (by norm_num : 2 ≠ 0)]
  have hS0 : S ≠ 0 := by
    intro hSZero
    apply hcapitalW0
    rw [← hS, hSZero, zero_pow (by norm_num : 2 ≠ 0)]
  obtain ⟨y, hyAnalytic, hyZero, hyPower⟩ :=
    exists_analyticAt_root_with_value
      (hFiniteBoundaryW z) (analyticAt_hFiniteBoundaryW z hlinear)
        hw0 2 (by norm_num) s hs
  obtain ⟨Y, hYAnalytic, hYZero, hYPower⟩ :=
    exists_analyticAt_root_with_value
      (hFiniteBoundaryCapitalW z)
        (analyticAt_hFiniteBoundaryCapitalW z hlinear)
          hcapitalW0 2 (by norm_num) S hS
  let raw : ℂ → ℂ := fun lambda ↦
    hFormEval (hFiniteBoundaryFirstX z lambda)
          (hFiniteBoundaryW z lambda) Rzero -
      hFormEval (hFiniteBoundarySecondX z lambda)
          (hFiniteBoundaryCapitalW z lambda) Rzero +
      coefficient * (y lambda ^ N - Y lambda ^ N)
  have hrawAnalytic : AnalyticAt ℂ raw 0 := by
    dsimp only [raw]
    have hfirst := analyticAt_eval_finTwo Rzero
      (hFiniteBoundaryFirstX z) (hFiniteBoundaryW z)
      (analyticAt_hFiniteBoundaryFirstX z)
      (analyticAt_hFiniteBoundaryW z hlinear)
    have hsecond := analyticAt_eval_finTwo Rzero
      (hFiniteBoundarySecondX z) (hFiniteBoundaryCapitalW z)
      (analyticAt_hFiniteBoundarySecondX z)
      (analyticAt_hFiniteBoundaryCapitalW z hlinear)
    have hsum := (hfirst.sub hsecond).add
      ((analyticAt_const : AnalyticAt ℂ
          (fun _ : ℂ ↦ coefficient) 0).mul
        ((hyAnalytic.pow N).sub (hYAnalytic.pow N)))
    convert hsum using 1
    funext lambda
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
      hFormEval_eq_eval_finTwo]
  have hrawZero : raw 0 = 0 := by
    simpa only [raw, hyZero, hYZero] using hsection
  have hlinearEventually : ∀ᶠ lambda in nhds 0,
      hFiniteBoundaryLinear.eval (z + lambda) ≠ 0 := by
    have ht : Tendsto
        (fun lambda : ℂ ↦ hFiniteBoundaryLinear.eval (z + lambda))
        (nhds 0) (nhds (hFiniteBoundaryLinear.eval z)) := by
      have hc :=
        (analyticAt_polynomial_eval_add hFiniteBoundaryLinear z).continuousAt
      change Tendsto
        (fun lambda : ℂ ↦ hFiniteBoundaryLinear.eval (z + lambda))
        (nhds 0)
        (nhds (hFiniteBoundaryLinear.eval (z + 0))) at hc
      simpa using hc
    exact ht.eventually_ne hlinear
  let secondFactor : ℂ → ℂ := fun lambda ↦
    hFormEval (hFiniteBoundaryFirstX z lambda)
          (hFiniteBoundaryW z lambda) Rzero -
      hFormEval (hFiniteBoundarySecondX z lambda)
          (hFiniteBoundaryCapitalW z lambda) Rzero +
      coefficient * (y lambda ^ N + Y lambda ^ N)
  let thirdFactor : ℂ → ℂ := fun lambda ↦
    hFormEval (hFiniteBoundaryFirstX z lambda)
          (hFiniteBoundaryW z lambda) Rzero -
      hFormEval (hFiniteBoundarySecondX z lambda)
          (hFiniteBoundaryCapitalW z lambda) Rzero +
      coefficient * (-y lambda ^ N - Y lambda ^ N)
  let fourthFactor : ℂ → ℂ := fun lambda ↦
    hFormEval (hFiniteBoundaryFirstX z lambda)
          (hFiniteBoundaryW z lambda) Rzero -
      hFormEval (hFiniteBoundarySecondX z lambda)
          (hFiniteBoundaryCapitalW z lambda) Rzero +
      coefficient * (-y lambda ^ N + Y lambda ^ N)
  have hnormProduct : ∀ᶠ lambda in nhds 0,
      RatFunc.eval (RingHom.id ℂ) (z + lambda)
          ((algebraMap ℂ[X] (RatFunc ℂ) hConicParamDenominator) ^
              (4 * N) * hHardOddNorm Rzero coefficient N) =
        raw lambda * secondFactor lambda * thirdFactor lambda *
          fourthFactor lambda := by
    filter_upwards [hlinearEventually] with lambda hlinearAt
    have hformula :=
      h_finite_boundary_scaled_hHardOddNorm_eval_eq_formula
        Rzero coefficient (z + lambda) N hRzero hlinearAt
    dsimp only at hformula
    have hformula' :
        RatFunc.eval (RingHom.id ℂ) (z + lambda)
            ((algebraMap ℂ[X] (RatFunc ℂ) hConicParamDenominator) ^
                (4 * N) * hHardOddNorm Rzero coefficient N) =
          ((hFormEval (hFiniteBoundaryFirstX z lambda)
                    (hFiniteBoundaryW z lambda) Rzero -
                  hFormEval (hFiniteBoundarySecondX z lambda)
                    (hFiniteBoundaryCapitalW z lambda) Rzero) ^ 2 +
              coefficient ^ 2 *
                (hFiniteBoundaryW z lambda ^ N -
                  hFiniteBoundaryCapitalW z lambda ^ N)) ^ 2 -
            (4 * coefficient ^ 2) *
              (hFormEval (hFiniteBoundaryFirstX z lambda)
                    (hFiniteBoundaryW z lambda) Rzero -
                  hFormEval (hFiniteBoundarySecondX z lambda)
                    (hFiniteBoundaryCapitalW z lambda) Rzero) ^ 2 *
              hFiniteBoundaryW z lambda ^ N := by
      simpa only [hFiniteBoundaryFirstX, hFiniteBoundaryW,
        hFiniteBoundarySecondX, hFiniteBoundaryCapitalW] using hformula
    have hproduct := hHardOddNorm_eq_sign_product coefficient
      (y lambda) (Y lambda) N
      (hFormEval (hFiniteBoundaryFirstX z lambda)
            (hFiniteBoundaryW z lambda) Rzero -
        hFormEval (hFiniteBoundarySecondX z lambda)
          (hFiniteBoundaryCapitalW z lambda) Rzero)
      (hFiniteBoundaryW z lambda)
      (hFiniteBoundaryCapitalW z lambda)
      (hyPower lambda) (hYPower lambda)
    simpa only [raw, secondFactor, thirdFactor, fourthFactor] using
      hformula'.trans hproduct.symm
  have hscaledRepresentation :=
    hHardOdd_finite_boundary_scaled_representation
      Rzero coefficient N numerator hrepresentation
  dsimp only at hscaledRepresentation
  have hrawNotZero : ¬ ∀ᶠ lambda in nhds 0, raw lambda = 0 := by
    intro hrawEventually
    have hnormZero : ∀ᶠ lambda in nhds 0,
        RatFunc.eval (RingHom.id ℂ) (z + lambda)
          ((algebraMap ℂ[X] (RatFunc ℂ) hConicParamDenominator) ^
              (4 * N) * hHardOddNorm Rzero coefficient N) = 0 := by
      filter_upwards [hnormProduct, hrawEventually] with
        lambda hproduct hrawAt
      rw [hproduct, hrawAt]
      simp
    have hnumeratorZero : ∀ᶠ lambda in nhds 0,
        numerator.eval (z + lambda) = 0 := by
      filter_upwards [hnormZero, hlinearEventually] with
        lambda hnormAt hlinearAt
      have hdenominatorAt :
          (hFiniteBoundaryLinear ^ (2 * N)).eval (z + lambda) ≠ 0 := by
        simpa only [Polynomial.eval_pow] using
          pow_ne_zero (2 * N) hlinearAt
      have heval := congrArg
        (RatFunc.eval (RingHom.id ℂ) (z + lambda))
          hscaledRepresentation
      rw [h_ratFunc_eval_algebraMap_div (z + lambda) numerator
        (hFiniteBoundaryLinear ^ (2 * N)) hdenominatorAt] at heval
      rw [hnormAt] at heval
      exact (div_eq_zero_iff.mp heval.symm).resolve_right hdenominatorAt
    exact (not_eventually_polynomial_eval_add_eq_zero
      numerator hnumerator z) hnumeratorZero
  obtain ⟨order, rawUnit, hrawUnitAnalytic, hrawUnitZero,
      hrawFactorRaw⟩ :=
    hrawAnalytic.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hrawNotZero
  have hrawFactor : ∀ᶠ lambda in nhds 0,
      raw lambda = lambda ^ order * rawUnit lambda := by
    simpa only [sub_zero, smul_eq_mul] using hrawFactorRaw
  have horder : 0 < order := by
    apply Nat.pos_of_ne_zero
    intro horderZero
    have hfactorAt := hrawFactor.self_of_nhds
    rw [horderZero, pow_zero, one_mul, hrawZero] at hfactorAt
    exact hrawUnitZero hfactorAt.symm
  let firstX : ℂ → ℂ := fun lambda ↦
    hFiniteBoundaryFirstX z lambda / y lambda
  let secondPoint : ℂ → Fin 2 → ℂ := fun lambda ↦
    ![hFiniteBoundarySecondX z lambda / y lambda,
      Y lambda / y lambda]
  let secondX : ℂ := hFiniteBoundarySecondX z 0 / s
  let secondT : ℂ := S / s
  let unit : ℂ → ℂ := fun lambda ↦ rawUnit lambda / y lambda ^ N
  have hfirstXAnalytic : AnalyticAt ℂ firstX 0 := by
    exact (analyticAt_hFiniteBoundaryFirstX z).div hyAnalytic
      (by simpa only [hyZero] using hs0)
  have hsecondPointAnalytic : AnalyticAt ℂ secondPoint 0 := by
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · exact (analyticAt_hFiniteBoundarySecondX z).div hyAnalytic
        (by simpa only [hyZero] using hs0)
    · exact hYAnalytic.div hyAnalytic
        (by simpa only [hyZero] using hs0)
  have hsecondPointZero : secondPoint 0 = ![secondX, secondT] := by
    funext i
    fin_cases i
    · simp [secondPoint, secondX, hyZero]
    · simp [secondPoint, secondT, hyZero, hYZero]
  have hsecondT : secondT ≠ 0 := div_ne_zero hS0 hs0
  have hchart : (firstX 0, 1) ≠ (secondX, secondT) := by
    intro hequal
    have hfirstCoordinate := congrArg Prod.fst hequal
    have hcoordinate : hFiniteBoundaryFirstX z 0 / s =
        hFiniteBoundarySecondX z 0 / s := by
      simpa only [firstX, secondX, hyZero] using hfirstCoordinate
    have hxequal := (div_left_inj' hs0).mp hcoordinate
    rw [hfirstX0] at hxequal
    exact hsecondX0 hxequal.symm
  have hyTendsto : Tendsto y (nhds 0) (nhds s) := by
    have ht := hyAnalytic.continuousAt
    change Tendsto y (nhds 0) (nhds (y 0)) at ht
    rw [hyZero] at ht
    exact ht
  have hyEventually : ∀ᶠ lambda in nhds 0, y lambda ≠ 0 :=
    hyTendsto.eventually_ne hs0
  have hplaneZero : ∀ᶠ lambda in nhds 0,
      hCollisionPlaneDifference 1 firstX
        (lambda, secondPoint lambda) = 0 := by
    filter_upwards [eventually_hFiniteBoundary_fibre z hz,
      hyEventually] with lambda hfibre hyAt
    obtain ⟨hPfiber, hQfiber⟩ := h_normalized_fibre
      1 (hFiniteBoundaryFirstX z lambda) (y lambda)
        (hFiniteBoundarySecondX z lambda) (Y lambda)
        (hFiniteBoundaryW z lambda)
        (hFiniteBoundaryCapitalW z lambda)
        (by simpa using hyPower lambda) (by simpa using hYPower lambda)
        hyAt hfibre.1 hfibre.2
    funext i
    fin_cases i
    · simpa [hCollisionPlaneDifference, firstX, secondPoint]
        using sub_eq_zero.mpr hPfiber
    · simpa [hCollisionPlaneDifference, firstX, secondPoint]
        using sub_eq_zero.mpr hQfiber
  have hunitAnalytic : AnalyticAt ℂ unit 0 := by
    exact hrawUnitAnalytic.div (hyAnalytic.pow N)
      (by
        rw [hyZero]
        exact pow_ne_zero N hs0)
  have hunitZero : unit 0 ≠ 0 := by
    change rawUnit 0 / y 0 ^ N ≠ 0
    rw [hyZero]
    exact div_ne_zero hrawUnitZero (pow_ne_zero N hs0)
  have hthirdFactor : ∀ᶠ lambda in nhds 0,
      MvPolynomial.eval ![firstX lambda, 1] R -
          MvPolynomial.eval
            ![secondPoint lambda 0, secondPoint lambda 1] R =
        lambda ^ order * unit lambda := by
    filter_upwards [hyEventually, hrawFactor] with
      lambda hyAt hrawAt
    have hnormalized := normalized_ordinary_form_difference_general
      R N hR (hFiniteBoundaryFirstX z lambda) (y lambda)
        (hFiniteBoundarySecondX z lambda) (Y lambda) hyAt
    rw [hHardOddDecomposition_eval R Rzero coefficient
        (hFiniteBoundaryFirstX z lambda) (y lambda) N hdecomposition,
      hHardOddDecomposition_eval R Rzero coefficient
        (hFiniteBoundarySecondX z lambda) (Y lambda) N hdecomposition,
      hyPower lambda, hYPower lambda] at hnormalized
    change MvPolynomial.eval
        ![hFiniteBoundaryFirstX z lambda / y lambda, 1] R -
      MvPolynomial.eval
        ![hFiniteBoundarySecondX z lambda / y lambda,
          Y lambda / y lambda] R = _
    rw [hnormalized]
    have hrawExpression :
        hFormEval (hFiniteBoundaryFirstX z lambda)
              (hFiniteBoundaryW z lambda) Rzero +
            coefficient * y lambda ^ N -
          (hFormEval (hFiniteBoundarySecondX z lambda)
                (hFiniteBoundaryCapitalW z lambda) Rzero +
            coefficient * Y lambda ^ N) = raw lambda := by
      simp only [raw]
      ring
    rw [hrawExpression, hrawAt]
    simp only [unit]
    ring
  let data : HHardOddOrdinarySourceBranchData R :=
    { firstX := firstX
      secondPoint := secondPoint
      secondX := secondX
      secondT := secondT
      order := order
      unit := unit
      firstX_analyticAt := hfirstXAnalytic
      secondPoint_analyticAt := hsecondPointAnalytic
      secondPoint_zero := hsecondPointZero
      secondT_ne_zero := hsecondT
      chart_points_ne := hchart
      plane_zero := hplaneZero
      order_pos := horder
      unit_analyticAt := hunitAnalytic
      unit_zero_ne := hunitZero
      third_factor := hthirdFactor }
  exact ⟨data⟩

/-- A finite boundary hard norm root is incompatible with an injective
representative under ordinary tails. -/
theorem hHardOddFiniteBoundaryMaximalIdealTails_not_hasInjectiveRepresentative
    (R Rzero : Form ℂ) (coefficient : ℂ) (N : ℕ)
    (hR : R.IsHomogeneous N)
    (hdecomposition :
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N)
    (hNodd : Odd N)
    (hRzero : Rzero.IsWeightedHomogeneous hFormWeight N)
    (numerator : ℂ[X]) (hnumerator : numerator ≠ 0)
    (z : ℂ) (hz : z ^ 2 + 2 = 0) (hroot : numerator.IsRoot z)
    (hrepresentation :
      hHardOddNorm Rzero coefficient N =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (2 * N) (4 * N)))
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hOrdinaryPolynomialMap R i) ∈
        Germ.maximalIdeal 2 ^ (hOrdinaryDegrees N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨data⟩ :=
    exists_hHardOddOrdinarySourceBranchData_of_finite_boundary_root
      R Rzero coefficient N hR hdecomposition hNodd hRzero numerator
        hnumerator z hz hroot hrepresentation
  exact
    hHardOddOrdinarySourceBranchMaximalIdealTails_not_hasInjectiveRepresentative
      R N hR data representative hanalytic hzero htail

end OnLeConjecture.DThree
