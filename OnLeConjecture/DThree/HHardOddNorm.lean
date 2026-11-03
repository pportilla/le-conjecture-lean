/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HNoninvariantReflection
public import OnLeConjecture.DThree.HPositiveLocalOrders
public import OnLeConjecture.DThree.HRegularProfileCollision

/-!
# The norm of an odd H section

The two square roots of each conic coordinate define four values of an odd
section. Their product is a rational function on the residual conic. This
module gives that rational function, proves its pole profile, and relates its
zeros to zeros of the original section.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- The product of the four sign conjugates of the odd section difference. -/
@[expose]
noncomputable def hHardOddNorm
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ) :
    RatFunc ℂ :=
  let A := hConicDifference Rzero
  (A ^ 2 + algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2) *
      (hConicParamW ^ N - hConicParamCapitalW ^ N)) ^ 2 -
    algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2) *
      A ^ 2 * hConicParamW ^ N

/-- The norm is the product of the four possible sign differences whenever
the two conic coordinates are squares. -/
theorem hHardOddNorm_eq_sign_product
    (coefficient t T : ℂ) (N : ℕ)
    (A w W : ℂ) (ht : t ^ 2 = w) (hT : T ^ 2 = W) :
    (A + coefficient * (t ^ N - T ^ N)) *
        (A + coefficient * (t ^ N + T ^ N)) *
        (A + coefficient * (-t ^ N - T ^ N)) *
        (A + coefficient * (-t ^ N + T ^ N)) =
      (A ^ 2 + coefficient ^ 2 * (w ^ N - W ^ N)) ^ 2 -
        (4 * coefficient ^ 2) * A ^ 2 * w ^ N := by
  have htN : (t ^ N) ^ 2 = w ^ N := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, ht]
  have hTN : (T ^ N) ^ 2 = W ^ N := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hT]
  rw [← htN, ← hTN]
  ring

/-- Evaluation of the hard norm at a regular parameter is the product of the
four sign differences. -/
theorem hHardOddNorm_eval_eq_sign_product
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient z t T : ℂ) (N : ℕ)
    (hA : HRatFuncRegularAt z (hConicDifference Rzero))
    (hw : HRatFuncRegularAt z hConicParamW)
    (hW : HRatFuncRegularAt z hConicParamCapitalW)
    (ht : t ^ 2 = RatFunc.eval (RingHom.id ℂ) z hConicParamW)
    (hT : T ^ 2 = RatFunc.eval (RingHom.id ℂ) z hConicParamCapitalW) :
    RatFunc.eval (RingHom.id ℂ) z (hHardOddNorm Rzero coefficient N) =
      (RatFunc.eval (RingHom.id ℂ) z (hConicDifference Rzero) +
          coefficient * (t ^ N - T ^ N)) *
        (RatFunc.eval (RingHom.id ℂ) z (hConicDifference Rzero) +
          coefficient * (t ^ N + T ^ N)) *
        (RatFunc.eval (RingHom.id ℂ) z (hConicDifference Rzero) +
          coefficient * (-t ^ N - T ^ N)) *
        (RatFunc.eval (RingHom.id ℂ) z (hConicDifference Rzero) +
          coefficient * (-t ^ N + T ^ N)) := by
  let A := hConicDifference Rzero
  let cTwo : RatFunc ℂ := algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2)
  let cFour : RatFunc ℂ := algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2)
  have hcTwo : HRatFuncRegularAt z cTwo := by
    change HRatFuncRegularAt z (RatFunc.C (coefficient ^ 2))
    exact hRatFuncRegularAt_C z (coefficient ^ 2)
  have hcFour : HRatFuncRegularAt z cFour := by
    change HRatFuncRegularAt z (RatFunc.C (4 * coefficient ^ 2))
    exact hRatFuncRegularAt_C z (4 * coefficient ^ 2)
  have hASquare := hRatFuncRegularAt_pow hA 2
  have hwPower := hRatFuncRegularAt_pow hw N
  have hWPower := hRatFuncRegularAt_pow hW N
  have hpowers := hRatFuncRegularAt_sub hwPower hWPower
  have hscaled := hRatFuncRegularAt_mul hcTwo hpowers
  have hmiddle := hRatFuncRegularAt_add hASquare hscaled
  have hleft := hRatFuncRegularAt_pow hmiddle 2
  have hright := hRatFuncRegularAt_mul
    (hRatFuncRegularAt_mul hcFour hASquare) hwPower
  have hcTwoEval : RatFunc.eval (RingHom.id ℂ) z
      (algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2)) =
        coefficient ^ 2 := by
    rw [RatFunc.eval_algebraMap]
    simp
  have hcFourEval : RatFunc.eval (RingHom.id ℂ) z
      (algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2)) =
        4 * coefficient ^ 2 := by
    rw [RatFunc.eval_algebraMap]
    simp
  rw [hHardOddNorm,
    h_ratFunc_eval_sub z _ _ hleft hright,
    h_ratFunc_eval_pow z _ hmiddle,
    h_ratFunc_eval_add_regular z _ _ hASquare hscaled,
    h_ratFunc_eval_pow z A hA,
    h_ratFunc_eval_mul_regular z _ _ hcTwo hpowers,
    h_ratFunc_eval_sub z _ _ hwPower hWPower,
    h_ratFunc_eval_pow z _ hw,
    h_ratFunc_eval_pow z _ hW,
    h_ratFunc_eval_mul_regular z _ _
      (hRatFuncRegularAt_mul hcFour hASquare) hwPower,
    h_ratFunc_eval_mul_regular z _ _ hcFour hASquare,
    h_ratFunc_eval_pow z A hA,
    h_ratFunc_eval_pow z _ hw]
  rw [hcTwoEval, hcFourEval]
  change
    (RatFunc.eval (RingHom.id ℂ) z A ^ 2 +
        coefficient ^ 2 *
          (RatFunc.eval (RingHom.id ℂ) z hConicParamW ^ N -
            RatFunc.eval (RingHom.id ℂ) z hConicParamCapitalW ^ N)) ^ 2 -
      (4 * coefficient ^ 2) * RatFunc.eval (RingHom.id ℂ) z A ^ 2 *
        RatFunc.eval (RingHom.id ℂ) z hConicParamW ^ N = _
  exact (hHardOddNorm_eq_sign_product coefficient t T N
    (RatFunc.eval (RingHom.id ℂ) z A)
    (RatFunc.eval (RingHom.id ℂ) z hConicParamW)
    (RatFunc.eval (RingHom.id ℂ) z hConicParamCapitalW) ht hT).symm

/-- A zero of the hard norm at a regular parameter gives a choice of signs
for which the odd section difference vanishes. -/
theorem exists_signs_hard_difference_zero_of_norm_eval_zero
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient z : ℂ) (N : ℕ)
    (hNodd : Odd N)
    (hA : HRatFuncRegularAt z (hConicDifference Rzero))
    (hw : HRatFuncRegularAt z hConicParamW)
    (hW : HRatFuncRegularAt z hConicParamCapitalW)
    (hnorm : RatFunc.eval (RingHom.id ℂ) z
      (hHardOddNorm Rzero coefficient N) = 0) :
    ∃ t T : ℂ,
      t ^ 2 = RatFunc.eval (RingHom.id ℂ) z hConicParamW ∧
      T ^ 2 = RatFunc.eval (RingHom.id ℂ) z hConicParamCapitalW ∧
      RatFunc.eval (RingHom.id ℂ) z (hConicDifference Rzero) +
        coefficient * (t ^ N - T ^ N) = 0 := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq
    (RatFunc.eval (RingHom.id ℂ) z hConicParamW) (by norm_num : 0 < 2)
  obtain ⟨T, hT⟩ := IsAlgClosed.exists_pow_nat_eq
    (RatFunc.eval (RingHom.id ℂ) z hConicParamCapitalW)
      (by norm_num : 0 < 2)
  have hproduct := hHardOddNorm_eval_eq_sign_product
    Rzero coefficient z t T N hA hw hW ht hT
  rw [hnorm] at hproduct
  rcases mul_eq_zero.mp hproduct.symm with hleft | hfourth
  · rcases mul_eq_zero.mp hleft with hleft | hthird
    · rcases mul_eq_zero.mp hleft with hfirst | hsecond
      · exact ⟨t, T, ht, hT, hfirst⟩
      · exact ⟨t, -T, ht, by simpa using hT,
          by simpa only [hNodd.neg_pow, sub_neg_eq_add] using hsecond⟩
    · exact ⟨-t, T, by simpa using ht, hT,
        by simpa only [hNodd.neg_pow] using hthird⟩
  · exact ⟨-t, -T, by simpa using ht, by simpa using hT,
      by simpa only [hNodd.neg_pow, sub_neg_eq_add] using hfourth⟩

/-- The descended conic difference is regular wherever the conic
parametrization is regular. -/
theorem hConicDifference_regular_at
    (Rzero : MvPolynomial (Fin 2) ℂ) (z : ℂ)
    (hlinear : z + 1 ≠ 0)
    (hden : hConicParamDenominator.eval z ≠ 0) :
    HRatFuncRegularAt z (hConicDifference Rzero) := by
  obtain ⟨hx, hw, hW⟩ := h_conic_param_regular_at z hlinear hden
  have hone : HRatFuncRegularAt z (1 : RatFunc ℂ) := by
    simpa using hRatFuncRegularAt_algebraMap (K := ℂ) z 1
  rw [hConicDifference, hFirstConicPullback, hSecondConicPullback]
  exact hRatFuncRegularAt_sub
    (hRatFuncRegularAt_hFormEval z 1 hConicParamW Rzero hone hw)
    (hRatFuncRegularAt_hFormEval z hConicParamX
      hConicParamCapitalW Rzero hx hW)

/-- A finite numerator root of the hard norm produces roots of the two conic
coordinates for which the odd section difference vanishes. -/
theorem exists_signs_hard_difference_zero_of_norm_numerator_root
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient z : ℂ) (N : ℕ)
    (hNodd : Odd N) (numerator : ℂ[X])
    (hrepresentation :
      hHardOddNorm Rzero coefficient N =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (2 * N) (4 * N)))
    (hroot : numerator.IsRoot z)
    (hprofile :
      (hPoleProfileDenominator (K := ℂ) (2 * N) (4 * N)).eval z ≠ 0) :
    ∃ t T : ℂ,
      t ^ 2 = RatFunc.eval (RingHom.id ℂ) z hConicParamW ∧
      T ^ 2 = RatFunc.eval (RingHom.id ℂ) z hConicParamCapitalW ∧
      RatFunc.eval (RingHom.id ℂ) z (hConicDifference Rzero) +
        coefficient * (t ^ N - T ^ N) = 0 := by
  have hNpos : 0 < N := hNodd.pos
  obtain ⟨hlinear, hden⟩ := h_pole_profile_factors_ne_zero
    (2 * N) (4 * N) (by omega) (by omega) z hprofile
  obtain ⟨_hx, hw, hW⟩ := h_conic_param_regular_at z hlinear hden
  have hnorm : RatFunc.eval (RingHom.id ℂ) z
      (hHardOddNorm Rzero coefficient N) = 0 := by
    have heval := congrArg (RatFunc.eval (RingHom.id ℂ) z)
      hrepresentation
    rw [h_ratFunc_eval_algebraMap_div z numerator
      (hPoleProfileDenominator (2 * N) (4 * N)) hprofile] at heval
    have hnumerator : numerator.eval z = 0 := by
      simpa [Polynomial.IsRoot] using hroot
    rw [hnumerator, zero_div] at heval
    exact heval
  exact exists_signs_hard_difference_zero_of_norm_eval_zero
    Rzero coefficient z N hNodd
      (hConicDifference_regular_at Rzero z hlinear hden) hw hW hnorm

/-- A numerator root away from the two points over `X = 1` gives an affine
off diagonal fibre pair for the odd hard form. -/
theorem exists_hard_odd_affine_fibre_of_norm_numerator_root
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient z : ℂ) (N : ℕ)
    (hNodd : Odd N) (numerator : ℂ[X])
    (hrepresentation :
      hHardOddNorm Rzero coefficient N =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (2 * N) (4 * N)))
    (hroot : numerator.IsRoot z)
    (hzPlus : z ≠ hConicOneRootPlus)
    (hzMinus : z ≠ hConicOneRootMinus)
    (hprofile :
      (hPoleProfileDenominator (K := ℂ) (2 * N) (4 * N)).eval z ≠ 0) :
    ∃ t T : ℂ,
      RatFunc.eval (RingHom.id ℂ) z hConicParamX ≠ 1 ∧
      hP 1 (t ^ 2) =
        hP (RatFunc.eval (RingHom.id ℂ) z hConicParamX) (T ^ 2) ∧
      hQ 1 (t ^ 2) =
        hQ (RatFunc.eval (RingHom.id ℂ) z hConicParamX) (T ^ 2) ∧
      hFormEval 1 (t ^ 2) Rzero + coefficient * t ^ N =
        hFormEval (RatFunc.eval (RingHom.id ℂ) z hConicParamX)
          (T ^ 2) Rzero + coefficient * T ^ N := by
  have hNpos : 0 < N := hNodd.pos
  obtain ⟨hlinear, hden⟩ := h_pole_profile_factors_ne_zero
    (2 * N) (4 * N) (by omega) (by omega) z hprofile
  obtain ⟨t, T, ht, hT, hsection⟩ :=
    exists_signs_hard_difference_zero_of_norm_numerator_root
      Rzero coefficient z N hNodd numerator hrepresentation hroot hprofile
  have hfibre := h_conic_param_eval_fibre z hlinear hden
  rw [← ht, ← hT] at hfibre
  have hthird :
      hFormEval 1 (t ^ 2) Rzero + coefficient * t ^ N =
        hFormEval (RatFunc.eval (RingHom.id ℂ) z hConicParamX)
          (T ^ 2) Rzero + coefficient * T ^ N := by
    rw [h_ratFunc_eval_hConicDifference_regular Rzero z hlinear hden,
      ← ht, ← hT] at hsection
    linear_combination hsection
  refine ⟨t, T, ?_, hfibre.1, hfibre.2, hthird⟩
  exact h_conic_param_eval_x_ne_one
    h_conic_one_roots_equations.1 h_conic_one_roots_equations.2
      h_conic_one_roots_ne hzPlus hzMinus hden

/-- The odd hard norm has pole profile `(2N,4N)`, whose denominator has
degree `10N`. -/
theorem hasHPoleProfile_hHardOddNorm
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ)
    (hRzero : Rzero.IsWeightedHomogeneous hFormWeight N) :
    HasHPoleProfile (2 * N) (4 * N)
      (hHardOddNorm Rzero coefficient N) := by
  let A : RatFunc ℂ := hConicDifference Rzero
  have hA : HasHPoleProfile (N / 2) N A :=
    hasHPoleProfile_hConicDifference N Rzero hRzero
  have hASquare : HasHPoleProfile N (2 * N) (A ^ 2) := by
    apply (hA.pow 2).mono
    · omega
    · omega
  have hw : HasHPoleProfile N (2 * N)
      ((hConicParamW (K := ℂ)) ^ N) := by
    simpa [Nat.mul_comm] using
      (hasHPoleProfile_hConicParamW (K := ℂ)).pow N
  have hW : HasHPoleProfile N (2 * N)
      ((hConicParamCapitalW (K := ℂ)) ^ N) := by
    simpa [Nat.mul_comm] using
      (hasHPoleProfile_hConicParamCapitalW (K := ℂ)).pow N
  have hpowers : HasHPoleProfile N (2 * N)
      ((hConicParamW (K := ℂ)) ^ N -
        (hConicParamCapitalW (K := ℂ)) ^ N) := hw.sub hW
  have hscaled : HasHPoleProfile N (2 * N)
      (algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2) *
        ((hConicParamW (K := ℂ)) ^ N -
          (hConicParamCapitalW (K := ℂ)) ^ N)) :=
    hpowers.const_mul (coefficient ^ 2)
  have hmiddle : HasHPoleProfile N (2 * N)
      (A ^ 2 + algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2) *
        ((hConicParamW (K := ℂ)) ^ N -
          (hConicParamCapitalW (K := ℂ)) ^ N)) :=
    hASquare.add hscaled
  have hleft : HasHPoleProfile (2 * N) (4 * N)
      ((A ^ 2 + algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2) *
        ((hConicParamW (K := ℂ)) ^ N -
          (hConicParamCapitalW (K := ℂ)) ^ N)) ^ 2) := by
    convert hmiddle.pow 2 using 1
    omega
  have hright : HasHPoleProfile (2 * N) (4 * N)
      (algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2) *
        A ^ 2 * (hConicParamW (K := ℂ)) ^ N) := by
    have hproduct := hASquare.mul hw
    have hscaledProduct := hproduct.const_mul (4 * coefficient ^ 2)
    convert hscaledProduct using 1
    · omega
    · omega
    · ring
  simpa only [hHardOddNorm, A] using hleft.sub hright

/-- The degree of the denominator in the hard norm profile is `10N`. -/
theorem hHardOddNorm_profile_degree (N : ℕ) :
    2 * N + 2 * (4 * N) = 10 * N := by
  omega

end OnLeConjecture.DThree
