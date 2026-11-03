/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HHardOddRegularBranch
public import OnLeConjecture.DThree.HReciprocalCollision

/-!
# Ordinary source branches at parameter infinity for the hard H norm

The reciprocal conic chart has two nonzero second coordinates at parameter
zero. A zero of the reciprocal hard norm selects a sign factor, while
nonvanishing of the rational norm gives that factor positive finite order.
-/

public section

noncomputable section

open Filter Set
open scoped Topology Polynomial WithZero

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- The reciprocal hard norm is regular at parameter zero. -/
theorem h_reciprocal_hHardOddNorm_regular_at_zero
    (Rzero : Form ℂ) (coefficient : ℂ) (N : ℕ) :
    HRatFuncRegularAt 0
      (hReciprocalRatFuncRingHom
        (hHardOddNorm Rzero coefficient N)) := by
  rw [h_reciprocalRatFuncRingHom_hHardOddNorm]
  let A := hReciprocalRatFuncRingHom (hConicDifference Rzero)
  have hA : HRatFuncRegularAt 0 A := by
    dsimp only [A]
    rw [h_reciprocalRatFuncRingHom_hConicDifference]
    exact hRatFuncRegularAt_sub
      (hRatFuncRegularAt_hFormEval 0 1 hMinusParamW Rzero
        (by simpa using hRatFuncRegularAt_algebraMap (K := ℂ) 0 1)
        h_minus_param_regular_at_zero.2.1)
      (hRatFuncRegularAt_hFormEval 0 hMinusParamX
        hMinusParamCapitalW Rzero h_minus_param_regular_at_zero.1
          h_minus_param_regular_at_zero.2.2)
  let cTwo : RatFunc ℂ :=
    algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2)
  let cFour : RatFunc ℂ :=
    algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2)
  have hcTwo : HRatFuncRegularAt 0 cTwo := by
    change HRatFuncRegularAt 0 (RatFunc.C (coefficient ^ 2))
    exact hRatFuncRegularAt_C 0 _
  have hcFour : HRatFuncRegularAt 0 cFour := by
    change HRatFuncRegularAt 0 (RatFunc.C (4 * coefficient ^ 2))
    exact hRatFuncRegularAt_C 0 _
  exact hRatFuncRegularAt_sub
    (hRatFuncRegularAt_pow
      (hRatFuncRegularAt_add (hRatFuncRegularAt_pow hA 2)
        (hRatFuncRegularAt_mul hcTwo
          (hRatFuncRegularAt_sub
            (hRatFuncRegularAt_pow h_minus_param_regular_at_zero.2.1 N)
            (hRatFuncRegularAt_pow h_minus_param_regular_at_zero.2.2 N)))) 2)
    (hRatFuncRegularAt_mul
      (hRatFuncRegularAt_mul hcFour (hRatFuncRegularAt_pow hA 2))
      (hRatFuncRegularAt_pow h_minus_param_regular_at_zero.2.1 N))

/-- Along analytic square roots of the reciprocal conic coordinates, the
reciprocal hard norm is the product of the four sign differences. -/
theorem eventually_hReciprocalCollision_hHardOddNorm_eq_sign_product
    (Rzero : Form ℂ) (coefficient : ℂ) (N : ℕ)
    (y Y : ℂ → ℂ)
    (hy : ∀ lambda, y lambda ^ 2 = hReciprocalCollisionW lambda)
    (hY : ∀ lambda,
      Y lambda ^ 2 = hReciprocalCollisionCapitalW lambda) :
    ∀ᶠ lambda in nhds 0,
      RatFunc.eval (RingHom.id ℂ) lambda
          (hReciprocalRatFuncRingHom
            (hHardOddNorm Rzero coefficient N)) =
        (hFormEval 1 (hReciprocalCollisionW lambda) Rzero -
            hFormEval (hReciprocalCollisionX lambda)
              (hReciprocalCollisionCapitalW lambda) Rzero +
            coefficient * (y lambda ^ N - Y lambda ^ N)) *
          (hFormEval 1 (hReciprocalCollisionW lambda) Rzero -
            hFormEval (hReciprocalCollisionX lambda)
              (hReciprocalCollisionCapitalW lambda) Rzero +
            coefficient * (y lambda ^ N + Y lambda ^ N)) *
          (hFormEval 1 (hReciprocalCollisionW lambda) Rzero -
            hFormEval (hReciprocalCollisionX lambda)
              (hReciprocalCollisionCapitalW lambda) Rzero +
            coefficient * (-y lambda ^ N - Y lambda ^ N)) *
          (hFormEval 1 (hReciprocalCollisionW lambda) Rzero -
            hFormEval (hReciprocalCollisionX lambda)
              (hReciprocalCollisionCapitalW lambda) Rzero +
            coefficient * (-y lambda ^ N + Y lambda ^ N)) := by
  filter_upwards [eventually_hReciprocalCollision_denominators] with
    lambda hdenominators
  obtain ⟨hden, hfunction⟩ := hdenominators
  have hxRegular : HRatFuncRegularAt lambda
      (hMinusParamX (K := ℂ)) :=
    hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd hMinusParamXNumerator
        hMinusParamDenominator) hden
  have hwRegular : HRatFuncRegularAt lambda
      (hMinusParamW (K := ℂ)) :=
    hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd hMinusParamWNumerator
        hMinusParamFunctionDenominator) hfunction
  have hcapitalWRegular : HRatFuncRegularAt lambda
      (hMinusParamCapitalW (K := ℂ)) :=
    hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd hMinusParamCapitalWNumerator
        hMinusParamFunctionDenominator) hfunction
  let A := hReciprocalRatFuncRingHom (hConicDifference Rzero)
  have hA : HRatFuncRegularAt lambda A := by
    dsimp only [A]
    rw [h_reciprocalRatFuncRingHom_hConicDifference]
    exact hRatFuncRegularAt_sub
      (hRatFuncRegularAt_hFormEval lambda 1 hMinusParamW Rzero
        (by simpa using hRatFuncRegularAt_algebraMap (K := ℂ) lambda 1)
        hwRegular)
      (hRatFuncRegularAt_hFormEval lambda hMinusParamX
        hMinusParamCapitalW Rzero hxRegular hcapitalWRegular)
  let cTwo : RatFunc ℂ :=
    algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2)
  let cFour : RatFunc ℂ :=
    algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2)
  have hcTwo : HRatFuncRegularAt lambda cTwo := by
    change HRatFuncRegularAt lambda (RatFunc.C (coefficient ^ 2))
    exact hRatFuncRegularAt_C lambda _
  have hcFour : HRatFuncRegularAt lambda cFour := by
    change HRatFuncRegularAt lambda (RatFunc.C (4 * coefficient ^ 2))
    exact hRatFuncRegularAt_C lambda _
  have hASquare := hRatFuncRegularAt_pow hA 2
  have hwPower := hRatFuncRegularAt_pow hwRegular N
  have hcapitalWPower := hRatFuncRegularAt_pow hcapitalWRegular N
  have hpowers := hRatFuncRegularAt_sub hwPower hcapitalWPower
  have hscaled := hRatFuncRegularAt_mul hcTwo hpowers
  have hmiddle := hRatFuncRegularAt_add hASquare hscaled
  have hleft := hRatFuncRegularAt_pow hmiddle 2
  have hright := hRatFuncRegularAt_mul
    (hRatFuncRegularAt_mul hcFour hASquare) hwPower
  have hcTwoEval : RatFunc.eval (RingHom.id ℂ) lambda
      (algebraMap ℂ (RatFunc ℂ) (coefficient ^ 2)) =
        coefficient ^ 2 := by
    change RatFunc.eval (RingHom.id ℂ) lambda
      (RatFunc.C (coefficient ^ 2)) = coefficient ^ 2
    rw [RatFunc.eval_C]
    rfl
  have hcFourEval : RatFunc.eval (RingHom.id ℂ) lambda
      (algebraMap ℂ (RatFunc ℂ) (4 * coefficient ^ 2)) =
        4 * coefficient ^ 2 := by
    change RatFunc.eval (RingHom.id ℂ) lambda
      (RatFunc.C (4 * coefficient ^ 2)) = 4 * coefficient ^ 2
    rw [RatFunc.eval_C]
    rfl
  have heval := congrArg (RatFunc.eval (RingHom.id ℂ) lambda)
    (h_reciprocalRatFuncRingHom_hHardOddNorm
      Rzero coefficient N)
  rw [h_ratFunc_eval_sub lambda _ _ hleft hright,
    h_ratFunc_eval_pow lambda _ hmiddle,
    h_ratFunc_eval_add_regular lambda _ _ hASquare hscaled,
    h_ratFunc_eval_pow lambda A hA,
    h_ratFunc_eval_mul_regular lambda _ _ hcTwo hpowers,
    h_ratFunc_eval_sub lambda _ _ hwPower hcapitalWPower,
    h_ratFunc_eval_pow lambda _ hwRegular,
    h_ratFunc_eval_pow lambda _ hcapitalWRegular,
    h_ratFunc_eval_mul_regular lambda _ _
      (hRatFuncRegularAt_mul hcFour hASquare) hwPower,
    h_ratFunc_eval_mul_regular lambda _ _ hcFour hASquare,
    h_ratFunc_eval_pow lambda A hA,
    h_ratFunc_eval_pow lambda _ hwRegular,
    hcTwoEval, hcFourEval] at heval
  have hweval : RatFunc.eval (RingHom.id ℂ) lambda
      (hMinusParamW (K := ℂ)) = hReciprocalCollisionW lambda := by
    rw [hMinusParamW,
      h_ratFunc_eval_algebraMap_div lambda hMinusParamWNumerator
        hMinusParamFunctionDenominator hfunction]
    rfl
  have hcapitalWeval : RatFunc.eval (RingHom.id ℂ) lambda
      (hMinusParamCapitalW (K := ℂ)) =
        hReciprocalCollisionCapitalW lambda := by
    rw [hMinusParamCapitalW,
      h_ratFunc_eval_algebraMap_div lambda hMinusParamCapitalWNumerator
        hMinusParamFunctionDenominator hfunction]
    rfl
  have hAeval : RatFunc.eval (RingHom.id ℂ) lambda A =
      hFormEval 1 (hReciprocalCollisionW lambda) Rzero -
        hFormEval (hReciprocalCollisionX lambda)
          (hReciprocalCollisionCapitalW lambda) Rzero := by
    exact (h_reciprocal_collision_difference_at
      Rzero lambda hden hfunction).symm
  rw [hweval, hcapitalWeval, hAeval] at heval
  rw [heval]
  exact (hHardOddNorm_eq_sign_product coefficient
    (y lambda) (Y lambda) N
    (hFormEval 1 (hReciprocalCollisionW lambda) Rzero -
      hFormEval (hReciprocalCollisionX lambda)
        (hReciprocalCollisionCapitalW lambda) Rzero)
    (hReciprocalCollisionW lambda)
    (hReciprocalCollisionCapitalW lambda)
    (hy lambda) (hY lambda)).symm

/-- A function with a local coordinate power times a nonzero analytic unit
cannot vanish throughout a neighborhood. -/
theorem not_eventually_eq_zero_of_pow_mul_analytic_unit
    (f u : ℂ → ℂ) (k : ℕ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hfactor : ∀ᶠ lambda in nhds 0,
      f lambda = lambda ^ k * u lambda) :
    ¬ ∀ᶠ lambda in nhds 0, f lambda = 0 := by
  have huEventually : ∀ᶠ lambda in nhds 0, u lambda ≠ 0 := by
    have ht := hu.continuousAt.tendsto
    change Tendsto u (nhds 0) (nhds (u 0)) at ht
    exact ht.eventually_ne hu0
  intro hzero
  have hfalse : ∀ᶠ lambda in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
      False := by
    filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds,
      huEventually.filter_mono nhdsWithin_le_nhds,
      hzero.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with
      lambda hfactorAt huAt hzeroAt hlambda
    rw [hzeroAt] at hfactorAt
    exact (mul_ne_zero (pow_ne_zero k (by simpa using hlambda)) huAt)
      hfactorAt.symm
  obtain ⟨lambda, hfalseAt⟩ := hfalse.exists
  exact hfalseAt

/-- A nonzero reciprocal hard norm which vanishes at parameter zero gives
ordinary source branch data at infinity. -/
theorem exists_hHardOddOrdinarySourceBranchData_of_reciprocal_norm_zero
    (R Rzero : Form ℂ) (coefficient : ℂ) (N : ℕ)
    (hR : R.IsHomogeneous N)
    (hdecomposition :
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N)
    (hNodd : Odd N)
    (hnormNe : hReciprocalRatFuncRingHom
      (hHardOddNorm Rzero coefficient N) ≠ 0)
    (hnormZero : RatFunc.eval (RingHom.id ℂ) 0
      (hReciprocalRatFuncRingHom
        (hHardOddNorm Rzero coefficient N)) = 0) :
    Nonempty (HHardOddOrdinarySourceBranchData R) := by
  obtain ⟨normOrder, hnormOrder⟩ := exists_h_finite_order_of_regular
    0 (hReciprocalRatFuncRingHom
      (hHardOddNorm Rzero coefficient N)) hnormNe
      (h_reciprocal_hHardOddNorm_regular_at_zero
        Rzero coefficient N)
  obtain ⟨normUnit, hnormUnitAnalytic, hnormUnitZero, hnormFactor⟩ :=
    exists_analyticAt_ratFunc_eval_factor_of_finite_order
      (hReciprocalRatFuncRingHom
        (hHardOddNorm Rzero coefficient N)) normOrder hnormOrder
  have hnormNotEventuallyZero :
      ¬ ∀ᶠ lambda in nhds 0,
        RatFunc.eval (RingHom.id ℂ) lambda
          (hReciprocalRatFuncRingHom
            (hHardOddNorm Rzero coefficient N)) = 0 :=
    not_eventually_eq_zero_of_pow_mul_analytic_unit
      (fun lambda ↦ RatFunc.eval (RingHom.id ℂ) lambda
        (hReciprocalRatFuncRingHom
          (hHardOddNorm Rzero coefficient N)))
      normUnit normOrder hnormUnitAnalytic hnormUnitZero hnormFactor
  have hformulaZero := hnormZero
  rw [h_reciprocal_hHardOddNorm_eval_zero] at hformulaZero
  let A := RatFunc.eval (RingHom.id ℂ) 0
    (hReciprocalRatFuncRingHom (hConicDifference Rzero))
  let w : ℂ := -(1 / 3)
  obtain ⟨s, S, hs, hS, hsection⟩ :=
    exists_signs_hard_difference_zero_of_formula_zero
      coefficient A w w N hNodd (by simpa [A, w] using hformulaZero)
  have hw0 : hReciprocalCollisionW 0 = w := by
    norm_num [hReciprocalCollisionW, hMinusParamWNumerator,
      hMinusParamFunctionDenominator, hMinusParamDenominator, w]
  have hcapitalW0 : hReciprocalCollisionCapitalW 0 = w := by
    norm_num [hReciprocalCollisionCapitalW,
      hMinusParamCapitalWNumerator, hMinusParamFunctionDenominator,
      hMinusParamDenominator, w]
  have hx0 : hReciprocalCollisionX 0 = -1 := by
    norm_num [hReciprocalCollisionX, hMinusParamXNumerator,
      hMinusParamDenominator]
  have hs0 : s ≠ 0 := by
    intro hsZero
    have hwZero : w = 0 := by
      rw [← hs, hsZero, zero_pow (by norm_num : 2 ≠ 0)]
    norm_num [w] at hwZero
  have hS0 : S ≠ 0 := by
    intro hSZero
    have hwZero : w = 0 := by
      rw [← hS, hSZero, zero_pow (by norm_num : 2 ≠ 0)]
    norm_num [w] at hwZero
  have hsCollision : s ^ 2 = hReciprocalCollisionW 0 := by
    rw [hw0]
    exact hs
  have hSCollision :
      S ^ 2 = hReciprocalCollisionCapitalW 0 := by
    rw [hcapitalW0]
    exact hS
  obtain ⟨y, hyAnalytic, hyZero, hyPower⟩ :=
    exists_analyticAt_root_with_value
      hReciprocalCollisionW analyticAt_hReciprocalCollisionW
        (by
          rw [hw0]
          norm_num [w]) 2 (by norm_num) s hsCollision
  obtain ⟨Y, hYAnalytic, hYZero, hYPower⟩ :=
    exists_analyticAt_root_with_value
      hReciprocalCollisionCapitalW
        analyticAt_hReciprocalCollisionCapitalW
        (by
          rw [hcapitalW0]
          norm_num [w])
        2 (by norm_num) S hSCollision
  let raw : ℂ → ℂ := fun lambda ↦
    hFormEval 1 (hReciprocalCollisionW lambda) Rzero -
      hFormEval (hReciprocalCollisionX lambda)
        (hReciprocalCollisionCapitalW lambda) Rzero +
      coefficient * (y lambda ^ N - Y lambda ^ N)
  have hrawAnalytic : AnalyticAt ℂ raw 0 := by
    dsimp only [raw]
    have hfirst := analyticAt_eval_finTwo Rzero
      (fun _ ↦ 1) hReciprocalCollisionW
      analyticAt_const analyticAt_hReciprocalCollisionW
    have hsecond := analyticAt_eval_finTwo Rzero
      hReciprocalCollisionX hReciprocalCollisionCapitalW
      analyticAt_hReciprocalCollisionX
      analyticAt_hReciprocalCollisionCapitalW
    have hsum := (hfirst.sub hsecond).add
      ((analyticAt_const : AnalyticAt ℂ
          (fun _ : ℂ ↦ coefficient) 0).mul
        ((hyAnalytic.pow N).sub (hYAnalytic.pow N)))
    convert hsum using 1
    funext lambda
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
      hFormEval_eq_eval_finTwo]
  have hrawZero : raw 0 = 0 := by
    have hAvalue : A =
        hFormEval 1 w Rzero - hFormEval (-1) w Rzero := by
      dsimp only [A]
      simpa [w] using h_reciprocal_hConicDifference_eval_zero Rzero
    dsimp only [raw]
    rw [hw0, hcapitalW0, hx0, hyZero, hYZero]
    rw [hAvalue] at hsection
    exact hsection
  have hnormProduct :=
    eventually_hReciprocalCollision_hHardOddNorm_eq_sign_product
      Rzero coefficient N y Y hyPower hYPower
  have hrawNotZero : ¬ ∀ᶠ lambda in nhds 0, raw lambda = 0 := by
    intro hrawEventually
    apply hnormNotEventuallyZero
    filter_upwards [hnormProduct, hrawEventually] with
      lambda hproduct hrawAt
    rw [hproduct]
    change raw lambda * _ * _ * _ = 0
    rw [hrawAt]
    simp
  obtain ⟨order, rawUnit, hrawUnitAnalytic, hrawUnitZero,
      hrawFactorRaw⟩ :=
    hrawAnalytic.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hrawNotZero
  have hrawFactor : ∀ᶠ lambda in nhds 0,
      raw lambda = lambda ^ order * rawUnit lambda := by
    simpa [sub_zero, smul_eq_mul] using hrawFactorRaw
  have horder : 0 < order := by
    apply Nat.pos_of_ne_zero
    intro horderZero
    have hfactorAt := hrawFactor.self_of_nhds
    rw [horderZero, pow_zero, one_mul, hrawZero] at hfactorAt
    exact hrawUnitZero hfactorAt.symm
  let firstX : ℂ → ℂ := fun lambda ↦ 1 / y lambda
  let secondPoint : ℂ → Fin 2 → ℂ := fun lambda ↦
    ![hReciprocalCollisionX lambda / y lambda,
      Y lambda / y lambda]
  let secondX : ℂ := -1 / s
  let secondT : ℂ := S / s
  let unit : ℂ → ℂ := fun lambda ↦ rawUnit lambda / y lambda ^ N
  have hfirstXAnalytic : AnalyticAt ℂ firstX 0 := by
    apply analyticAt_const.div hyAnalytic
    simpa [hyZero] using hs0
  have hsecondPointAnalytic : AnalyticAt ℂ secondPoint 0 := by
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · exact analyticAt_hReciprocalCollisionX.div hyAnalytic
        (by simpa [hyZero] using hs0)
    · exact hYAnalytic.div hyAnalytic (by simpa [hyZero] using hs0)
  have hsecondPointZero : secondPoint 0 = ![secondX, secondT] := by
    funext i
    fin_cases i
    · simp [secondPoint, secondX, hyZero, hx0]
    · simp [secondPoint, secondT, hyZero, hYZero]
  have hsecondT : secondT ≠ 0 := div_ne_zero hS0 hs0
  have hchart : (firstX 0, 1) ≠ (secondX, secondT) := by
    intro hequal
    have hfirstCoordinate := congrArg Prod.fst hequal
    have hcoordinate : 1 / s = -1 / s := by
      simpa [firstX, secondX, hyZero] using hfirstCoordinate
    have hfalse : (1 : ℂ) = -1 :=
      (div_left_inj' hs0).mp hcoordinate
    norm_num at hfalse
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
    filter_upwards [eventually_hReciprocalCollision_fibre,
      hyEventually] with lambda hfibre hyAt
    obtain ⟨hPfiber, hQfiber⟩ := h_normalized_regular_fibre
      1 (y lambda) (Y lambda) (hReciprocalCollisionX lambda)
        (hReciprocalCollisionW lambda)
        (hReciprocalCollisionCapitalW lambda)
        (by simpa using hyPower lambda) (by simpa using hYPower lambda)
        hyAt hfibre.1 hfibre.2
    funext i
    fin_cases i
    · simpa [hCollisionPlaneDifference, firstX, secondPoint]
        using sub_eq_zero.mpr hPfiber
    · simpa [hCollisionPlaneDifference, firstX, secondPoint]
        using sub_eq_zero.mpr hQfiber
  have hunitAnalytic : AnalyticAt ℂ unit 0 :=
    hrawUnitAnalytic.div (hyAnalytic.pow N)
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
    have hnormalized := normalized_ordinary_form_difference
      R N hR (y lambda) (hReciprocalCollisionX lambda)
        (Y lambda) hyAt
    rw [hHardOddDecomposition_eval R Rzero coefficient 1 (y lambda) N
        hdecomposition,
      hHardOddDecomposition_eval R Rzero coefficient
        (hReciprocalCollisionX lambda) (Y lambda) N hdecomposition,
      hyPower lambda, hYPower lambda] at hnormalized
    change MvPolynomial.eval ![1 / y lambda, 1] R -
        MvPolynomial.eval
          ![hReciprocalCollisionX lambda / y lambda,
            Y lambda / y lambda] R = _
    rw [hnormalized]
    have hrawExpression :
        hFormEval 1 (hReciprocalCollisionW lambda) Rzero +
              coefficient * y lambda ^ N -
            (hFormEval (hReciprocalCollisionX lambda)
                (hReciprocalCollisionCapitalW lambda) Rzero +
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

/-- A strict degree loss in the hard norm numerator gives the ordinary tail
endpoint through the reciprocal chart. -/
theorem hHardOddNormDegreeDropMaximalIdealTails_not_hasInjectiveRepresentative
    (R Rzero : Form ℂ) (coefficient : ℂ) (N : ℕ)
    (hR : R.IsHomogeneous N)
    (hdecomposition :
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N)
    (hNodd : Odd N)
    (numerator : ℂ[X]) (hnumerator : numerator ≠ 0)
    (hdegree : numerator.natDegree < 10 * N)
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
  have hdegreeProfile :
      numerator.natDegree < 2 * N + 2 * (4 * N) := by
    omega
  obtain ⟨order, horder, horderInfinity⟩ :=
    h_order_at_infinity_positive_of_pole_profile_degree_drop
      (2 * N) (4 * N) hnumerator hdegreeProfile hrepresentation
  have horderZero :
      hFiniteOrderAt (0 : ℂ)
          (hReciprocalRatFuncRingHom
            (hHardOddNorm Rzero coefficient N)) =
        WithZero.exp (order : ℤ) := by
    rw [h_finite_order_reciprocalRatFuncRingHom]
    exact horderInfinity
  have hnormNe : hReciprocalRatFuncRingHom
      (hHardOddNorm Rzero coefficient N) ≠ 0 :=
    h_ratFunc_ne_zero_of_finite_order horderZero
  have hnormZero : RatFunc.eval (RingHom.id ℂ) 0
      (hReciprocalRatFuncRingHom
        (hHardOddNorm Rzero coefficient N)) = 0 :=
    h_ratFunc_eval_eq_zero_of_finite_order_pos
      0 (hReciprocalRatFuncRingHom
        (hHardOddNorm Rzero coefficient N)) order horder horderZero
  obtain ⟨data⟩ :=
    exists_hHardOddOrdinarySourceBranchData_of_reciprocal_norm_zero
      R Rzero coefficient N hR hdecomposition hNodd hnormNe hnormZero
  exact
    hHardOddOrdinarySourceBranchMaximalIdealTails_not_hasInjectiveRepresentative
      R N hR data representative hanalytic hzero htail

/-- The first conic second coordinate at finite parameter zero. -/
theorem h_conic_param_w_eval_zero :
    RatFunc.eval (RingHom.id ℂ) 0 (hConicParamW (K := ℂ)) =
      -(16 / 3 : ℂ) := by
  rw [hConicParamW,
    h_ratFunc_eval_algebraMap_div 0
      (-hConicParamOneFactor * hConicParamWFactor)
      hConicParamFunctionDenominator]
  · norm_num [hConicParamOneFactor, hConicParamWFactor,
      hConicParamFunctionDenominator, hConicParamDenominator]
  · norm_num [hConicParamFunctionDenominator,
      hConicParamDenominator]

/-- The second conic second coordinate at finite parameter zero. -/
theorem h_conic_param_capitalW_eval_zero :
    RatFunc.eval (RingHom.id ℂ) 0
        (hConicParamCapitalW (K := ℂ)) =
      -(4 / 3 : ℂ) := by
  rw [hConicParamCapitalW,
    h_ratFunc_eval_algebraMap_div 0
      (-hConicParamOneFactor * hConicParamCapitalWFactor)
      hConicParamFunctionDenominator]
  · norm_num [hConicParamOneFactor, hConicParamCapitalWFactor,
      hConicParamFunctionDenominator, hConicParamDenominator]
  · norm_num [hConicParamFunctionDenominator,
      hConicParamDenominator]

/-- Positive powers of the two conic second coordinates at finite parameter
zero are distinct. -/
theorem h_conic_param_second_powers_ne_at_zero
    (N : ℕ) (hN : 0 < N) :
    (-(16 / 3 : ℂ)) ^ N ≠ (-(4 / 3 : ℂ)) ^ N := by
  intro hequal
  have hbase : (-(16 / 3 : ℂ)) =
      4 * (-(4 / 3 : ℂ)) := by ring
  rw [hbase, mul_pow] at hequal
  have hsmall : (-(4 / 3 : ℂ)) ^ N ≠ 0 :=
    pow_ne_zero N (by norm_num)
  have hfour : (4 : ℂ) ^ N = 1 := by
    apply mul_right_cancel₀ hsmall
    simpa using hequal
  have hnat : (1 : ℕ) < 4 ^ N :=
    Nat.one_lt_pow (Nat.ne_of_gt hN) (by norm_num)
  have hcomplex : (1 : ℂ) ≠ (4 : ℂ) ^ N := by
    exact_mod_cast (ne_of_lt hnat)
  exact hcomplex hfour.symm

/-- If the descended conic difference is zero, the nonzero odd term keeps
the hard norm nonzero. -/
theorem hHardOddNorm_ne_zero_of_conicDifference_eq_zero
    (Rzero : Form ℂ) (coefficient : ℂ) (N : ℕ)
    (hNodd : Odd N) (hcoefficient : coefficient ≠ 0)
    (hdifference : hConicDifference Rzero = 0) :
    hHardOddNorm Rzero coefficient N ≠ 0 := by
  have hlinear : (0 : ℂ) + 1 ≠ 0 := by norm_num
  have hden : hConicParamDenominator (K := ℂ).eval 0 ≠ 0 := by
    norm_num [hConicParamDenominator]
  obtain ⟨_hxRegular, hwRegular, hcapitalWRegular⟩ :=
    h_conic_param_regular_at (0 : ℂ) hlinear hden
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq
    (-(16 / 3 : ℂ)) (by norm_num : 0 < 2)
  obtain ⟨S, hS⟩ := IsAlgClosed.exists_pow_nat_eq
    (-(4 / 3 : ℂ)) (by norm_num : 0 < 2)
  have hARegular : HRatFuncRegularAt 0 (hConicDifference Rzero) :=
    hConicDifference_regular_at Rzero 0 hlinear hden
  have hAeval : RatFunc.eval (RingHom.id ℂ) 0
      (hConicDifference Rzero) = 0 := by
    rw [hdifference, RatFunc.eval_zero]
  have heval := hHardOddNorm_eval_eq_sign_product
    Rzero coefficient 0 s S N hARegular hwRegular hcapitalWRegular
      (by
        rw [h_conic_param_w_eval_zero]
        exact hs)
      (by
        rw [h_conic_param_capitalW_eval_zero]
        exact hS)
  have hproduct := hHardOddNorm_eq_sign_product
    coefficient s S N 0 (-(16 / 3 : ℂ)) (-(4 / 3 : ℂ)) hs hS
  have hvalue : RatFunc.eval (RingHom.id ℂ) 0
      (hHardOddNorm Rzero coefficient N) =
        (coefficient ^ 2 *
          ((-(16 / 3 : ℂ)) ^ N - (-(4 / 3 : ℂ)) ^ N)) ^ 2 := by
    rw [hAeval] at heval
    rw [heval, hproduct]
    ring
  intro hnorm
  have hzero := congrArg (RatFunc.eval (RingHom.id ℂ) 0) hnorm
  rw [RatFunc.eval_zero, hvalue] at hzero
  exact (pow_ne_zero 2
    (mul_ne_zero (pow_ne_zero 2 hcoefficient)
      (sub_ne_zero.mpr
        (h_conic_param_second_powers_ne_at_zero N hNodd.pos)))) hzero

/-- Reciprocal substitution preserves nonvanishing of the hard norm. -/
theorem h_reciprocal_hHardOddNorm_ne_zero_of_conicDifference_eq_zero
    (Rzero : Form ℂ) (coefficient : ℂ) (N : ℕ)
    (hNodd : Odd N) (hcoefficient : coefficient ≠ 0)
    (hdifference : hConicDifference Rzero = 0) :
    hReciprocalRatFuncRingHom
      (hHardOddNorm Rzero coefficient N) ≠ 0 := by
  intro hzero
  apply hHardOddNorm_ne_zero_of_conicDifference_eq_zero
    Rzero coefficient N hNodd hcoefficient hdifference
  apply (hReciprocalRatFuncRingHom (K := ℂ)).injective
  simpa using hzero

/-- A zero descended conic difference makes the reciprocal hard norm vanish
at parameter zero. -/
theorem h_reciprocal_hHardOddNorm_eval_zero_of_conicDifference_eq_zero
    (Rzero : Form ℂ) (coefficient : ℂ) (N : ℕ)
    (hdifference : hConicDifference Rzero = 0) :
    RatFunc.eval (RingHom.id ℂ) 0
      (hReciprocalRatFuncRingHom
        (hHardOddNorm Rzero coefficient N)) = 0 := by
  rw [h_reciprocal_hHardOddNorm_eval_zero]
  have hA : RatFunc.eval (RingHom.id ℂ) 0
      (hReciprocalRatFuncRingHom (hConicDifference Rzero)) = 0 := by
    rw [hdifference, map_zero, RatFunc.eval_zero]
  rw [hA]
  ring

/-- The descended base case of an odd hard decomposition gives the ordinary
tail endpoint through the reciprocal chart. -/
theorem hHardOddConicDifferenceZeroMaximalIdealTails_not_hasInjectiveRepresentative
    (R Rzero : Form ℂ) (coefficient : ℂ) (N : ℕ)
    (hR : R.IsHomogeneous N)
    (hdecomposition :
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N)
    (hNodd : Odd N) (hcoefficient : coefficient ≠ 0)
    (hdifference : hConicDifference Rzero = 0)
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
    exists_hHardOddOrdinarySourceBranchData_of_reciprocal_norm_zero
      R Rzero coefficient N hR hdecomposition hNodd
        (h_reciprocal_hHardOddNorm_ne_zero_of_conicDifference_eq_zero
          Rzero coefficient N hNodd hcoefficient hdifference)
        (h_reciprocal_hHardOddNorm_eval_zero_of_conicDifference_eq_zero
          Rzero coefficient N hdifference)
  exact
    hHardOddOrdinarySourceBranchMaximalIdealTails_not_hasInjectiveRepresentative
      R N hR data representative hanalytic hzero htail

end OnLeConjecture.DThree
