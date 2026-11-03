/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HRatFuncAnalyticFactor

/-!
# Analytic collisions in the reciprocal H chart

Reciprocal parameter zero represents parameter infinity.  The reciprocal
conic coordinates are analytic units there, and profile degree loss is their
exact collision order.
-/

public section

open Filter Set
open scoped Topology Polynomial WithZero

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- The second first coordinate in the reciprocal chart. -/
@[expose]
noncomputable def hReciprocalCollisionX (lambda : ℂ) : ℂ :=
  hMinusParamXNumerator.eval lambda /
    hMinusParamDenominator.eval lambda

/-- The first weighted second coordinate in the reciprocal chart. -/
@[expose]
noncomputable def hReciprocalCollisionW (lambda : ℂ) : ℂ :=
  hMinusParamWNumerator.eval lambda /
    hMinusParamFunctionDenominator.eval lambda

/-- The second weighted second coordinate in the reciprocal chart. -/
@[expose]
noncomputable def hReciprocalCollisionCapitalW (lambda : ℂ) : ℂ :=
  hMinusParamCapitalWNumerator.eval lambda /
    hMinusParamFunctionDenominator.eval lambda

theorem analyticAt_hReciprocalCollisionX :
    AnalyticAt ℂ hReciprocalCollisionX 0 := by
  have hnum : AnalyticAt ℂ
      (fun lambda : ℂ ↦ hMinusParamXNumerator.eval lambda) 0 := by
    simpa using analyticAt_polynomial_eval_add
      (hMinusParamXNumerator (K := ℂ)) 0
  have hden : AnalyticAt ℂ
      (fun lambda : ℂ ↦ hMinusParamDenominator.eval lambda) 0 := by
    simpa using analyticAt_polynomial_eval_add
      (hMinusParamDenominator (K := ℂ)) 0
  exact hnum.div hden (by norm_num [hMinusParamDenominator])

theorem analyticAt_hReciprocalCollisionW :
    AnalyticAt ℂ hReciprocalCollisionW 0 := by
  have hnum : AnalyticAt ℂ
      (fun lambda : ℂ ↦ hMinusParamWNumerator.eval lambda) 0 := by
    simpa using analyticAt_polynomial_eval_add
      (hMinusParamWNumerator (K := ℂ)) 0
  have hden : AnalyticAt ℂ
      (fun lambda : ℂ ↦
        hMinusParamFunctionDenominator.eval lambda) 0 := by
    simpa using analyticAt_polynomial_eval_add
      (hMinusParamFunctionDenominator (K := ℂ)) 0
  exact hnum.div hden (by norm_num [hMinusParamFunctionDenominator,
    hMinusParamDenominator])

theorem analyticAt_hReciprocalCollisionCapitalW :
    AnalyticAt ℂ hReciprocalCollisionCapitalW 0 := by
  have hnum : AnalyticAt ℂ
      (fun lambda : ℂ ↦
        hMinusParamCapitalWNumerator.eval lambda) 0 := by
    simpa using analyticAt_polynomial_eval_add
      (hMinusParamCapitalWNumerator (K := ℂ)) 0
  have hden : AnalyticAt ℂ
      (fun lambda : ℂ ↦
        hMinusParamFunctionDenominator.eval lambda) 0 := by
    simpa using analyticAt_polynomial_eval_add
      (hMinusParamFunctionDenominator (K := ℂ)) 0
  exact hnum.div hden (by norm_num [hMinusParamFunctionDenominator,
    hMinusParamDenominator])

/-- Reciprocal substitution preserves the two fibre equations. -/
theorem h_minus_param_fibre_equations :
    hP 1 (hMinusParamW (K := ℂ)) =
        hP hMinusParamX hMinusParamCapitalW ∧
      hQ 1 (hMinusParamW (K := ℂ)) =
        hQ hMinusParamX hMinusParamCapitalW := by
  obtain ⟨hPfiber, hQfiber⟩ :=
    h_conic_param_fibre_equations (K := ℂ)
  constructor
  · have hPform :
        hFormEval 1 (hConicParamW (K := ℂ)) (hPForm (K := ℂ)) =
          hFormEval (hConicParamX (K := ℂ))
            (hConicParamCapitalW (K := ℂ)) (hPForm (K := ℂ)) := by
      simpa only [hFormEval_hPForm] using hPfiber
    have hmapped := congrArg
      (hReciprocalRatFuncRingHom (K := ℂ)) hPform
    change hReciprocalRatFuncRingHom
        (hFormEval 1 hConicParamW (hPForm (K := ℂ))) =
      hReciprocalRatFuncRingHom
        (hFormEval hConicParamX hConicParamCapitalW hPForm) at hmapped
    rw [h_reciprocalRatFuncRingHom_hFormEval,
      h_reciprocalRatFuncRingHom_hFormEval] at hmapped
    simpa only [
      h_reciprocalRatFuncRingHom_hConicParamX,
      h_reciprocalRatFuncRingHom_hConicParamW,
      h_reciprocalRatFuncRingHom_hConicParamCapitalW,
      map_one, hFormEval_hPForm] using hmapped
  · have hQform :
        hFormEval 1 (hConicParamW (K := ℂ)) (hQForm (K := ℂ)) =
          hFormEval (hConicParamX (K := ℂ))
            (hConicParamCapitalW (K := ℂ)) (hQForm (K := ℂ)) := by
      simpa only [hFormEval_hQForm] using hQfiber
    have hmapped := congrArg
      (hReciprocalRatFuncRingHom (K := ℂ)) hQform
    change hReciprocalRatFuncRingHom
        (hFormEval 1 hConicParamW (hQForm (K := ℂ))) =
      hReciprocalRatFuncRingHom
        (hFormEval hConicParamX hConicParamCapitalW hQForm) at hmapped
    rw [h_reciprocalRatFuncRingHom_hFormEval,
      h_reciprocalRatFuncRingHom_hFormEval] at hmapped
    simpa only [
      h_reciprocalRatFuncRingHom_hConicParamX,
      h_reciprocalRatFuncRingHom_hConicParamW,
      h_reciprocalRatFuncRingHom_hConicParamCapitalW,
      map_one, hFormEval_hQForm] using hmapped

/-- Evaluation of the reciprocal coordinates gives one fibre whenever their
displayed denominators do not vanish. -/
theorem h_reciprocal_collision_fibre_at
    (lambda : ℂ)
    (hden : hMinusParamDenominator.eval lambda ≠ 0)
    (hfunction : hMinusParamFunctionDenominator.eval lambda ≠ 0) :
    hP 1 (hReciprocalCollisionW lambda) =
        hP (hReciprocalCollisionX lambda)
          (hReciprocalCollisionCapitalW lambda) ∧
      hQ 1 (hReciprocalCollisionW lambda) =
        hQ (hReciprocalCollisionX lambda)
          (hReciprocalCollisionCapitalW lambda) := by
  obtain ⟨hxRegular, hwRegular, hcapitalWRegular⟩ :
      HRatFuncRegularAt lambda (hMinusParamX (K := ℂ)) ∧
        HRatFuncRegularAt lambda hMinusParamW ∧
        HRatFuncRegularAt lambda hMinusParamCapitalW := by
    refine ⟨?_, ?_, ?_⟩
    · exact hRatFuncRegularAt_of_denom_dvd
        (RatFunc.denom_div_dvd hMinusParamXNumerator
          hMinusParamDenominator) hden
    · exact hRatFuncRegularAt_of_denom_dvd
        (RatFunc.denom_div_dvd hMinusParamWNumerator
          hMinusParamFunctionDenominator) hfunction
    · exact hRatFuncRegularAt_of_denom_dvd
        (RatFunc.denom_div_dvd hMinusParamCapitalWNumerator
          hMinusParamFunctionDenominator) hfunction
  have honeRegular : HRatFuncRegularAt lambda (1 : RatFunc ℂ) := by
    simpa using hRatFuncRegularAt_algebraMap (K := ℂ) lambda 1
  have hPeval := congrArg (RatFunc.eval (RingHom.id ℂ) lambda)
    h_minus_param_fibre_equations.1
  have hQeval := congrArg (RatFunc.eval (RingHom.id ℂ) lambda)
    h_minus_param_fibre_equations.2
  rw [← hFormEval_hPForm (K := ℂ),
    ← hFormEval_hPForm (K := ℂ),
    h_ratFunc_eval_hFormEval lambda _ _ hPForm honeRegular hwRegular,
    h_ratFunc_eval_hFormEval lambda _ _ hPForm
      hxRegular hcapitalWRegular,
    hMinusParamW, hMinusParamX, hMinusParamCapitalW,
    h_ratFunc_eval_algebraMap_div lambda hMinusParamWNumerator
      hMinusParamFunctionDenominator hfunction,
    h_ratFunc_eval_algebraMap_div lambda hMinusParamXNumerator
      hMinusParamDenominator hden,
    h_ratFunc_eval_algebraMap_div lambda hMinusParamCapitalWNumerator
      hMinusParamFunctionDenominator hfunction,
    RatFunc.eval_one] at hPeval
  rw [← hFormEval_hQForm (K := ℂ),
    ← hFormEval_hQForm (K := ℂ),
    h_ratFunc_eval_hFormEval lambda _ _ hQForm honeRegular hwRegular,
    h_ratFunc_eval_hFormEval lambda _ _ hQForm
      hxRegular hcapitalWRegular,
    hMinusParamW, hMinusParamX, hMinusParamCapitalW,
    h_ratFunc_eval_algebraMap_div lambda hMinusParamWNumerator
      hMinusParamFunctionDenominator hfunction,
    h_ratFunc_eval_algebraMap_div lambda hMinusParamXNumerator
      hMinusParamDenominator hden,
    h_ratFunc_eval_algebraMap_div lambda hMinusParamCapitalWNumerator
      hMinusParamFunctionDenominator hfunction,
    RatFunc.eval_one] at hQeval
  simpa only [hMinusParamX, hMinusParamW, hMinusParamCapitalW,
    hReciprocalCollisionX, hReciprocalCollisionW,
    hReciprocalCollisionCapitalW, hFormEval_hPForm,
    hFormEval_hQForm] using And.intro hPeval hQeval

/-- Evaluation of the reciprocal conic difference is the third coordinate
difference in the reciprocal chart. -/
theorem h_reciprocal_collision_difference_at
    (R : MvPolynomial (Fin 2) ℂ) (lambda : ℂ)
    (hden : hMinusParamDenominator.eval lambda ≠ 0)
    (hfunction : hMinusParamFunctionDenominator.eval lambda ≠ 0) :
    hFormEval 1 (hReciprocalCollisionW lambda) R -
        hFormEval (hReciprocalCollisionX lambda)
          (hReciprocalCollisionCapitalW lambda) R =
      RatFunc.eval (RingHom.id ℂ) lambda
        (hReciprocalRatFuncRingHom (hConicDifference R)) := by
  obtain ⟨hxRegular, hwRegular, hcapitalWRegular⟩ :
      HRatFuncRegularAt lambda (hMinusParamX (K := ℂ)) ∧
        HRatFuncRegularAt lambda hMinusParamW ∧
        HRatFuncRegularAt lambda hMinusParamCapitalW := by
    refine ⟨?_, ?_, ?_⟩
    · exact hRatFuncRegularAt_of_denom_dvd
        (RatFunc.denom_div_dvd hMinusParamXNumerator
          hMinusParamDenominator) hden
    · exact hRatFuncRegularAt_of_denom_dvd
        (RatFunc.denom_div_dvd hMinusParamWNumerator
          hMinusParamFunctionDenominator) hfunction
    · exact hRatFuncRegularAt_of_denom_dvd
        (RatFunc.denom_div_dvd hMinusParamCapitalWNumerator
          hMinusParamFunctionDenominator) hfunction
  have honeRegular : HRatFuncRegularAt lambda (1 : RatFunc ℂ) := by
    simpa using hRatFuncRegularAt_algebraMap (K := ℂ) lambda 1
  have hfirstRegular := hRatFuncRegularAt_hFormEval lambda
    1 (hMinusParamW (K := ℂ)) R honeRegular hwRegular
  have hsecondRegular := hRatFuncRegularAt_hFormEval lambda
    (hMinusParamX (K := ℂ)) hMinusParamCapitalW R
      hxRegular hcapitalWRegular
  rw [h_reciprocalRatFuncRingHom_hConicDifference]
  rw [h_ratFunc_eval_sub lambda _ _ hfirstRegular hsecondRegular,
    h_ratFunc_eval_hFormEval lambda _ _ R honeRegular hwRegular,
    h_ratFunc_eval_hFormEval lambda _ _ R hxRegular hcapitalWRegular,
    hMinusParamW, hMinusParamX, hMinusParamCapitalW,
    h_ratFunc_eval_algebraMap_div lambda hMinusParamWNumerator
      hMinusParamFunctionDenominator hfunction,
    h_ratFunc_eval_algebraMap_div lambda hMinusParamXNumerator
      hMinusParamDenominator hden,
    h_ratFunc_eval_algebraMap_div lambda hMinusParamCapitalWNumerator
      hMinusParamFunctionDenominator hfunction,
    RatFunc.eval_one]
  rfl

/-- Both reciprocal coordinate denominators remain nonzero near zero. -/
theorem eventually_hReciprocalCollision_denominators :
    ∀ᶠ lambda in nhds (0 : ℂ),
      hMinusParamDenominator.eval lambda ≠ 0 ∧
        hMinusParamFunctionDenominator.eval lambda ≠ 0 := by
  have hdenAt : hMinusParamDenominator (K := ℂ).eval 0 ≠ 0 := by
    norm_num [hMinusParamDenominator]
  have hfunctionAt :
      hMinusParamFunctionDenominator (K := ℂ).eval 0 ≠ 0 := by
    norm_num [hMinusParamFunctionDenominator, hMinusParamDenominator]
  have hdenTendsto : Tendsto
      (fun lambda : ℂ ↦ hMinusParamDenominator.eval lambda)
      (nhds 0) (nhds (hMinusParamDenominator.eval 0)) := by
    have hcontinuous := (analyticAt_polynomial_eval_add
      (hMinusParamDenominator (K := ℂ)) 0).continuousAt
    change Tendsto
      (fun lambda : ℂ ↦ hMinusParamDenominator.eval (0 + lambda))
      (nhds 0) (nhds (hMinusParamDenominator.eval (0 + 0))) at hcontinuous
    simpa using hcontinuous
  have hfunctionTendsto : Tendsto
      (fun lambda : ℂ ↦ hMinusParamFunctionDenominator.eval lambda)
      (nhds 0) (nhds (hMinusParamFunctionDenominator.eval 0)) := by
    have hcontinuous := (analyticAt_polynomial_eval_add
      (hMinusParamFunctionDenominator (K := ℂ)) 0).continuousAt
    change Tendsto
      (fun lambda : ℂ ↦
        hMinusParamFunctionDenominator.eval (0 + lambda))
      (nhds 0)
      (nhds (hMinusParamFunctionDenominator.eval (0 + 0))) at hcontinuous
    simpa using hcontinuous
  filter_upwards [hdenTendsto.eventually_ne hdenAt,
    hfunctionTendsto.eventually_ne hfunctionAt] with lambda hden hfunction
  exact ⟨hden, hfunction⟩

/-- The reciprocal collision coordinates lie in one fibre near zero. -/
theorem eventually_hReciprocalCollision_fibre :
    ∀ᶠ lambda in nhds (0 : ℂ),
      hP 1 (hReciprocalCollisionW lambda) =
          hP (hReciprocalCollisionX lambda)
            (hReciprocalCollisionCapitalW lambda) ∧
        hQ 1 (hReciprocalCollisionW lambda) =
          hQ (hReciprocalCollisionX lambda)
            (hReciprocalCollisionCapitalW lambda) := by
  filter_upwards [eventually_hReciprocalCollision_denominators]
    with lambda hdenominators
  exact h_reciprocal_collision_fibre_at lambda
    hdenominators.1 hdenominators.2

/-- Evaluation of the reciprocal conic difference agrees with the analytic
coordinate difference near zero. -/
theorem eventually_hReciprocalCollision_difference
    (R : MvPolynomial (Fin 2) ℂ) :
    ∀ᶠ lambda in nhds (0 : ℂ),
      hFormEval 1 (hReciprocalCollisionW lambda) R -
          hFormEval (hReciprocalCollisionX lambda)
            (hReciprocalCollisionCapitalW lambda) R =
        RatFunc.eval (RingHom.id ℂ) lambda
          (hReciprocalRatFuncRingHom (hConicDifference R)) := by
  filter_upwards [eventually_hReciprocalCollision_denominators]
    with lambda hdenominators
  exact h_reciprocal_collision_difference_at R lambda
    hdenominators.1 hdenominators.2

/-- A strict profile degree drop gives normalized source branch data in the
reciprocal chart. -/
theorem exists_hReciprocalSourceBranchData_of_profile_degree_drop
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X]) (hp : p ≠ 0)
    (hdegree : p.natDegree < N / 2 + 2 * N)
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (N / 2) N)) :
    Nonempty (HNormalizedSourceBranchData a N R) := by
  obtain ⟨order, horderPositive, horderInfinity⟩ :=
    h_order_at_infinity_positive_of_pole_profile_degree_drop
      (N / 2) N hp hdegree hrepresentation
  have horderZero :
      hFiniteOrderAt (0 : ℂ)
          (hReciprocalRatFuncRingHom (hConicDifference R)) =
        WithZero.exp (order : ℤ) := by
    rw [h_finite_order_reciprocalRatFuncRingHom]
    exact horderInfinity
  obtain ⟨rawUnit, hrawUnit, hrawUnit0, hfactor⟩ :=
    exists_analyticAt_ratFunc_eval_factor_of_finite_order
      (hReciprocalRatFuncRingHom (hConicDifference R)) order horderZero
  have hrawFactor : ∀ᶠ lambda in nhds 0,
      hFormEval 1 (hReciprocalCollisionW lambda) R -
          hFormEval (hReciprocalCollisionX lambda)
            (hReciprocalCollisionCapitalW lambda) R =
        lambda ^ order * rawUnit lambda := by
    filter_upwards [eventually_hReciprocalCollision_difference R,
      hfactor] with lambda hdifference hfactorAt
    rw [hdifference, hfactorAt]
  have hw0 : hReciprocalCollisionW 0 ≠ 0 := by
    norm_num [hReciprocalCollisionW, hMinusParamWNumerator,
      hMinusParamFunctionDenominator, hMinusParamDenominator]
  have hcapitalW0 : hReciprocalCollisionCapitalW 0 ≠ 0 := by
    norm_num [hReciprocalCollisionCapitalW,
      hMinusParamCapitalWNumerator, hMinusParamFunctionDenominator,
      hMinusParamDenominator]
  have hdistinct : (1 : ℂ) ≠ hReciprocalCollisionX 0 := by
    norm_num [hReciprocalCollisionX, hMinusParamXNumerator,
      hMinusParamDenominator]
  exact exists_hNormalizedSourceBranchData
    a N ha R hR
      (fun _ : ℂ ↦ 1) hReciprocalCollisionW
      hReciprocalCollisionX hReciprocalCollisionCapitalW
      analyticAt_const analyticAt_hReciprocalCollisionW
      analyticAt_hReciprocalCollisionX
      analyticAt_hReciprocalCollisionCapitalW
      hw0 hcapitalW0 (Or.inl hdistinct)
      eventually_hReciprocalCollision_fibre
      order rawUnit (by omega) hrawUnit hrawUnit0 hrawFactor

/-- Weighted order tails exclude an injective representative when the fixed
profile has a strict degree drop. -/
theorem hReciprocalDegreeDropWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X]) (hp : p ≠ 0)
    (hdegree : p.natDegree < N / 2 + 2 * N)
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (N / 2) N))
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hQuadraticWeightedPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (hQuadraticWeightedDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨data⟩ :=
    exists_hReciprocalSourceBranchData_of_profile_degree_drop
      a N ha R hR p hp hdegree hrepresentation
  exact hNormalizedWeightedOrderTails_not_hasInjectiveRepresentative
    a N ha R hR data representative hanalytic hzero htail

end OnLeConjecture.DThree
