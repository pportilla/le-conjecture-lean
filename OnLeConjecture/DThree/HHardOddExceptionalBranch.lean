/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HHardOddFiniteBoundaryBranch
public import OnLeConjecture.DThree.HHardOddZeroSecondPersistence
public import OnLeConjecture.DThree.HExceptionalProfileSource

/-!
# Ordinary hard H branches with one zero second coordinate

At an exceptional regular profile point, ramification by the square of the
branch parameter makes the vanishing weighted coordinate a square. The
resulting source branch lies in the transverse zero coordinate chart.
-/

public section

noncomputable section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- A nonzero polynomial remains nonzero on every neighborhood after a
translated square substitution. -/
theorem not_eventually_polynomial_eval_add_sq_eq_zero
    (p : ℂ[X]) (hp : p ≠ 0) (z : ℂ) :
    ¬ ∀ᶠ lambda in nhds 0, p.eval (z + lambda ^ 2) = 0 := by
  let order := p.rootMultiplicity z
  let quotient := p /ₘ (Polynomial.X - Polynomial.C z) ^ order
  have hfactor :
      (Polynomial.X - Polynomial.C z) ^ order * quotient = p :=
    Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p z
  have hquotient : quotient.eval z ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero z hp
  have hquotientAnalytic : AnalyticAt ℂ
      (fun lambda : ℂ ↦ quotient.eval (z + lambda ^ 2)) 0 := by
    have hparameter : AnalyticAt ℂ
        (fun lambda : ℂ ↦ z + lambda ^ 2) 0 :=
      analyticAt_const.add (analyticAt_id.pow 2)
    simpa [aeval_def] using hparameter.aeval_polynomial quotient
  have hquotientEventually : ∀ᶠ lambda in nhds 0,
      quotient.eval (z + lambda ^ 2) ≠ 0 := by
    have ht := hquotientAnalytic.continuousAt.tendsto
    change Tendsto (fun lambda : ℂ ↦ quotient.eval (z + lambda ^ 2))
      (nhds 0) (nhds (quotient.eval (z + 0 ^ 2))) at ht
    have hquotient' : quotient.eval (z + 0 ^ 2) ≠ 0 := by
      simpa using hquotient
    exact ht.eventually_ne hquotient'
  intro hzero
  have hfalse : ∀ᶠ lambda in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
      False := by
    filter_upwards [hzero.filter_mono nhdsWithin_le_nhds,
      hquotientEventually.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with
      lambda hpZero hquotientAt hlambda
    have hfactorEval := congrArg
      (fun q : ℂ[X] ↦ q.eval (z + lambda ^ 2)) hfactor
    rw [Polynomial.eval_mul, Polynomial.eval_pow] at hfactorEval
    have hlinear :
        (Polynomial.X - Polynomial.C z).eval
          (z + lambda ^ 2) = lambda ^ 2 := by
      simp
    rw [hlinear, hpZero] at hfactorEval
    exact (mul_ne_zero
      (pow_ne_zero order (pow_ne_zero 2 (by simpa using hlambda)))
      hquotientAt) hfactorEval
  obtain ⟨lambda, hfalseAt⟩ := hfalse.exists
  exact hfalseAt

/-- A regular hard norm root whose second profile coordinate vanishes gives
ordinary source data in the zero coordinate chart. -/
theorem
    exists_hHardOddZeroSecondSourceBranchData_of_capitalW_norm_root
    (R Rzero : Form ℂ) (coefficient : ℂ) (N : ℕ)
    (hR : R.IsHomogeneous N)
    (hdecomposition :
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N)
    (hNodd : Odd N)
    (numerator : ℂ[X]) (hnumerator : numerator ≠ 0)
    (z : ℂ) (hroot : numerator.IsRoot z)
    (hlinear : z + 1 ≠ 0)
    (hden : hConicParamDenominator.eval z ≠ 0)
    (hprofile :
      (hPoleProfileDenominator (K := ℂ) (2 * N) (4 * N)).eval z ≠ 0)
    (hW : hRegularProfileW z 0 ≠ 0)
    (hCapitalW : hRegularProfileCapitalW z 0 = 0)
    (hrepresentation :
      hHardOddNorm Rzero coefficient N =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (2 * N) (4 * N))) :
    Nonempty (HHardOddZeroSecondSourceBranchData R) := by
  have hfunction := h_regular_function_denominator_ne_zero hlinear hden
  have hone := h_one_factor_ne_zero_of_regular_W_ne_zero z hW
  have hcapitalFactor := h_capitalW_factor_root_of_regular_value_zero
    z hfunction hone hCapitalW
  obtain ⟨s, S, hsRat, hSRat, hsection⟩ :=
    exists_signs_hard_difference_zero_of_norm_numerator_root
      Rzero coefficient z N hNodd numerator hrepresentation hroot hprofile
  have hs : s ^ 2 = hRegularProfileW z 0 := by
    have heq := h_regular_profile_W_eq_eval z 0
      (by simpa using hfunction)
    rw [add_zero] at heq
    rw [heq]
    exact hsRat
  have hS : S ^ 2 = hRegularProfileCapitalW z 0 := by
    have heq := h_regular_profile_capitalW_eq_eval z 0
      (by simpa using hfunction)
    rw [add_zero] at heq
    rw [heq]
    exact hSRat
  have hs0 : s ≠ 0 := by
    intro hsZero
    apply hW
    rw [← hs, hsZero, zero_pow (by norm_num : 2 ≠ 0)]
  have hSZero : S = 0 := by
    apply sq_eq_zero_iff.mp
    rw [hS, hCapitalW]
  have hsection' :
      hFormEval 1 (hRegularProfileW z 0) Rzero -
          hFormEval (hRegularProfileX z 0)
            (hRegularProfileCapitalW z 0) Rzero +
        coefficient * (s ^ N - S ^ N) = 0 := by
    rw [h_ratFunc_eval_hConicDifference_regular
      Rzero z hlinear hden] at hsection
    have hxEq := h_regular_profile_X_eq_eval z 0 (by simpa using hden)
    have hwEq := h_regular_profile_W_eq_eval z 0
      (by simpa using hfunction)
    have hcapitalWEq := h_regular_profile_capitalW_eq_eval z 0
      (by simpa using hfunction)
    rw [add_zero] at hxEq hwEq hcapitalWEq
    rw [← hxEq, ← hwEq, ← hcapitalWEq] at hsection
    exact hsection
  let w : ℂ → ℂ := fun lambda ↦
    hRegularProfileW z (lambda ^ 2)
  have hwRamified0 : w 0 ≠ 0 := by
    change hRegularProfileW z (0 ^ 2) ≠ 0
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact hW
  have hsRamified : s ^ 2 = w 0 := by
    change s ^ 2 = hRegularProfileW z (0 ^ 2)
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact hs
  obtain ⟨y, hyAnalytic, hyZero, hyPower⟩ :=
    exists_analyticAt_root_with_value w
      (by simpa only [w] using
        analyticAt_hRegularProfileW_ramified 1 (by norm_num) z hfunction)
      hwRamified0 2 (by norm_num) s hsRamified
  let capitalUnit := hCapitalWZeroUnit 1 z
  have hcapitalUnitAnalytic : AnalyticAt ℂ capitalUnit 0 :=
    analyticAt_hCapitalWZeroUnit 1 (by norm_num) z hfunction
  have hcapitalUnit0 : capitalUnit 0 ≠ 0 :=
    hCapitalWZeroUnit_zero_ne_zero
      1 (by norm_num) z hfunction hone hcapitalFactor
  obtain ⟨Vzero, hVzero⟩ := IsAlgClosed.exists_pow_nat_eq
    (capitalUnit 0) (by norm_num : 0 < 2)
  obtain ⟨V, hVAnalytic, hVZero, hVPower⟩ :=
    exists_analyticAt_root_with_value capitalUnit hcapitalUnitAnalytic
      hcapitalUnit0 2 (by norm_num) Vzero hVzero
  let Y : ℂ → ℂ := fun lambda ↦ lambda * V lambda
  have hYAnalytic : AnalyticAt ℂ Y 0 := analyticAt_id.mul hVAnalytic
  have hYZero : Y 0 = S := by
    simp only [Y, zero_mul, hSZero]
  have hYPower (lambda : ℂ) :
      Y lambda ^ 2 = hRegularProfileCapitalW z (lambda ^ 2) := by
    change (lambda * V lambda) ^ 2 = _
    rw [mul_pow, hVPower]
    simpa only [capitalUnit] using
      (h_regular_profile_capitalW_ramified_factor
        1 z lambda hcapitalFactor).symm
  let raw : ℂ → ℂ := fun lambda ↦
    hFormEval 1 (w lambda) Rzero -
      hFormEval (hRegularProfileX z (lambda ^ 2))
        (hRegularProfileCapitalW z (lambda ^ 2)) Rzero +
      coefficient * (y lambda ^ N - Y lambda ^ N)
  have hrawAnalytic : AnalyticAt ℂ raw 0 := by
    dsimp only [raw]
    have hfirst := analyticAt_eval_finTwo Rzero (fun _ ↦ 1) w
      analyticAt_const
      (by simpa only [w] using
        analyticAt_hRegularProfileW_ramified 1 (by norm_num) z hfunction)
    have hsecond := analyticAt_eval_finTwo Rzero
      (fun lambda ↦ hRegularProfileX z (lambda ^ 2))
      (fun lambda ↦ hRegularProfileCapitalW z (lambda ^ 2))
      (by simpa using
        (analyticAt_hRegularProfileX_ramified
          1 (by norm_num) z hden))
      (by simpa using
        (analyticAt_hRegularProfileCapitalW_ramified
          1 (by norm_num) z hfunction))
    have hsum := (hfirst.sub hsecond).add
      ((analyticAt_const : AnalyticAt ℂ
          (fun _ : ℂ ↦ coefficient) 0).mul
        ((hyAnalytic.pow N).sub (hYAnalytic.pow N)))
    convert hsum using 1
    funext lambda
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
      hFormEval_eq_eval_finTwo]
  have hrawZero : raw 0 = 0 := by
    dsimp only [raw, w]
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), hyZero, hYZero]
    exact hsection'
  have hdelta : Tendsto (fun lambda : ℂ ↦ lambda ^ 2)
      (nhds 0) (nhds 0) := by
    have hdeltaAnalytic : AnalyticAt ℂ
        (fun lambda : ℂ ↦ lambda ^ 2) 0 := analyticAt_id.pow 2
    have ht := hdeltaAnalytic.continuousAt
    change Tendsto (fun lambda : ℂ ↦ lambda ^ 2)
      (nhds 0) (nhds (0 ^ 2)) at ht
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using ht
  have hparameter : Tendsto (fun delta : ℂ ↦ z + delta)
      (nhds 0) (nhds z) := by
    simpa using
      (tendsto_const_nhds.add tendsto_id :
        Tendsto (fun delta : ℂ ↦ z + delta)
          (nhds 0) (nhds (z + 0)))
  have hlinearBase : ∀ᶠ delta in nhds 0, z + delta + 1 ≠ 0 :=
    (hparameter.add_const 1).eventually_ne hlinear
  have hdenBase : ∀ᶠ delta in nhds 0,
      hConicParamDenominator.eval (z + delta) ≠ 0 := by
    have ht : Tendsto
        (fun delta : ℂ ↦ hConicParamDenominator.eval (z + delta))
        (nhds 0) (nhds (hConicParamDenominator.eval z)) := by
      have hc :=
        (analyticAt_polynomial_eval_add hConicParamDenominator z).continuousAt
      change Tendsto
        (fun delta : ℂ ↦ hConicParamDenominator.eval (z + delta))
        (nhds 0)
        (nhds (hConicParamDenominator.eval (z + 0))) at hc
      simpa using hc
    exact ht.eventually_ne hden
  have hprofileBase : ∀ᶠ delta in nhds 0,
      (hPoleProfileDenominator (K := ℂ) (2 * N) (4 * N)).eval
        (z + delta) ≠ 0 := by
    have ht : Tendsto
        (fun delta : ℂ ↦
          (hPoleProfileDenominator (2 * N) (4 * N)).eval
            (z + delta))
        (nhds 0)
        (nhds ((hPoleProfileDenominator (2 * N) (4 * N)).eval z)) := by
      have hc := (analyticAt_polynomial_eval_add
        (hPoleProfileDenominator (2 * N) (4 * N)) z).continuousAt
      change Tendsto
        (fun delta : ℂ ↦
          (hPoleProfileDenominator (2 * N) (4 * N)).eval
            (z + delta))
        (nhds 0)
        (nhds ((hPoleProfileDenominator (2 * N) (4 * N)).eval
          (z + 0))) at hc
      simpa using hc
    exact ht.eventually_ne hprofile
  have hlinearEventually : ∀ᶠ lambda in nhds 0,
      z + lambda ^ 2 + 1 ≠ 0 := hdelta.eventually hlinearBase
  have hdenEventually : ∀ᶠ lambda in nhds 0,
      hConicParamDenominator.eval (z + lambda ^ 2) ≠ 0 :=
    hdelta.eventually hdenBase
  have hprofileEventually : ∀ᶠ lambda in nhds 0,
      (hPoleProfileDenominator (K := ℂ) (2 * N) (4 * N)).eval
        (z + lambda ^ 2) ≠ 0 := hdelta.eventually hprofileBase
  let secondFactor : ℂ → ℂ := fun lambda ↦
    hFormEval 1 (w lambda) Rzero -
      hFormEval (hRegularProfileX z (lambda ^ 2))
        (hRegularProfileCapitalW z (lambda ^ 2)) Rzero +
      coefficient * (y lambda ^ N + Y lambda ^ N)
  let thirdFactor : ℂ → ℂ := fun lambda ↦
    hFormEval 1 (w lambda) Rzero -
      hFormEval (hRegularProfileX z (lambda ^ 2))
        (hRegularProfileCapitalW z (lambda ^ 2)) Rzero +
      coefficient * (-y lambda ^ N - Y lambda ^ N)
  let fourthFactor : ℂ → ℂ := fun lambda ↦
    hFormEval 1 (w lambda) Rzero -
      hFormEval (hRegularProfileX z (lambda ^ 2))
        (hRegularProfileCapitalW z (lambda ^ 2)) Rzero +
      coefficient * (-y lambda ^ N + Y lambda ^ N)
  have hnormProduct : ∀ᶠ lambda in nhds 0,
      RatFunc.eval (RingHom.id ℂ) (z + lambda ^ 2)
          (hHardOddNorm Rzero coefficient N) =
        raw lambda * secondFactor lambda * thirdFactor lambda *
          fourthFactor lambda := by
    filter_upwards [hlinearEventually, hdenEventually] with
      lambda hlinearAt hdenAt
    have hfunctionAt := h_regular_function_denominator_ne_zero
      hlinearAt hdenAt
    obtain ⟨hxRegular, hwRegular, hcapitalWRegular⟩ :=
      h_conic_param_regular_at (z + lambda ^ 2) hlinearAt hdenAt
    have hyRat : y lambda ^ 2 =
        RatFunc.eval (RingHom.id ℂ) (z + lambda ^ 2) hConicParamW := by
      rw [← h_regular_profile_W_eq_eval z (lambda ^ 2) hfunctionAt]
      exact hyPower lambda
    have hYRat : Y lambda ^ 2 =
        RatFunc.eval (RingHom.id ℂ) (z + lambda ^ 2)
          hConicParamCapitalW := by
      rw [← h_regular_profile_capitalW_eq_eval
        z (lambda ^ 2) hfunctionAt]
      exact hYPower lambda
    have hproduct := hHardOddNorm_eval_eq_sign_product
      Rzero coefficient (z + lambda ^ 2) (y lambda) (Y lambda) N
        (hConicDifference_regular_at Rzero (z + lambda ^ 2)
          hlinearAt hdenAt) hwRegular hcapitalWRegular hyRat hYRat
    rw [h_ratFunc_eval_hConicDifference_regular
        Rzero (z + lambda ^ 2) hlinearAt hdenAt,
      ← h_regular_profile_X_eq_eval z (lambda ^ 2) hdenAt,
      ← h_regular_profile_W_eq_eval z (lambda ^ 2) hfunctionAt,
      ← h_regular_profile_capitalW_eq_eval
        z (lambda ^ 2) hfunctionAt] at hproduct
    simpa only [raw, w, secondFactor, thirdFactor, fourthFactor]
      using hproduct
  have hrawNotZero : ¬ ∀ᶠ lambda in nhds 0, raw lambda = 0 := by
    intro hrawEventually
    have hnormZero : ∀ᶠ lambda in nhds 0,
        RatFunc.eval (RingHom.id ℂ) (z + lambda ^ 2)
          (hHardOddNorm Rzero coefficient N) = 0 := by
      filter_upwards [hnormProduct, hrawEventually] with
        lambda hproduct hrawAt
      rw [hproduct, hrawAt]
      simp
    have hnumeratorZero : ∀ᶠ lambda in nhds 0,
        numerator.eval (z + lambda ^ 2) = 0 := by
      filter_upwards [hnormZero, hprofileEventually] with
        lambda hnormAt hprofileAt
      have heval := congrArg
        (RatFunc.eval (RingHom.id ℂ) (z + lambda ^ 2)) hrepresentation
      rw [h_ratFunc_eval_algebraMap_div (z + lambda ^ 2) numerator
        (hPoleProfileDenominator (2 * N) (4 * N)) hprofileAt] at heval
      rw [hnormAt] at heval
      exact (div_eq_zero_iff.mp heval.symm).resolve_right hprofileAt
    exact (not_eventually_polynomial_eval_add_sq_eq_zero
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
  let T : ℂ → ℂ := fun lambda ↦ Y lambda / y lambda
  let point : ℂ → Fin 2 → ℂ := fun lambda ↦
    ![1 / y lambda,
      hRegularProfileX z (lambda ^ 2) / y lambda]
  let firstX : ℂ := 1 / s
  let secondX : ℂ := hRegularProfileX z 0 / s
  let unit : ℂ → ℂ := fun lambda ↦ rawUnit lambda / y lambda ^ N
  have hTAnalytic : AnalyticAt ℂ T 0 := by
    exact hYAnalytic.div hyAnalytic
      (by simpa only [hyZero] using hs0)
  have hpointAnalytic : AnalyticAt ℂ point 0 := by
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · exact analyticAt_const.div hyAnalytic
        (by simpa only [hyZero] using hs0)
    · have hxRamified : AnalyticAt ℂ
          (fun lambda : ℂ ↦ hRegularProfileX z (lambda ^ 2)) 0 := by
        simpa using
          (analyticAt_hRegularProfileX_ramified
            1 (by norm_num) z hden)
      exact hxRamified.div hyAnalytic
        (by simpa only [hyZero] using hs0)
  have hTZero : T 0 = 0 := by
    simp [T, Y]
  have hpointZero : point 0 = ![firstX, secondX] := by
    funext i
    fin_cases i
    · simp [point, firstX, hyZero]
    · simp [point, secondX, hyZero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have hyTendsto : Tendsto y (nhds 0) (nhds s) := by
    have ht := hyAnalytic.continuousAt
    change Tendsto y (nhds 0) (nhds (y 0)) at ht
    rw [hyZero] at ht
    exact ht
  have hyEventually : ∀ᶠ lambda in nhds 0, y lambda ≠ 0 :=
    hyTendsto.eventually_ne hs0
  have hfibreReparam := hdelta.eventually
    (eventually_hRegularProfile_fibre z hlinear hden)
  have hplaneZero : ∀ᶠ lambda in nhds 0,
      hZeroSecondPlaneDifference 1 T (lambda, point lambda) = 0 := by
    filter_upwards [hfibreReparam, hyEventually] with
      lambda hfibreAt hyAt
    obtain ⟨hPfiber, hQfiber⟩ := h_normalized_fibre
      1 1 (y lambda) (hRegularProfileX z (lambda ^ 2)) (Y lambda)
        (w lambda) (hRegularProfileCapitalW z (lambda ^ 2))
        (by simpa using hyPower lambda) (by simpa using hYPower lambda)
        hyAt hfibreAt.1 hfibreAt.2
    funext i
    fin_cases i
    · simpa [hZeroSecondPlaneDifference, point, T]
        using sub_eq_zero.mpr hPfiber
    · simpa [hZeroSecondPlaneDifference, point, T]
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
      MvPolynomial.eval ![point lambda 0, 1] R -
          MvPolynomial.eval ![point lambda 1, T lambda] R =
        lambda ^ order * unit lambda := by
    filter_upwards [hyEventually, hrawFactor] with
      lambda hyAt hrawAt
    have hnormalized := normalized_ordinary_form_difference
      R N hR (y lambda) (hRegularProfileX z (lambda ^ 2))
        (Y lambda) hyAt
    rw [hHardOddDecomposition_eval R Rzero coefficient
        1 (y lambda) N hdecomposition,
      hHardOddDecomposition_eval R Rzero coefficient
        (hRegularProfileX z (lambda ^ 2)) (Y lambda) N hdecomposition,
      hyPower lambda, hYPower lambda] at hnormalized
    change MvPolynomial.eval ![1 / y lambda, 1] R -
      MvPolynomial.eval
        ![hRegularProfileX z (lambda ^ 2) / y lambda,
          Y lambda / y lambda] R = _
    rw [hnormalized]
    have hrawExpression :
        hFormEval 1 (w lambda) Rzero + coefficient * y lambda ^ N -
          (hFormEval (hRegularProfileX z (lambda ^ 2))
              (hRegularProfileCapitalW z (lambda ^ 2)) Rzero +
            coefficient * Y lambda ^ N) = raw lambda := by
      simp only [raw]
      ring
    rw [hrawExpression, hrawAt]
    simp only [unit]
    ring
  let data : HHardOddZeroSecondSourceBranchData R :=
    { T := T
      point := point
      firstX := firstX
      secondX := secondX
      order := order
      unit := unit
      T_analyticAt := hTAnalytic
      point_analyticAt := hpointAnalytic
      T_zero := hTZero
      point_zero := hpointZero
      plane_zero := hplaneZero
      order_pos := horder
      unit_analyticAt := hunitAnalytic
      unit_zero_ne := hunitZero
      third_factor := hthirdFactor }
  exact ⟨data⟩

/-- A regular hard norm root with zero second profile coordinate is
incompatible with an injective representative under ordinary tails. -/
theorem
    hHardOddCapitalWZeroNormRootMaximalIdealTails_not_hasInjectiveRepresentative
    (R Rzero : Form ℂ) (coefficient : ℂ) (N : ℕ)
    (hR : R.IsHomogeneous N)
    (hdecomposition :
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N)
    (hNodd : Odd N)
    (numerator : ℂ[X]) (hnumerator : numerator ≠ 0)
    (z : ℂ) (hroot : numerator.IsRoot z)
    (hlinear : z + 1 ≠ 0)
    (hden : hConicParamDenominator.eval z ≠ 0)
    (hprofile :
      (hPoleProfileDenominator (K := ℂ) (2 * N) (4 * N)).eval z ≠ 0)
    (hW : hRegularProfileW z 0 ≠ 0)
    (hCapitalW : hRegularProfileCapitalW z 0 = 0)
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
    exists_hHardOddZeroSecondSourceBranchData_of_capitalW_norm_root
      R Rzero coefficient N hR hdecomposition hNodd numerator hnumerator
        z hroot hlinear hden hprofile hW hCapitalW hrepresentation
  exact
    hHardOddZeroSecondMaximalIdealTails_not_hasInjectiveRepresentative
      R N hR data representative hanalytic hzero htail

/-- A regular hard norm root whose first profile coordinate vanishes gives
ordinary source data after interchanging the two fibre points. -/
theorem exists_hHardOddZeroSecondSourceBranchData_of_W_norm_root
    (R Rzero : Form ℂ) (coefficient : ℂ) (N : ℕ)
    (hR : R.IsHomogeneous N)
    (hdecomposition :
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N)
    (hNodd : Odd N)
    (numerator : ℂ[X]) (hnumerator : numerator ≠ 0)
    (z : ℂ) (hroot : numerator.IsRoot z)
    (hlinear : z + 1 ≠ 0)
    (hden : hConicParamDenominator.eval z ≠ 0)
    (hprofile :
      (hPoleProfileDenominator (K := ℂ) (2 * N) (4 * N)).eval z ≠ 0)
    (hW : hRegularProfileW z 0 = 0)
    (hCapitalW : hRegularProfileCapitalW z 0 ≠ 0)
    (hrepresentation :
      hHardOddNorm Rzero coefficient N =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (2 * N) (4 * N))) :
    Nonempty (HHardOddZeroSecondSourceBranchData R) := by
  have hfunction := h_regular_function_denominator_ne_zero hlinear hden
  have hone := h_one_factor_ne_zero_of_regular_capitalW_ne_zero
    z hCapitalW
  have hWFactor := h_W_factor_root_of_regular_value_zero
    z hfunction hone hW
  obtain ⟨s, S, hsRat, hSRat, hsection⟩ :=
    exists_signs_hard_difference_zero_of_norm_numerator_root
      Rzero coefficient z N hNodd numerator hrepresentation hroot hprofile
  have hs : s ^ 2 = hRegularProfileW z 0 := by
    have heq := h_regular_profile_W_eq_eval z 0
      (by simpa using hfunction)
    rw [add_zero] at heq
    rw [heq]
    exact hsRat
  have hS : S ^ 2 = hRegularProfileCapitalW z 0 := by
    have heq := h_regular_profile_capitalW_eq_eval z 0
      (by simpa using hfunction)
    rw [add_zero] at heq
    rw [heq]
    exact hSRat
  have hsZero : s = 0 := by
    apply sq_eq_zero_iff.mp
    rw [hs, hW]
  have hS0 : S ≠ 0 := by
    intro hSZero
    apply hCapitalW
    rw [← hS, hSZero, zero_pow (by norm_num : 2 ≠ 0)]
  have hsection' :
      hFormEval 1 (hRegularProfileW z 0) Rzero -
          hFormEval (hRegularProfileX z 0)
            (hRegularProfileCapitalW z 0) Rzero +
        coefficient * (s ^ N - S ^ N) = 0 := by
    rw [h_ratFunc_eval_hConicDifference_regular
      Rzero z hlinear hden] at hsection
    have hxEq := h_regular_profile_X_eq_eval z 0 (by simpa using hden)
    have hwEq := h_regular_profile_W_eq_eval z 0
      (by simpa using hfunction)
    have hcapitalWEq := h_regular_profile_capitalW_eq_eval z 0
      (by simpa using hfunction)
    rw [add_zero] at hxEq hwEq hcapitalWEq
    rw [← hxEq, ← hwEq, ← hcapitalWEq] at hsection
    exact hsection
  let w : ℂ → ℂ := fun lambda ↦
    hRegularProfileCapitalW z (lambda ^ 2)
  have hwRamified0 : w 0 ≠ 0 := by
    change hRegularProfileCapitalW z (0 ^ 2) ≠ 0
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact hCapitalW
  have hSRamified : S ^ 2 = w 0 := by
    change S ^ 2 = hRegularProfileCapitalW z (0 ^ 2)
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact hS
  obtain ⟨y, hyAnalytic, hyZero, hyPower⟩ :=
    exists_analyticAt_root_with_value w
      (by simpa only [w] using
        (analyticAt_hRegularProfileCapitalW_ramified
          1 (by norm_num) z hfunction))
      hwRamified0 2 (by norm_num) S hSRamified
  let WUnit := hWZeroUnit 1 z
  have hWUnitAnalytic : AnalyticAt ℂ WUnit 0 :=
    analyticAt_hWZeroUnit 1 (by norm_num) z hfunction
  have hWUnit0 : WUnit 0 ≠ 0 :=
    hWZeroUnit_zero_ne_zero
      1 (by norm_num) z hfunction hone hWFactor
  obtain ⟨Vzero, hVzero⟩ := IsAlgClosed.exists_pow_nat_eq
    (WUnit 0) (by norm_num : 0 < 2)
  obtain ⟨V, hVAnalytic, hVZero, hVPower⟩ :=
    exists_analyticAt_root_with_value WUnit hWUnitAnalytic
      hWUnit0 2 (by norm_num) Vzero hVzero
  let Y : ℂ → ℂ := fun lambda ↦ lambda * V lambda
  have hYAnalytic : AnalyticAt ℂ Y 0 := analyticAt_id.mul hVAnalytic
  have hYZero : Y 0 = s := by
    simp only [Y, zero_mul, hsZero]
  have hYPower (lambda : ℂ) :
      Y lambda ^ 2 = hRegularProfileW z (lambda ^ 2) := by
    change (lambda * V lambda) ^ 2 = _
    rw [mul_pow, hVPower]
    simpa only [WUnit] using
      (h_regular_profile_W_ramified_factor
        1 z lambda hWFactor).symm
  let raw : ℂ → ℂ := fun lambda ↦
    hFormEval (hRegularProfileX z (lambda ^ 2)) (w lambda) Rzero -
      hFormEval 1 (hRegularProfileW z (lambda ^ 2)) Rzero +
      coefficient * (y lambda ^ N - Y lambda ^ N)
  have hrawAnalytic : AnalyticAt ℂ raw 0 := by
    dsimp only [raw]
    have hfirst := analyticAt_eval_finTwo Rzero
      (fun lambda ↦ hRegularProfileX z (lambda ^ 2)) w
      (by simpa using
        (analyticAt_hRegularProfileX_ramified
          1 (by norm_num) z hden))
      (by simpa only [w] using
        (analyticAt_hRegularProfileCapitalW_ramified
          1 (by norm_num) z hfunction))
    have hsecond := analyticAt_eval_finTwo Rzero (fun _ ↦ 1)
      (fun lambda ↦ hRegularProfileW z (lambda ^ 2))
      analyticAt_const
      (by simpa using
        (analyticAt_hRegularProfileW_ramified
          1 (by norm_num) z hfunction))
    have hsum := (hfirst.sub hsecond).add
      ((analyticAt_const : AnalyticAt ℂ
          (fun _ : ℂ ↦ coefficient) 0).mul
        ((hyAnalytic.pow N).sub (hYAnalytic.pow N)))
    convert hsum using 1
    funext lambda
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
      hFormEval_eq_eval_finTwo]
  have hrawZero : raw 0 = 0 := by
    dsimp only [raw, w]
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), hyZero, hYZero]
    linear_combination -hsection'
  have hdelta : Tendsto (fun lambda : ℂ ↦ lambda ^ 2)
      (nhds 0) (nhds 0) := by
    have hdeltaAnalytic : AnalyticAt ℂ
        (fun lambda : ℂ ↦ lambda ^ 2) 0 := analyticAt_id.pow 2
    have ht := hdeltaAnalytic.continuousAt
    change Tendsto (fun lambda : ℂ ↦ lambda ^ 2)
      (nhds 0) (nhds (0 ^ 2)) at ht
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using ht
  have hparameter : Tendsto (fun delta : ℂ ↦ z + delta)
      (nhds 0) (nhds z) := by
    simpa using
      (tendsto_const_nhds.add tendsto_id :
        Tendsto (fun delta : ℂ ↦ z + delta)
          (nhds 0) (nhds (z + 0)))
  have hlinearBase : ∀ᶠ delta in nhds 0, z + delta + 1 ≠ 0 :=
    (hparameter.add_const 1).eventually_ne hlinear
  have hdenBase : ∀ᶠ delta in nhds 0,
      hConicParamDenominator.eval (z + delta) ≠ 0 := by
    have ht : Tendsto
        (fun delta : ℂ ↦ hConicParamDenominator.eval (z + delta))
        (nhds 0) (nhds (hConicParamDenominator.eval z)) := by
      have hc :=
        (analyticAt_polynomial_eval_add hConicParamDenominator z).continuousAt
      change Tendsto
        (fun delta : ℂ ↦ hConicParamDenominator.eval (z + delta))
        (nhds 0)
        (nhds (hConicParamDenominator.eval (z + 0))) at hc
      simpa using hc
    exact ht.eventually_ne hden
  have hprofileBase : ∀ᶠ delta in nhds 0,
      (hPoleProfileDenominator (K := ℂ) (2 * N) (4 * N)).eval
        (z + delta) ≠ 0 := by
    have ht : Tendsto
        (fun delta : ℂ ↦
          (hPoleProfileDenominator (2 * N) (4 * N)).eval
            (z + delta))
        (nhds 0)
        (nhds ((hPoleProfileDenominator (2 * N) (4 * N)).eval z)) := by
      have hc := (analyticAt_polynomial_eval_add
        (hPoleProfileDenominator (2 * N) (4 * N)) z).continuousAt
      change Tendsto
        (fun delta : ℂ ↦
          (hPoleProfileDenominator (2 * N) (4 * N)).eval
            (z + delta))
        (nhds 0)
        (nhds ((hPoleProfileDenominator (2 * N) (4 * N)).eval
          (z + 0))) at hc
      simpa using hc
    exact ht.eventually_ne hprofile
  have hlinearEventually : ∀ᶠ lambda in nhds 0,
      z + lambda ^ 2 + 1 ≠ 0 := hdelta.eventually hlinearBase
  have hdenEventually : ∀ᶠ lambda in nhds 0,
      hConicParamDenominator.eval (z + lambda ^ 2) ≠ 0 :=
    hdelta.eventually hdenBase
  have hprofileEventually : ∀ᶠ lambda in nhds 0,
      (hPoleProfileDenominator (K := ℂ) (2 * N) (4 * N)).eval
        (z + lambda ^ 2) ≠ 0 := hdelta.eventually hprofileBase
  let secondFactor : ℂ → ℂ := fun lambda ↦
    hFormEval 1 (hRegularProfileW z (lambda ^ 2)) Rzero -
      hFormEval (hRegularProfileX z (lambda ^ 2)) (w lambda) Rzero +
      coefficient * (Y lambda ^ N + y lambda ^ N)
  let thirdFactor : ℂ → ℂ := fun lambda ↦
    hFormEval 1 (hRegularProfileW z (lambda ^ 2)) Rzero -
      hFormEval (hRegularProfileX z (lambda ^ 2)) (w lambda) Rzero +
      coefficient * (-Y lambda ^ N - y lambda ^ N)
  let fourthFactor : ℂ → ℂ := fun lambda ↦
    hFormEval 1 (hRegularProfileW z (lambda ^ 2)) Rzero -
      hFormEval (hRegularProfileX z (lambda ^ 2)) (w lambda) Rzero +
      coefficient * (-Y lambda ^ N + y lambda ^ N)
  have hnormProduct : ∀ᶠ lambda in nhds 0,
      RatFunc.eval (RingHom.id ℂ) (z + lambda ^ 2)
          (hHardOddNorm Rzero coefficient N) =
        (-raw lambda) * secondFactor lambda * thirdFactor lambda *
          fourthFactor lambda := by
    filter_upwards [hlinearEventually, hdenEventually] with
      lambda hlinearAt hdenAt
    have hfunctionAt := h_regular_function_denominator_ne_zero
      hlinearAt hdenAt
    obtain ⟨hxRegular, hwRegular, hcapitalWRegular⟩ :=
      h_conic_param_regular_at (z + lambda ^ 2) hlinearAt hdenAt
    have hYRat : Y lambda ^ 2 =
        RatFunc.eval (RingHom.id ℂ) (z + lambda ^ 2) hConicParamW := by
      rw [← h_regular_profile_W_eq_eval z (lambda ^ 2) hfunctionAt]
      exact hYPower lambda
    have hyRat : y lambda ^ 2 =
        RatFunc.eval (RingHom.id ℂ) (z + lambda ^ 2)
          hConicParamCapitalW := by
      rw [← h_regular_profile_capitalW_eq_eval
        z (lambda ^ 2) hfunctionAt]
      exact hyPower lambda
    have hproduct := hHardOddNorm_eval_eq_sign_product
      Rzero coefficient (z + lambda ^ 2) (Y lambda) (y lambda) N
        (hConicDifference_regular_at Rzero (z + lambda ^ 2)
          hlinearAt hdenAt) hwRegular hcapitalWRegular hYRat hyRat
    rw [h_ratFunc_eval_hConicDifference_regular
        Rzero (z + lambda ^ 2) hlinearAt hdenAt,
      ← h_regular_profile_X_eq_eval z (lambda ^ 2) hdenAt,
      ← h_regular_profile_W_eq_eval z (lambda ^ 2) hfunctionAt,
      ← h_regular_profile_capitalW_eq_eval
        z (lambda ^ 2) hfunctionAt] at hproduct
    have hfirst :
        hFormEval 1 (hRegularProfileW z (lambda ^ 2)) Rzero -
              hFormEval (hRegularProfileX z (lambda ^ 2))
                (hRegularProfileCapitalW z (lambda ^ 2)) Rzero +
            coefficient * (Y lambda ^ N - y lambda ^ N) =
          -raw lambda := by
      simp only [raw, w]
      ring
    rw [hfirst] at hproduct
    simpa only [w, secondFactor, thirdFactor, fourthFactor]
      using hproduct
  have hrawNotZeroW : ¬ ∀ᶠ lambda in nhds 0, raw lambda = 0 := by
    intro hrawEventually
    have hnormZero : ∀ᶠ lambda in nhds 0,
        RatFunc.eval (RingHom.id ℂ) (z + lambda ^ 2)
          (hHardOddNorm Rzero coefficient N) = 0 := by
      filter_upwards [hnormProduct, hrawEventually] with
        lambda hproduct hrawAt
      rw [hproduct, hrawAt]
      simp
    have hnumeratorZero : ∀ᶠ lambda in nhds 0,
        numerator.eval (z + lambda ^ 2) = 0 := by
      filter_upwards [hnormZero, hprofileEventually] with
        lambda hnormAt hprofileAt
      have heval := congrArg
        (RatFunc.eval (RingHom.id ℂ) (z + lambda ^ 2)) hrepresentation
      rw [h_ratFunc_eval_algebraMap_div (z + lambda ^ 2) numerator
        (hPoleProfileDenominator (2 * N) (4 * N)) hprofileAt] at heval
      rw [hnormAt] at heval
      exact (div_eq_zero_iff.mp heval.symm).resolve_right hprofileAt
    exact (not_eventually_polynomial_eval_add_sq_eq_zero
      numerator hnumerator z) hnumeratorZero
  obtain ⟨order, rawUnit, hrawUnitAnalytic, hrawUnitZero,
      hrawFactorRaw⟩ :=
    hrawAnalytic.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hrawNotZeroW
  have hrawFactor : ∀ᶠ lambda in nhds 0,
      raw lambda = lambda ^ order * rawUnit lambda := by
    simpa only [sub_zero, smul_eq_mul] using hrawFactorRaw
  have horder : 0 < order := by
    apply Nat.pos_of_ne_zero
    intro horderZero
    have hfactorAt := hrawFactor.self_of_nhds
    rw [horderZero, pow_zero, one_mul, hrawZero] at hfactorAt
    exact hrawUnitZero hfactorAt.symm
  let T : ℂ → ℂ := fun lambda ↦ Y lambda / y lambda
  let point : ℂ → Fin 2 → ℂ := fun lambda ↦
    ![hRegularProfileX z (lambda ^ 2) / y lambda,
      1 / y lambda]
  let firstX : ℂ := hRegularProfileX z 0 / S
  let secondX : ℂ := 1 / S
  let unit : ℂ → ℂ := fun lambda ↦ rawUnit lambda / y lambda ^ N
  have hTAnalytic : AnalyticAt ℂ T 0 := by
    exact hYAnalytic.div hyAnalytic
      (by simpa only [hyZero] using hS0)
  have hpointAnalytic : AnalyticAt ℂ point 0 := by
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · have hxRamified : AnalyticAt ℂ
          (fun lambda : ℂ ↦ hRegularProfileX z (lambda ^ 2)) 0 := by
        simpa using
          (analyticAt_hRegularProfileX_ramified
            1 (by norm_num) z hden)
      exact hxRamified.div hyAnalytic
        (by simpa only [hyZero] using hS0)
    · exact analyticAt_const.div hyAnalytic
        (by simpa only [hyZero] using hS0)
  have hTZero : T 0 = 0 := by
    simp [T, Y]
  have hpointZero : point 0 = ![firstX, secondX] := by
    funext i
    fin_cases i
    · simp [point, firstX, hyZero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    · simp [point, secondX, hyZero]
  have hyTendsto : Tendsto y (nhds 0) (nhds S) := by
    have ht := hyAnalytic.continuousAt
    change Tendsto y (nhds 0) (nhds (y 0)) at ht
    rw [hyZero] at ht
    exact ht
  have hyEventually : ∀ᶠ lambda in nhds 0, y lambda ≠ 0 :=
    hyTendsto.eventually_ne hS0
  have hfibreReparam := hdelta.eventually
    (eventually_hRegularProfile_fibre z hlinear hden)
  have hplaneZero : ∀ᶠ lambda in nhds 0,
      hZeroSecondPlaneDifference 1 T (lambda, point lambda) = 0 := by
    filter_upwards [hfibreReparam, hyEventually] with
      lambda hfibreAt hyAt
    obtain ⟨hPfiber, hQfiber⟩ := h_normalized_fibre
      1 (hRegularProfileX z (lambda ^ 2)) (y lambda) 1 (Y lambda)
        (w lambda) (hRegularProfileW z (lambda ^ 2))
        (by simpa using hyPower lambda) (by simpa using hYPower lambda)
        hyAt hfibreAt.1.symm hfibreAt.2.symm
    funext i
    fin_cases i
    · simpa [hZeroSecondPlaneDifference, point, T]
        using sub_eq_zero.mpr hPfiber
    · simpa [hZeroSecondPlaneDifference, point, T]
        using sub_eq_zero.mpr hQfiber
  have hunitAnalytic : AnalyticAt ℂ unit 0 := by
    exact hrawUnitAnalytic.div (hyAnalytic.pow N)
      (by
        rw [hyZero]
        exact pow_ne_zero N hS0)
  have hunitZero : unit 0 ≠ 0 := by
    change rawUnit 0 / y 0 ^ N ≠ 0
    rw [hyZero]
    exact div_ne_zero hrawUnitZero (pow_ne_zero N hS0)
  have hthirdFactor : ∀ᶠ lambda in nhds 0,
      MvPolynomial.eval ![point lambda 0, 1] R -
          MvPolynomial.eval ![point lambda 1, T lambda] R =
        lambda ^ order * unit lambda := by
    filter_upwards [hyEventually, hrawFactor] with
      lambda hyAt hrawAt
    have hnormalized := normalized_ordinary_form_difference_general
      R N hR (hRegularProfileX z (lambda ^ 2)) (y lambda)
        1 (Y lambda) hyAt
    rw [hHardOddDecomposition_eval R Rzero coefficient
        (hRegularProfileX z (lambda ^ 2)) (y lambda) N hdecomposition,
      hHardOddDecomposition_eval R Rzero coefficient
        1 (Y lambda) N hdecomposition,
      hyPower lambda, hYPower lambda] at hnormalized
    change MvPolynomial.eval
        ![hRegularProfileX z (lambda ^ 2) / y lambda, 1] R -
      MvPolynomial.eval ![1 / y lambda, Y lambda / y lambda] R = _
    rw [hnormalized]
    have hrawExpression :
        hFormEval (hRegularProfileX z (lambda ^ 2)) (w lambda) Rzero +
              coefficient * y lambda ^ N -
            (hFormEval 1 (hRegularProfileW z (lambda ^ 2)) Rzero +
              coefficient * Y lambda ^ N) = raw lambda := by
      simp only [raw]
      ring
    rw [hrawExpression, hrawAt]
    simp only [unit]
    ring
  let data : HHardOddZeroSecondSourceBranchData R :=
    { T := T
      point := point
      firstX := firstX
      secondX := secondX
      order := order
      unit := unit
      T_analyticAt := hTAnalytic
      point_analyticAt := hpointAnalytic
      T_zero := hTZero
      point_zero := hpointZero
      plane_zero := hplaneZero
      order_pos := horder
      unit_analyticAt := hunitAnalytic
      unit_zero_ne := hunitZero
      third_factor := hthirdFactor }
  exact ⟨data⟩

/-- A regular hard norm root with zero first profile coordinate is
incompatible with an injective representative under ordinary tails. -/
theorem
    hHardOddWZeroNormRootMaximalIdealTails_not_hasInjectiveRepresentative
    (R Rzero : Form ℂ) (coefficient : ℂ) (N : ℕ)
    (hR : R.IsHomogeneous N)
    (hdecomposition :
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N)
    (hNodd : Odd N)
    (numerator : ℂ[X]) (hnumerator : numerator ≠ 0)
    (z : ℂ) (hroot : numerator.IsRoot z)
    (hlinear : z + 1 ≠ 0)
    (hden : hConicParamDenominator.eval z ≠ 0)
    (hprofile :
      (hPoleProfileDenominator (K := ℂ) (2 * N) (4 * N)).eval z ≠ 0)
    (hW : hRegularProfileW z 0 = 0)
    (hCapitalW : hRegularProfileCapitalW z 0 ≠ 0)
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
    exists_hHardOddZeroSecondSourceBranchData_of_W_norm_root
      R Rzero coefficient N hR hdecomposition hNodd numerator hnumerator
        z hroot hlinear hden hprofile hW hCapitalW hrepresentation
  exact
    hHardOddZeroSecondMaximalIdealTails_not_hasInjectiveRepresentative
      R N hR data representative hanalytic hzero htail

end OnLeConjecture.DThree
