/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HHardOddAlternative
public import OnLeConjecture.DThree.HHardOddOrdinaryPersistence

/-!
# Ordinary source branches from regular hard norm roots

A regular zero of the hard norm selects one of four analytic sign factors.
The product identity and the nonzero norm numerator show that the selected
factor has finite positive order. Normalizing its two source points gives the
ordinary collision data used by analytic persistence.
-/

public section

noncomputable section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- A nonzero polynomial cannot vanish on a neighborhood after translation. -/
theorem not_eventually_polynomial_eval_add_eq_zero
    (p : ℂ[X]) (hp : p ≠ 0) (z : ℂ) :
    ¬ ∀ᶠ lambda in nhds 0, p.eval (z + lambda) = 0 := by
  let k := p.rootMultiplicity z
  let quotient := p /ₘ (Polynomial.X - Polynomial.C z) ^ k
  have hfactor :
      (Polynomial.X - Polynomial.C z) ^ k * quotient = p := by
    exact Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p z
  have hquotient : quotient.eval z ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero z hp
  have hquotientAnalytic : AnalyticAt ℂ
      (fun lambda : ℂ ↦ quotient.eval (z + lambda)) 0 :=
    analyticAt_polynomial_eval_add quotient z
  have hquotientEventually : ∀ᶠ lambda in nhds 0,
      quotient.eval (z + lambda) ≠ 0 := by
    have ht := hquotientAnalytic.continuousAt.tendsto
    change Tendsto (fun lambda : ℂ ↦ quotient.eval (z + lambda))
      (nhds 0) (nhds (quotient.eval (z + 0))) at ht
    have hquotient' : quotient.eval (z + 0) ≠ 0 := by
      simpa using hquotient
    exact ht.eventually_ne hquotient'
  intro hzero
  have hfalse : ∀ᶠ lambda in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
      False := by
    filter_upwards [hzero.filter_mono nhdsWithin_le_nhds,
      hquotientEventually.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with lambda hpZero hquotientAt hlambda
    have hfactorEval := congrArg
      (fun q : ℂ[X] ↦ q.eval (z + lambda)) hfactor
    rw [Polynomial.eval_mul, Polynomial.eval_pow] at hfactorEval
    have hlinear :
        (Polynomial.X - Polynomial.C z).eval (z + lambda) = lambda := by
      simp
    rw [hlinear, hpZero] at hfactorEval
    exact (mul_ne_zero (pow_ne_zero k (by simpa using hlambda))
      hquotientAt) hfactorEval
  obtain ⟨lambda, hfalseAt⟩ := hfalse.exists
  exact hfalseAt

/-- Evaluation of a bivariate polynomial along two analytic coordinate
functions is analytic. -/
theorem analyticAt_eval_finTwo
    (R : Form ℂ) (x t : ℂ → ℂ)
    (hx : AnalyticAt ℂ x 0) (ht : AnalyticAt ℂ t 0) :
    AnalyticAt ℂ (fun lambda ↦
      MvPolynomial.eval ![x lambda, t lambda] R) 0 := by
  have hcoordinate (i : Fin 2) : AnalyticAt ℂ
      (fun lambda ↦ (![x lambda, t lambda] : Fin 2 → ℂ) i) 0 := by
    fin_cases i
    · simpa using hx
    · simpa using ht
  simpa [MvPolynomial.aeval_def] using
    AnalyticAt.aeval_mvPolynomial hcoordinate R

/-- The weighted form evaluation agrees with evaluation at the corresponding
two coordinate vector. -/
theorem hFormEval_eq_eval_finTwo
    (R : Form ℂ) (x w : ℂ) :
    hFormEval x w R = MvPolynomial.eval ![x, w] R := by
  simp only [hFormEval, MvPolynomial.eval]
  congr 1
  funext i
  fin_cases i
  all_goals simp

/-- Ordinary homogeneity gives the quotient formula used to normalize the
first source second coordinate to one. -/
theorem normalized_ordinary_form_difference
    (R : Form ℂ) (N : ℕ) (hR : R.IsHomogeneous N)
    (y X Y : ℂ) (hy : y ≠ 0) :
    MvPolynomial.eval ![1 / y, 1] R -
        MvPolynomial.eval ![X / y, Y / y] R =
      (MvPolynomial.eval ![1, y] R -
        MvPolynomial.eval ![X, Y] R) / y ^ N := by
  have hweights : (![1, 1] : Fin 2 → ℕ) = 1 := by
    funext i
    fin_cases i
    all_goals rfl
  have hRweighted : R.IsWeightedHomogeneous ![1, 1] N := by
    rw [hweights]
    exact hR
  have hfirst := eval_weighted_smul_of_isWeightedHomogeneous
    hRweighted y ![1 / y, 1]
  have hsecond := eval_weighted_smul_of_isWeightedHomogeneous
    hRweighted y ![X / y, Y / y]
  have hfirstCoordinates :
      (fun i : Fin 2 ↦ y ^ (![1, 1] : Fin 2 → ℕ) i *
        (![1 / y, 1] : Fin 2 → ℂ) i) = ![1, y] := by
    funext i
    fin_cases i
    · simp [hy]
    · simp
  have hsecondCoordinates :
      (fun i : Fin 2 ↦ y ^ (![1, 1] : Fin 2 → ℕ) i *
        (![X / y, Y / y] : Fin 2 → ℂ) i) = ![X, Y] := by
    funext i
    fin_cases i
    all_goals simp
    all_goals field_simp
  rw [hfirstCoordinates] at hfirst
  rw [hsecondCoordinates] at hsecond
  have hfirst' : MvPolynomial.eval ![1, y] R =
      y ^ N * MvPolynomial.eval ![1 / y, 1] R := by
    exact hfirst
  have hsecond' : MvPolynomial.eval ![X, Y] R =
      y ^ N * MvPolynomial.eval ![X / y, Y / y] R := by
    exact hsecond
  apply (eq_div_iff (pow_ne_zero N hy)).2
  calc
    (MvPolynomial.eval ![1 / y, 1] R -
          MvPolynomial.eval ![X / y, Y / y] R) * y ^ N =
        y ^ N * MvPolynomial.eval ![1 / y, 1] R -
          y ^ N * MvPolynomial.eval ![X / y, Y / y] R := by ring
    _ = MvPolynomial.eval ![1, y] R -
        MvPolynomial.eval ![X, Y] R := by
      rw [← hfirst', ← hsecond']

/-- A regular numerator root of the hard norm with two nonzero second
coordinates gives ordinary source branch data. -/
theorem exists_hHardOddOrdinarySourceBranchData_of_regular_norm_root
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
    (hCapitalW : hRegularProfileCapitalW z 0 ≠ 0)
    (hX : hRegularProfileX z 0 ≠ 1)
    (hrepresentation :
      hHardOddNorm Rzero coefficient N =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (2 * N) (4 * N))) :
    Nonempty (HHardOddOrdinarySourceBranchData R) := by
  have hfunction := h_regular_function_denominator_ne_zero hlinear hden
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
  obtain ⟨y, hyAnalytic, hyZero, hyPower⟩ :=
    exists_analyticAt_root_with_value
      (hRegularProfileW z) (analyticAt_hRegularProfileW z hfunction)
        hW 2 (by norm_num) s hs
  obtain ⟨Y, hYAnalytic, hYZero, hYPower⟩ :=
    exists_analyticAt_root_with_value
      (hRegularProfileCapitalW z)
        (analyticAt_hRegularProfileCapitalW z hfunction)
          hCapitalW 2 (by norm_num) S hS
  let raw : ℂ → ℂ := fun lambda ↦
    hFormEval 1 (hRegularProfileW z lambda) Rzero -
      hFormEval (hRegularProfileX z lambda)
        (hRegularProfileCapitalW z lambda) Rzero +
      coefficient * (y lambda ^ N - Y lambda ^ N)
  have hrawAnalytic : AnalyticAt ℂ raw 0 := by
    dsimp only [raw]
    have hfirst := analyticAt_eval_finTwo Rzero
      (fun _ ↦ 1) (hRegularProfileW z)
      analyticAt_const (analyticAt_hRegularProfileW z hfunction)
    have hsecond := analyticAt_eval_finTwo Rzero
      (hRegularProfileX z) (hRegularProfileCapitalW z)
      (analyticAt_hRegularProfileX z hden)
      (analyticAt_hRegularProfileCapitalW z hfunction)
    have hsum := (hfirst.sub hsecond).add
      ((analyticAt_const : AnalyticAt ℂ
          (fun _ : ℂ ↦ coefficient) 0).mul
        ((hyAnalytic.pow N).sub (hYAnalytic.pow N)))
    convert hsum using 1
    funext lambda
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
      hFormEval_eq_eval_finTwo]
  have hrawZero : raw 0 = 0 := by
    simpa [raw, hyZero, hYZero] using hsection'
  have hparameter : Tendsto (fun lambda : ℂ ↦ z + lambda)
      (nhds 0) (nhds z) := by
    simpa using
      (tendsto_const_nhds.add tendsto_id :
        Tendsto (fun lambda : ℂ ↦ z + lambda)
          (nhds 0) (nhds (z + 0)))
  have hlinearEventually : ∀ᶠ lambda in nhds 0,
      z + lambda + 1 ≠ 0 :=
    (hparameter.add_const 1).eventually_ne hlinear
  have hdenEventually : ∀ᶠ lambda in nhds 0,
      hConicParamDenominator.eval (z + lambda) ≠ 0 := by
    have ht : Tendsto
        (fun lambda : ℂ ↦ hConicParamDenominator.eval (z + lambda))
        (nhds 0) (nhds (hConicParamDenominator.eval z)) := by
      have hc :=
        (analyticAt_polynomial_eval_add hConicParamDenominator z).continuousAt
      change Tendsto
        (fun lambda : ℂ ↦ hConicParamDenominator.eval (z + lambda))
        (nhds 0)
        (nhds (hConicParamDenominator.eval (z + 0))) at hc
      simpa using hc
    exact ht.eventually_ne hden
  have hprofileEventually : ∀ᶠ lambda in nhds 0,
      (hPoleProfileDenominator (K := ℂ) (2 * N) (4 * N)).eval
        (z + lambda) ≠ 0 := by
    have ht : Tendsto
        (fun lambda : ℂ ↦
          (hPoleProfileDenominator (2 * N) (4 * N)).eval
            (z + lambda))
        (nhds 0)
        (nhds ((hPoleProfileDenominator (2 * N) (4 * N)).eval z)) := by
      have hc := (analyticAt_polynomial_eval_add
        (hPoleProfileDenominator (2 * N) (4 * N)) z).continuousAt
      change Tendsto
        (fun lambda : ℂ ↦
          (hPoleProfileDenominator (2 * N) (4 * N)).eval
            (z + lambda))
        (nhds 0)
        (nhds ((hPoleProfileDenominator (2 * N) (4 * N)).eval
          (z + 0))) at hc
      simpa using hc
    exact ht.eventually_ne hprofile
  let secondFactor : ℂ → ℂ := fun lambda ↦
    hFormEval 1 (hRegularProfileW z lambda) Rzero -
      hFormEval (hRegularProfileX z lambda)
        (hRegularProfileCapitalW z lambda) Rzero +
      coefficient * (y lambda ^ N + Y lambda ^ N)
  let thirdFactor : ℂ → ℂ := fun lambda ↦
    hFormEval 1 (hRegularProfileW z lambda) Rzero -
      hFormEval (hRegularProfileX z lambda)
        (hRegularProfileCapitalW z lambda) Rzero +
      coefficient * (-y lambda ^ N - Y lambda ^ N)
  let fourthFactor : ℂ → ℂ := fun lambda ↦
    hFormEval 1 (hRegularProfileW z lambda) Rzero -
      hFormEval (hRegularProfileX z lambda)
        (hRegularProfileCapitalW z lambda) Rzero +
      coefficient * (-y lambda ^ N + Y lambda ^ N)
  have hnormProduct : ∀ᶠ lambda in nhds 0,
      RatFunc.eval (RingHom.id ℂ) (z + lambda)
          (hHardOddNorm Rzero coefficient N) =
        raw lambda * secondFactor lambda * thirdFactor lambda *
          fourthFactor lambda := by
    filter_upwards [hlinearEventually, hdenEventually] with
      lambda hlinearAt hdenAt
    have hfunctionAt := h_regular_function_denominator_ne_zero
      hlinearAt hdenAt
    obtain ⟨hxRegular, hwRegular, hcapitalWRegular⟩ :=
      h_conic_param_regular_at (z + lambda) hlinearAt hdenAt
    have hyRat : y lambda ^ 2 =
        RatFunc.eval (RingHom.id ℂ) (z + lambda) hConicParamW := by
      rw [← h_regular_profile_W_eq_eval z lambda hfunctionAt]
      exact hyPower lambda
    have hYRat : Y lambda ^ 2 =
        RatFunc.eval (RingHom.id ℂ) (z + lambda)
          hConicParamCapitalW := by
      rw [← h_regular_profile_capitalW_eq_eval z lambda hfunctionAt]
      exact hYPower lambda
    have hproduct := hHardOddNorm_eval_eq_sign_product
      Rzero coefficient (z + lambda) (y lambda) (Y lambda) N
        (hConicDifference_regular_at Rzero (z + lambda)
          hlinearAt hdenAt) hwRegular hcapitalWRegular hyRat hYRat
    rw [h_ratFunc_eval_hConicDifference_regular
        Rzero (z + lambda) hlinearAt hdenAt,
      ← h_regular_profile_X_eq_eval z lambda hdenAt,
      ← h_regular_profile_W_eq_eval z lambda hfunctionAt,
      ← h_regular_profile_capitalW_eq_eval z lambda hfunctionAt]
      at hproduct
    simpa [raw, secondFactor, thirdFactor, fourthFactor] using hproduct
  have hrawNotZero : ¬ ∀ᶠ lambda in nhds 0, raw lambda = 0 := by
    intro hrawEventually
    have hnormZero : ∀ᶠ lambda in nhds 0,
        RatFunc.eval (RingHom.id ℂ) (z + lambda)
          (hHardOddNorm Rzero coefficient N) = 0 := by
      filter_upwards [hnormProduct, hrawEventually] with
        lambda hproduct hrawAt
      rw [hproduct, hrawAt]
      simp
    have hnumeratorZero : ∀ᶠ lambda in nhds 0,
        numerator.eval (z + lambda) = 0 := by
      filter_upwards [hnormZero, hprofileEventually] with
        lambda hnormAt hprofileAt
      have heval := congrArg
        (RatFunc.eval (RingHom.id ℂ) (z + lambda)) hrepresentation
      rw [h_ratFunc_eval_algebraMap_div (z + lambda) numerator
        (hPoleProfileDenominator (2 * N) (4 * N)) hprofileAt]
        at heval
      rw [hnormAt] at heval
      exact (div_eq_zero_iff.mp heval.symm).resolve_right hprofileAt
    exact (not_eventually_polynomial_eval_add_eq_zero
      numerator hnumerator z) hnumeratorZero
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
    ![hRegularProfileX z lambda / y lambda,
      Y lambda / y lambda]
  let secondX : ℂ := hRegularProfileX z 0 / s
  let secondT : ℂ := S / s
  let unit : ℂ → ℂ := fun lambda ↦ rawUnit lambda / y lambda ^ N
  have hfirstXAnalytic : AnalyticAt ℂ firstX 0 := by
    apply analyticAt_const.div hyAnalytic
    simpa [hyZero] using hs0
  have hsecondPointAnalytic : AnalyticAt ℂ secondPoint 0 := by
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · exact (analyticAt_hRegularProfileX z hden).div hyAnalytic
        (by simpa [hyZero] using hs0)
    · exact hYAnalytic.div hyAnalytic (by simpa [hyZero] using hs0)
  have hsecondPointZero : secondPoint 0 = ![secondX, secondT] := by
    funext i
    fin_cases i
    · simp [secondPoint, secondX, hyZero]
    · simp [secondPoint, secondT, hyZero, hYZero]
  have hsecondT : secondT ≠ 0 := div_ne_zero hS0 hs0
  have hchart : (firstX 0, 1) ≠ (secondX, secondT) := by
    intro hequal
    apply hX
    have hfirstCoordinate := congrArg Prod.fst hequal
    have hcoordinate : 1 / s = hRegularProfileX z 0 / s := by
      simpa [firstX, secondX, hyZero] using hfirstCoordinate
    exact ((div_left_inj' hs0).mp hcoordinate).symm
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
    filter_upwards [eventually_hRegularProfile_fibre z hlinear hden,
      hyEventually] with lambda hfibre hyAt
    obtain ⟨hPfiber, hQfiber⟩ := h_normalized_regular_fibre
      1 (y lambda) (Y lambda) (hRegularProfileX z lambda)
        (hRegularProfileW z lambda)
        (hRegularProfileCapitalW z lambda)
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
    have hnormalized := normalized_ordinary_form_difference
      R N hR (y lambda) (hRegularProfileX z lambda) (Y lambda) hyAt
    rw [hHardOddDecomposition_eval R Rzero coefficient 1 (y lambda) N
        hdecomposition,
      hHardOddDecomposition_eval R Rzero coefficient
        (hRegularProfileX z lambda) (Y lambda) N hdecomposition,
      hyPower lambda, hYPower lambda] at hnormalized
    change MvPolynomial.eval ![1 / y lambda, 1] R -
        MvPolynomial.eval
          ![hRegularProfileX z lambda / y lambda,
            Y lambda / y lambda] R = _
    rw [hnormalized]
    have hrawExpression :
        hFormEval 1 (hRegularProfileW z lambda) Rzero +
              coefficient * y lambda ^ N -
            (hFormEval (hRegularProfileX z lambda)
                (hRegularProfileCapitalW z lambda) Rzero +
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

/-- A regular hard norm root with two nonzero second coordinates is
incompatible with an injective representative under ordinary tails. -/
theorem hHardOddRegularNormRootMaximalIdealTails_not_hasInjectiveRepresentative
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
    (hCapitalW : hRegularProfileCapitalW z 0 ≠ 0)
    (hX : hRegularProfileX z 0 ≠ 1)
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
    exists_hHardOddOrdinarySourceBranchData_of_regular_norm_root
      R Rzero coefficient N hR hdecomposition hNodd numerator hnumerator
        z hroot hlinear hden hprofile hW hCapitalW hX hrepresentation
  exact
    hHardOddOrdinarySourceBranchMaximalIdealTails_not_hasInjectiveRepresentative
      R N hR data representative hanalytic hzero htail

/-- The regular finite root alternative from the norm count gives the
ordinary tail endpoint when both second coordinates are nonzero. -/
theorem hHardOddRegularFiniteRootMaximalIdealTails_not_hasInjectiveRepresentative
    (R Rzero : Form ℂ) (coefficient : ℂ) (N : ℕ)
    (hR : R.IsHomogeneous N)
    (hdecomposition :
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N)
    (hNodd : Odd N)
    (numerator : ℂ[X]) (hnumerator : numerator ≠ 0)
    (z : ℂ) (hroot : numerator.IsRoot z)
    (hzPlus : z ≠ hConicOneRootPlus)
    (hzMinus : z ≠ hConicOneRootMinus)
    (hprofile :
      (hPoleProfileDenominator (K := ℂ) (2 * N) (4 * N)).eval z ≠ 0)
    (hW : hRegularProfileW z 0 ≠ 0)
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
  have hNpos : 0 < N := hNodd.pos
  obtain ⟨hlinear, hden⟩ := h_pole_profile_factors_ne_zero
    (2 * N) (4 * N) (by omega) (by omega) z hprofile
  have hX : hRegularProfileX z 0 ≠ 1 := by
    rw [h_regular_profile_X_eq_eval z 0 (by simpa using hden)]
    simpa using h_conic_param_eval_x_ne_one
      h_conic_one_roots_equations.1 h_conic_one_roots_equations.2
        h_conic_one_roots_ne hzPlus hzMinus hden
  exact
    hHardOddRegularNormRootMaximalIdealTails_not_hasInjectiveRepresentative
      R Rzero coefficient N hR hdecomposition hNodd numerator hnumerator
        z hroot hlinear hden hprofile hW hCapitalW hX hrepresentation
          representative hanalytic hzero htail

end OnLeConjecture.DThree
