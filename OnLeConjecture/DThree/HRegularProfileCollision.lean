/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HAnalyticUnitRoot
public import OnLeConjecture.DThree.HCollisionPersistence
public import OnLeConjecture.DThree.HProjectiveDifferenceBoundary

/-!
# The regular affine profile chart in the H case

At a parameter where the conic parametrization is regular and both weighted
second coordinates are nonzero, analytic roots lift the conic to the source
chart.  The order of the third difference is the root multiplicity of the
profile numerator.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- Translation of the rational conic parameter to the selected point. -/
@[expose]
noncomputable def hRegularProfileParameter (z lambda : ℂ) : ℂ :=
  z + lambda

/-- The second first coordinate in the translated regular chart. -/
@[expose]
noncomputable def hRegularProfileX (z lambda : ℂ) : ℂ :=
  hConicParamXNumerator.eval (hRegularProfileParameter z lambda) /
    hConicParamDenominator.eval (hRegularProfileParameter z lambda)

/-- The weighted second coordinate of the first point. -/
@[expose]
noncomputable def hRegularProfileW (z lambda : ℂ) : ℂ :=
  (-hConicParamOneFactor * hConicParamWFactor).eval
      (hRegularProfileParameter z lambda) /
    hConicParamFunctionDenominator.eval
      (hRegularProfileParameter z lambda)

/-- The weighted second coordinate of the second point. -/
@[expose]
noncomputable def hRegularProfileCapitalW (z lambda : ℂ) : ℂ :=
  (-hConicParamOneFactor * hConicParamCapitalWFactor).eval
      (hRegularProfileParameter z lambda) /
    hConicParamFunctionDenominator.eval
      (hRegularProfileParameter z lambda)

theorem analyticAt_polynomial_eval_add (p : ℂ[X]) (z : ℂ) :
    AnalyticAt ℂ (fun lambda ↦ p.eval (z + lambda)) 0 := by
  have hargument : AnalyticAt ℂ (fun lambda : ℂ ↦ z + lambda) 0 :=
    analyticAt_const.add analyticAt_id
  simpa [aeval_def] using hargument.aeval_polynomial p

theorem h_regular_function_denominator_ne_zero
    {z : ℂ} (hlinear : z + 1 ≠ 0)
    (hden : hConicParamDenominator.eval z ≠ 0) :
    hConicParamFunctionDenominator.eval z ≠ 0 := by
  simp only [hConicParamFunctionDenominator, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_ofNat]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hlinear)
    (pow_ne_zero 2 hden)

theorem analyticAt_hRegularProfileX
    (z : ℂ) (hden : hConicParamDenominator.eval z ≠ 0) :
    AnalyticAt ℂ (hRegularProfileX z) 0 := by
  apply (analyticAt_polynomial_eval_add hConicParamXNumerator z).div
    (analyticAt_polynomial_eval_add hConicParamDenominator z)
  simpa [hRegularProfileParameter] using hden

theorem analyticAt_hRegularProfileW
    (z : ℂ) (hfunction : hConicParamFunctionDenominator.eval z ≠ 0) :
    AnalyticAt ℂ (hRegularProfileW z) 0 := by
  apply (analyticAt_polynomial_eval_add
      (-hConicParamOneFactor * hConicParamWFactor) z).div
    (analyticAt_polynomial_eval_add hConicParamFunctionDenominator z)
  simpa [hRegularProfileParameter] using hfunction

theorem analyticAt_hRegularProfileCapitalW
    (z : ℂ) (hfunction : hConicParamFunctionDenominator.eval z ≠ 0) :
    AnalyticAt ℂ (hRegularProfileCapitalW z) 0 := by
  apply (analyticAt_polynomial_eval_add
      (-hConicParamOneFactor * hConicParamCapitalWFactor) z).div
    (analyticAt_polynomial_eval_add hConicParamFunctionDenominator z)
  simpa [hRegularProfileParameter] using hfunction

theorem h_regular_profile_X_eq_eval
    (z lambda : ℂ)
    (hden : hConicParamDenominator.eval (z + lambda) ≠ 0) :
    hRegularProfileX z lambda =
      RatFunc.eval (RingHom.id ℂ) (z + lambda) hConicParamX := by
  rw [hConicParamX,
    h_ratFunc_eval_algebraMap_div (z + lambda)
      hConicParamXNumerator hConicParamDenominator hden]
  rfl

theorem h_regular_profile_W_eq_eval
    (z lambda : ℂ)
    (hfunction : hConicParamFunctionDenominator.eval (z + lambda) ≠ 0) :
    hRegularProfileW z lambda =
      RatFunc.eval (RingHom.id ℂ) (z + lambda) hConicParamW := by
  rw [hConicParamW,
    h_ratFunc_eval_algebraMap_div (z + lambda)
      (-hConicParamOneFactor * hConicParamWFactor)
        hConicParamFunctionDenominator hfunction]
  rfl

theorem h_regular_profile_capitalW_eq_eval
    (z lambda : ℂ)
    (hfunction : hConicParamFunctionDenominator.eval (z + lambda) ≠ 0) :
    hRegularProfileCapitalW z lambda =
      RatFunc.eval (RingHom.id ℂ) (z + lambda)
        hConicParamCapitalW := by
  rw [hConicParamCapitalW,
    h_ratFunc_eval_algebraMap_div (z + lambda)
      (-hConicParamOneFactor * hConicParamCapitalWFactor)
        hConicParamFunctionDenominator hfunction]
  rfl

/-- The translated regular coordinates lie in one fibre of `(hP,hQ)`. -/
theorem eventually_hRegularProfile_fibre
    (z : ℂ) (hlinear : z + 1 ≠ 0)
    (hden : hConicParamDenominator.eval z ≠ 0) :
    ∀ᶠ lambda in nhds 0,
      hP 1 (hRegularProfileW z lambda) =
          hP (hRegularProfileX z lambda)
            (hRegularProfileCapitalW z lambda) ∧
        hQ 1 (hRegularProfileW z lambda) =
          hQ (hRegularProfileX z lambda)
            (hRegularProfileCapitalW z lambda) := by
  have hparameter : Tendsto (fun lambda : ℂ ↦ z + lambda)
      (nhds 0) (nhds z) := by
    simpa using
      (tendsto_const_nhds.add tendsto_id :
        Tendsto (fun lambda : ℂ ↦ z + lambda) (nhds 0) (nhds (z + 0)))
  have hlinearEventually : ∀ᶠ lambda in nhds 0, z + lambda + 1 ≠ 0 :=
    (hparameter.add_const 1).eventually_ne hlinear
  have hdenEventually : ∀ᶠ lambda in nhds 0,
      hConicParamDenominator.eval (z + lambda) ≠ 0 := by
    have hcontinuous :=
      (analyticAt_polynomial_eval_add hConicParamDenominator z).continuousAt
    change Tendsto
        (fun lambda : ℂ ↦ hConicParamDenominator.eval (z + lambda))
        (nhds 0)
        (nhds (hConicParamDenominator.eval (z + 0))) at hcontinuous
    have hcontinuous' : Tendsto
        (fun lambda : ℂ ↦ hConicParamDenominator.eval (z + lambda))
        (nhds 0) (nhds (hConicParamDenominator.eval z)) := by
      simpa using hcontinuous
    exact hcontinuous'.eventually_ne hden
  filter_upwards [hlinearEventually, hdenEventually]
    with lambda hlinearAt hdenAt
  have hfunctionAt := h_regular_function_denominator_ne_zero
    hlinearAt hdenAt
  obtain ⟨hPfiber, hQfiber⟩ :=
    h_conic_param_eval_fibre (z + lambda) hlinearAt hdenAt
  rw [h_regular_profile_X_eq_eval z lambda hdenAt,
    h_regular_profile_W_eq_eval z lambda hfunctionAt,
    h_regular_profile_capitalW_eq_eval z lambda hfunctionAt]
  exact ⟨hPfiber, hQfiber⟩

/-- Evaluation of the conic difference at a regular parameter. -/
theorem h_ratFunc_eval_hConicDifference_regular
    (R : MvPolynomial (Fin 2) ℂ) (z : ℂ)
    (hlinear : z + 1 ≠ 0)
    (hden : hConicParamDenominator.eval z ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) z (hConicDifference R) =
      hFormEval 1 (RatFunc.eval (RingHom.id ℂ) z hConicParamW) R -
        hFormEval (RatFunc.eval (RingHom.id ℂ) z hConicParamX)
          (RatFunc.eval (RingHom.id ℂ) z hConicParamCapitalW) R := by
  obtain ⟨hxRegular, hwRegular, hWRegular⟩ :=
    h_conic_param_regular_at z hlinear hden
  have honeRegular : HRatFuncRegularAt z (1 : RatFunc ℂ) := by
    simpa using hRatFuncRegularAt_algebraMap (K := ℂ) z 1
  have hfirstRegular := hRatFuncRegularAt_hFormEval
    z 1 hConicParamW R honeRegular hwRegular
  have hsecondRegular := hRatFuncRegularAt_hFormEval
    z hConicParamX hConicParamCapitalW R hxRegular hWRegular
  rw [hConicDifference, hFirstConicPullback, hSecondConicPullback,
    h_ratFunc_eval_sub z _ _ hfirstRegular hsecondRegular,
    h_ratFunc_eval_hFormEval z 1 hConicParamW R
      honeRegular hwRegular,
    h_ratFunc_eval_hFormEval z hConicParamX hConicParamCapitalW R
      hxRegular hWRegular, RatFunc.eval_one]

/-- In the regular chart, the third difference is the quotient defining the
fixed profile. -/
theorem eventually_hRegularProfile_difference_eq_profile
    (R : MvPolynomial (Fin 2) ℂ) (p : ℂ[X])
    (aProfile bProfile : ℕ) (z : ℂ)
    (hlinear : z + 1 ≠ 0)
    (hden : hConicParamDenominator.eval z ≠ 0)
    (hprofile :
      (hPoleProfileDenominator (K := ℂ) aProfile bProfile).eval z ≠ 0)
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator aProfile bProfile)) :
    ∀ᶠ lambda in nhds 0,
      hFormEval 1 (hRegularProfileW z lambda) R -
          hFormEval (hRegularProfileX z lambda)
            (hRegularProfileCapitalW z lambda) R =
        p.eval (z + lambda) /
          (hPoleProfileDenominator aProfile bProfile).eval
            (z + lambda) := by
  have hparameter : Tendsto (fun lambda : ℂ ↦ z + lambda)
      (nhds 0) (nhds z) := by
    simpa using
      (tendsto_const_nhds.add tendsto_id :
        Tendsto (fun lambda : ℂ ↦ z + lambda) (nhds 0) (nhds (z + 0)))
  have hlinearEventually : ∀ᶠ lambda in nhds 0, z + lambda + 1 ≠ 0 :=
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
      (hPoleProfileDenominator aProfile bProfile).eval
        (z + lambda) ≠ 0 := by
    have ht : Tendsto
        (fun lambda : ℂ ↦
          (hPoleProfileDenominator aProfile bProfile).eval (z + lambda))
        (nhds 0)
        (nhds ((hPoleProfileDenominator aProfile bProfile).eval z)) := by
      have hc := (analyticAt_polynomial_eval_add
        (hPoleProfileDenominator aProfile bProfile) z).continuousAt
      change Tendsto
        (fun lambda : ℂ ↦
          (hPoleProfileDenominator aProfile bProfile).eval (z + lambda))
        (nhds 0)
        (nhds ((hPoleProfileDenominator aProfile bProfile).eval
          (z + 0))) at hc
      simpa using hc
    exact ht.eventually_ne hprofile
  filter_upwards [hlinearEventually, hdenEventually, hprofileEventually]
    with lambda hlinearAt hdenAt hprofileAt
  have hfunctionAt := h_regular_function_denominator_ne_zero
    hlinearAt hdenAt
  have heval := congrArg (RatFunc.eval (RingHom.id ℂ) (z + lambda))
    hrepresentation
  rw [h_ratFunc_eval_hConicDifference_regular R (z + lambda)
      hlinearAt hdenAt,
    h_ratFunc_eval_algebraMap_div (z + lambda) p
      (hPoleProfileDenominator aProfile bProfile) hprofileAt]
    at heval
  rw [h_regular_profile_X_eq_eval z lambda hdenAt,
    h_regular_profile_W_eq_eval z lambda hfunctionAt,
    h_regular_profile_capitalW_eq_eval z lambda hfunctionAt]
  exact heval

/-- Roots of the two weighted coordinates normalize a conic fibre pair to
the source chart whose first second coordinate is one. -/
theorem h_normalized_regular_fibre
    (a : ℕ) (y Y X w W : ℂ)
    (hy : y ^ (2 * a) = w) (hY : Y ^ (2 * a) = W)
    (hy0 : y ≠ 0)
    (hPfiber : hP 1 w = hP X W)
    (hQfiber : hQ 1 w = hQ X W) :
    hP (1 / y ^ a) 1 =
        hP (X / y ^ a) ((Y / y) ^ (2 * a)) ∧
      hQ (1 / y ^ a) 1 =
        hQ (X / y ^ a) ((Y / y) ^ (2 * a)) := by
  let mu : ℂ := y ^ a
  have hmu : mu ≠ 0 := pow_ne_zero a hy0
  have hmuSq : mu ^ 2 = w := by
    calc
      mu ^ 2 = y ^ (a * 2) := by simp [mu, pow_mul]
      _ = y ^ (2 * a) := by rw [Nat.mul_comm]
      _ = w := hy
  have hsecondWeighted :
      mu ^ 2 * (Y / y) ^ (2 * a) = W := by
    rw [hmuSq, ← hy, div_pow, hY]
    field_simp [pow_ne_zero (2 * a) hy0]
  have hfirstP := hP_weighted_smul mu (1 / mu) 1
  have hsecondP := hP_weighted_smul mu (X / mu) ((Y / y) ^ (2 * a))
  have hfirstQ := hQ_weighted_smul mu (1 / mu) 1
  have hsecondQ := hQ_weighted_smul mu (X / mu) ((Y / y) ^ (2 * a))
  have hfirstP' : hP 1 w =
      mu ^ 3 * hP (1 / mu) 1 := by
    rw [one_div, mul_inv_cancel₀ hmu, hmuSq, mul_one] at hfirstP
    simpa only [one_div] using hfirstP
  have hsecondP' : hP X W =
      mu ^ 3 * hP (X / mu) ((Y / y) ^ (2 * a)) := by
    simpa [mul_div_cancel₀ X hmu, hsecondWeighted] using hsecondP
  have hfirstQ' : hQ 1 w =
      mu ^ 4 * hQ (1 / mu) 1 := by
    rw [one_div, mul_inv_cancel₀ hmu, hmuSq, mul_one] at hfirstQ
    simpa only [one_div] using hfirstQ
  have hsecondQ' : hQ X W =
      mu ^ 4 * hQ (X / mu) ((Y / y) ^ (2 * a)) := by
    simpa [mul_div_cancel₀ X hmu, hsecondWeighted] using hsecondQ
  constructor
  · apply mul_left_cancel₀ (pow_ne_zero 3 hmu)
    calc
      mu ^ 3 * hP (1 / y ^ a) 1 = hP 1 w := by
        simpa [mu] using hfirstP'.symm
      _ = hP X W := hPfiber
      _ = mu ^ 3 * hP (X / y ^ a) ((Y / y) ^ (2 * a)) := by
        simpa [mu] using hsecondP'
  · apply mul_left_cancel₀ (pow_ne_zero 4 hmu)
    calc
      mu ^ 4 * hQ (1 / y ^ a) 1 = hQ 1 w := by
        simpa [mu] using hfirstQ'.symm
      _ = hQ X W := hQfiber
      _ = mu ^ 4 * hQ (X / y ^ a) ((Y / y) ^ (2 * a)) := by
        simpa [mu] using hsecondQ'

/-- Weighted homogeneity expresses the normalized third difference as the
original conic difference divided by a unit. -/
theorem h_normalized_regular_difference
    (a N : ℕ) (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (y Y X w W : ℂ)
    (hy : y ^ (2 * a) = w) (hY : Y ^ (2 * a) = W)
    (hy0 : y ≠ 0) :
    hFormEval (1 / y ^ a) 1 R -
        hFormEval (X / y ^ a) ((Y / y) ^ (2 * a)) R =
      (hFormEval 1 w R - hFormEval X W R) / (y ^ a) ^ N := by
  let mu : ℂ := y ^ a
  have hmu : mu ≠ 0 := pow_ne_zero a hy0
  have hmuSq : mu ^ 2 = w := by
    calc
      mu ^ 2 = y ^ (a * 2) := by simp [mu, pow_mul]
      _ = y ^ (2 * a) := by rw [Nat.mul_comm]
      _ = w := hy
  have hsecondWeighted :
      mu ^ 2 * (Y / y) ^ (2 * a) = W := by
    rw [hmuSq, ← hy, div_pow, hY]
    field_simp [pow_ne_zero (2 * a) hy0]
  have hfirst := hFormEval_weighted_smul R N hR
    mu (1 / mu) 1
  have hsecond := hFormEval_weighted_smul R N hR
    mu (X / mu) ((Y / y) ^ (2 * a))
  have hfirst' : hFormEval 1 w R =
      mu ^ N * hFormEval (1 / mu) 1 R := by
    rw [one_div, mul_inv_cancel₀ hmu, hmuSq, mul_one] at hfirst
    simpa only [one_div] using hfirst
  have hsecond' : hFormEval X W R =
      mu ^ N * hFormEval (X / mu) ((Y / y) ^ (2 * a)) R := by
    simpa [mul_div_cancel₀ X hmu, hsecondWeighted] using hsecond
  apply (eq_div_iff (pow_ne_zero N hmu)).2
  change
    (hFormEval (1 / mu) 1 R -
        hFormEval (X / mu) ((Y / y) ^ (2 * a)) R) * mu ^ N = _
  calc
    (hFormEval (1 / mu) 1 R -
          hFormEval (X / mu) ((Y / y) ^ (2 * a)) R) * mu ^ N =
        mu ^ N * hFormEval (1 / mu) 1 R -
          mu ^ N * hFormEval (X / mu) ((Y / y) ^ (2 * a)) R := by ring
    _ = hFormEval 1 w R - hFormEval X W R := by
      rw [← hfirst', ← hsecond']

/-- Analytic source data and the finite order factorization in a regular
profile chart. -/
structure HRegularSourceBranchData
    (a N : ℕ) (R : MvPolynomial (Fin 2) ℂ) where
  firstX : ℂ → ℂ
  secondPoint : ℂ → Fin 2 → ℂ
  secondX : ℂ
  secondT : ℂ
  order : ℕ
  unit : ℂ → ℂ
  firstX_analyticAt : AnalyticAt ℂ firstX 0
  secondPoint_analyticAt : AnalyticAt ℂ secondPoint 0
  secondPoint_zero : secondPoint 0 = ![secondX, secondT]
  secondT_ne_zero : secondT ≠ 0
  firstX_zero_ne_secondX : firstX 0 ≠ secondX
  plane_zero : ∀ᶠ lambda in nhds 0,
    hCollisionPlaneDifference a firstX
      (lambda, secondPoint lambda) = 0
  order_pos : 0 < order
  unit_analyticAt : AnalyticAt ℂ unit 0
  unit_zero_ne : unit 0 ≠ 0
  third_factor : ∀ᶠ lambda in nhds 0,
    hFormEval (firstX lambda) 1 R -
        hFormEval (secondPoint lambda 0)
          (secondPoint lambda 1 ^ (2 * a)) R =
      lambda ^ order * unit lambda

/-- A regular root of the fixed profile numerator gives an isolated source
collision with its exact positive multiplicity. -/
theorem exists_hRegularSourceBranchData_of_profile_root
    (a N aProfile bProfile : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X]) (hp : p ≠ 0) (z : ℂ) (hz : p.IsRoot z)
    (hlinear : z + 1 ≠ 0)
    (hden : hConicParamDenominator.eval z ≠ 0)
    (hprofile :
      (hPoleProfileDenominator (K := ℂ) aProfile bProfile).eval z ≠ 0)
    (hW : hRegularProfileW z 0 ≠ 0)
    (hCapitalW : hRegularProfileCapitalW z 0 ≠ 0)
    (hX : hRegularProfileX z 0 ≠ 1)
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator aProfile bProfile)) :
    Nonempty (HRegularSourceBranchData a N R) := by
  have hrootDegree : 0 < 2 * a := by omega
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq
    (hRegularProfileW z 0) hrootDegree
  obtain ⟨S, hS⟩ := IsAlgClosed.exists_pow_nat_eq
    (hRegularProfileCapitalW z 0) hrootDegree
  have hs0 : s ≠ 0 := by
    intro hsZero
    apply hW
    rw [← hs, hsZero, zero_pow (by omega)]
  have hS0 : S ≠ 0 := by
    intro hSZero
    apply hCapitalW
    rw [← hS, hSZero, zero_pow (by omega)]
  have hfunction := h_regular_function_denominator_ne_zero hlinear hden
  obtain ⟨y, hyAnalytic, hyZero, hyPower⟩ :=
    exists_analyticAt_root_with_value
      (hRegularProfileW z) (analyticAt_hRegularProfileW z hfunction)
        hW (2 * a) (by omega) s hs
  obtain ⟨Y, hYAnalytic, hYZero, hYPower⟩ :=
    exists_analyticAt_root_with_value
      (hRegularProfileCapitalW z)
        (analyticAt_hRegularProfileCapitalW z hfunction)
          hCapitalW (2 * a) (by omega) S hS
  let firstX : ℂ → ℂ := fun lambda ↦ 1 / y lambda ^ a
  let secondPoint : ℂ → Fin 2 → ℂ := fun lambda ↦
    ![hRegularProfileX z lambda / y lambda ^ a,
      Y lambda / y lambda]
  let secondX : ℂ := hRegularProfileX z 0 / s ^ a
  let secondT : ℂ := S / s
  have hfirstXAnalytic : AnalyticAt ℂ firstX 0 := by
    apply analyticAt_const.div (hyAnalytic.pow a)
    simpa only [Pi.pow_apply, hyZero] using pow_ne_zero a hs0
  have hsecondPointAnalytic : AnalyticAt ℂ secondPoint 0 := by
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · exact (analyticAt_hRegularProfileX z hden).div
        (hyAnalytic.pow a) (by rw [hyZero]; exact pow_ne_zero a hs0)
    · exact hYAnalytic.div hyAnalytic (by simpa [hyZero] using hs0)
  have hsecondPointZero : secondPoint 0 = ![secondX, secondT] := by
    funext i
    fin_cases i
    · simp [secondPoint, secondX, hyZero]
    · simp [secondPoint, secondT, hyZero, hYZero]
  have hsecondT : secondT ≠ 0 := by
    exact div_ne_zero hS0 hs0
  have hdistinct : firstX 0 ≠ secondX := by
    intro hequal
    apply hX
    have hequal' : 1 / s ^ a =
        hRegularProfileX z 0 / s ^ a := by
      simpa [firstX, secondX, hyZero] using hequal
    exact ((div_left_inj' (pow_ne_zero a hs0)).mp hequal').symm
  have hyTendsto : Tendsto y (nhds 0) (nhds s) := by
    have ht := hyAnalytic.continuousAt
    change Tendsto y (nhds 0) (nhds (y 0)) at ht
    rw [hyZero] at ht
    exact ht
  have hyEventually : ∀ᶠ lambda in nhds 0, y lambda ≠ 0 :=
    hyTendsto.eventually_ne hs0
  have hplaneZero : ∀ᶠ lambda in nhds 0,
      hCollisionPlaneDifference a firstX
        (lambda, secondPoint lambda) = 0 := by
    filter_upwards [eventually_hRegularProfile_fibre z hlinear hden,
      hyEventually] with lambda hfibre hyAt
    obtain ⟨hPfiber, hQfiber⟩ :=
      h_normalized_regular_fibre a (y lambda) (Y lambda)
        (hRegularProfileX z lambda) (hRegularProfileW z lambda)
          (hRegularProfileCapitalW z lambda)
            (hyPower lambda) (hYPower lambda) hyAt hfibre.1 hfibre.2
    funext i
    fin_cases i
    · simpa [hCollisionPlaneDifference, firstX, secondPoint] using
        sub_eq_zero.mpr hPfiber
    · simpa [hCollisionPlaneDifference, firstX, secondPoint] using
        sub_eq_zero.mpr hQfiber
  let order := p.rootMultiplicity z
  let quotient := p /ₘ (Polynomial.X - Polynomial.C z) ^ order
  have horder : 0 < order := by
    exact (Polynomial.rootMultiplicity_pos hp).2 hz
  have hpolynomialFactor :
      p = (Polynomial.X - Polynomial.C z) ^ order * quotient := by
    exact (Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p z).symm
  have hquotient : quotient.eval z ≠ 0 := by
    exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero z hp
  let unit : ℂ → ℂ := fun lambda ↦
    quotient.eval (z + lambda) /
        (hPoleProfileDenominator aProfile bProfile).eval (z + lambda) /
      (y lambda ^ a) ^ N
  have hunitAnalytic : AnalyticAt ℂ unit 0 := by
    have hquotientAnalytic := analyticAt_polynomial_eval_add quotient z
    have hprofileAnalytic := analyticAt_polynomial_eval_add
      (hPoleProfileDenominator aProfile bProfile) z
    exact (hquotientAnalytic.div hprofileAnalytic (by simpa using hprofile)).div
      ((hyAnalytic.pow a).pow N)
      (by rw [hyZero]; exact pow_ne_zero N (pow_ne_zero a hs0))
  have hunitZero : unit 0 ≠ 0 := by
    change quotient.eval (z + 0) /
        (hPoleProfileDenominator aProfile bProfile).eval (z + 0) /
      (y 0 ^ a) ^ N ≠ 0
    rw [add_zero, hyZero]
    exact div_ne_zero (div_ne_zero hquotient hprofile)
      (pow_ne_zero N (pow_ne_zero a hs0))
  have hthirdFactor : ∀ᶠ lambda in nhds 0,
      hFormEval (firstX lambda) 1 R -
          hFormEval (secondPoint lambda 0)
            (secondPoint lambda 1 ^ (2 * a)) R =
        lambda ^ order * unit lambda := by
    filter_upwards
      [eventually_hRegularProfile_difference_eq_profile
        R p aProfile bProfile z hlinear hden hprofile hrepresentation,
       hyEventually] with lambda hraw hyAt
    have hpEval := congrArg (fun polynomial : ℂ[X] ↦
      polynomial.eval (z + lambda)) hpolynomialFactor
    rw [Polynomial.eval_mul, Polynomial.eval_pow] at hpEval
    have hlinearEval :
        (Polynomial.X - Polynomial.C z).eval (z + lambda) = lambda := by
      simp
    rw [hlinearEval] at hpEval
    have hnormalized := h_normalized_regular_difference
      a N R hR (y lambda) (Y lambda)
        (hRegularProfileX z lambda) (hRegularProfileW z lambda)
          (hRegularProfileCapitalW z lambda)
            (hyPower lambda) (hYPower lambda) hyAt
    change hFormEval (1 / y lambda ^ a) 1 R -
        hFormEval (hRegularProfileX z lambda / y lambda ^ a)
          ((Y lambda / y lambda) ^ (2 * a)) R = _
    rw [hnormalized, hraw, hpEval]
    simp only [unit, order]
    ring
  let data : HRegularSourceBranchData a N R :=
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
      firstX_zero_ne_secondX := hdistinct
      plane_zero := hplaneZero
      order_pos := horder
      unit_analyticAt := hunitAnalytic
      unit_zero_ne := hunitZero
      third_factor := hthirdFactor }
  exact ⟨data⟩

end OnLeConjecture.DThree
