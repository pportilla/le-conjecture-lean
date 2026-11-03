/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HNormalizedCollisionNoninjectivity
public import OnLeConjecture.DThree.HProjectiveDifferenceFiniteBoundary

/-!
# Analytic collisions at the finite boundary of the H parametrization

At a root of `m² + 2`, rescaling by that factor gives analytic weighted
coordinates.  A root of the profile numerator has its polynomial root
multiplicity on this branch.
-/

public section

open Filter Set
open scoped Topology Polynomial

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- The remaining denominator after rescaling at a root of `m² + 2`. -/
@[expose]
noncomputable def hFiniteBoundaryLinear : ℂ[X] :=
  3 * (Polynomial.X + 1)

/-- The first first coordinate in the rescaled finite boundary chart. -/
@[expose]
noncomputable def hFiniteBoundaryFirstX (z lambda : ℂ) : ℂ :=
  hConicParamDenominator.eval (z + lambda)

/-- The first weighted second coordinate in the rescaled finite boundary
chart. -/
@[expose]
noncomputable def hFiniteBoundaryW (z lambda : ℂ) : ℂ :=
  (-hConicParamOneFactor * hConicParamWFactor).eval (z + lambda) /
    hFiniteBoundaryLinear.eval (z + lambda)

/-- The second first coordinate in the rescaled finite boundary chart. -/
@[expose]
noncomputable def hFiniteBoundarySecondX (z lambda : ℂ) : ℂ :=
  hConicParamXNumerator.eval (z + lambda)

/-- The second weighted second coordinate in the rescaled finite boundary
chart. -/
@[expose]
noncomputable def hFiniteBoundaryCapitalW (z lambda : ℂ) : ℂ :=
  (-hConicParamOneFactor * hConicParamCapitalWFactor).eval (z + lambda) /
    hFiniteBoundaryLinear.eval (z + lambda)

theorem h_finite_boundary_linear_ne_zero
    {z : ℂ} (hz : z ^ 2 + 2 = 0) :
    hFiniteBoundaryLinear.eval z ≠ 0 := by
  simp only [hFiniteBoundaryLinear, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one]
  exact mul_ne_zero (by norm_num)
    (h_conic_param_infinity_root_add_one_ne_zero hz)

theorem analyticAt_hFiniteBoundaryFirstX (z : ℂ) :
    AnalyticAt ℂ (hFiniteBoundaryFirstX z) 0 := by
  exact analyticAt_polynomial_eval_add hConicParamDenominator z

theorem analyticAt_hFiniteBoundaryW
    (z : ℂ) (hlinear : hFiniteBoundaryLinear.eval z ≠ 0) :
    AnalyticAt ℂ (hFiniteBoundaryW z) 0 := by
  exact (analyticAt_polynomial_eval_add
      (-hConicParamOneFactor * hConicParamWFactor) z).div
    (analyticAt_polynomial_eval_add hFiniteBoundaryLinear z)
      (by simpa using hlinear)

theorem analyticAt_hFiniteBoundarySecondX (z : ℂ) :
    AnalyticAt ℂ (hFiniteBoundarySecondX z) 0 := by
  exact analyticAt_polynomial_eval_add hConicParamXNumerator z

theorem analyticAt_hFiniteBoundaryCapitalW
    (z : ℂ) (hlinear : hFiniteBoundaryLinear.eval z ≠ 0) :
    AnalyticAt ℂ (hFiniteBoundaryCapitalW z) 0 := by
  exact (analyticAt_polynomial_eval_add
      (-hConicParamOneFactor * hConicParamCapitalWFactor) z).div
    (analyticAt_polynomial_eval_add hFiniteBoundaryLinear z)
      (by simpa using hlinear)

/-- The rescaled coordinates lie in one fibre wherever the remaining linear
denominator does not vanish. -/
theorem h_finite_boundary_fibre_at
    (m : ℂ) (hlinear : hFiniteBoundaryLinear.eval m ≠ 0) :
    hP (hConicParamDenominator.eval m)
          ((-hConicParamOneFactor * hConicParamWFactor).eval m /
            hFiniteBoundaryLinear.eval m) =
        hP (hConicParamXNumerator.eval m)
          ((-hConicParamOneFactor * hConicParamCapitalWFactor).eval m /
            hFiniteBoundaryLinear.eval m) ∧
      hQ (hConicParamDenominator.eval m)
          ((-hConicParamOneFactor * hConicParamWFactor).eval m /
            hFiniteBoundaryLinear.eval m) =
        hQ (hConicParamXNumerator.eval m)
          ((-hConicParamOneFactor * hConicParamCapitalWFactor).eval m /
            hFiniteBoundaryLinear.eval m) := by
  let firstNumerator : ℂ[X] :=
    -hConicParamOneFactor * hConicParamWFactor
  let secondNumerator : ℂ[X] :=
    -hConicParamOneFactor * hConicParamCapitalWFactor
  have hfirstRegular : HRatFuncRegularAt m
      (algebraMap ℂ[X] (RatFunc ℂ) firstNumerator /
        algebraMap ℂ[X] (RatFunc ℂ) hFiniteBoundaryLinear) :=
    hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd firstNumerator hFiniteBoundaryLinear) hlinear
  have hsecondRegular : HRatFuncRegularAt m
      (algebraMap ℂ[X] (RatFunc ℂ) secondNumerator /
        algebraMap ℂ[X] (RatFunc ℂ) hFiniteBoundaryLinear) :=
    hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd secondNumerator hFiniteBoundaryLinear) hlinear
  have hdenRegular := hRatFuncRegularAt_algebraMap
    (K := ℂ) m hConicParamDenominator
  have hxRegular := hRatFuncRegularAt_algebraMap
    (K := ℂ) m hConicParamXNumerator
  have hfibre := h_scaled_infinity_conic_fibre (K := ℂ)
  have hPeval := congrArg (RatFunc.eval (RingHom.id ℂ) m) hfibre.1
  have hQeval := congrArg (RatFunc.eval (RingHom.id ℂ) m) hfibre.2
  rw [show (3 * (Polynomial.X + 1) : ℂ[X]) =
      hFiniteBoundaryLinear by rfl] at hPeval hQeval
  rw [← hFormEval_hPForm (K := ℂ),
    ← hFormEval_hPForm (K := ℂ),
    h_ratFunc_eval_hFormEval m _ _ hPForm hdenRegular hfirstRegular,
    h_ratFunc_eval_hFormEval m _ _ hPForm hxRegular hsecondRegular,
    h_ratFunc_eval_algebraMap_div m firstNumerator
      hFiniteBoundaryLinear hlinear,
    h_ratFunc_eval_algebraMap_div m secondNumerator
      hFiniteBoundaryLinear hlinear,
    h_ratFunc_eval_algebraMap_id] at hPeval
  rw [← hFormEval_hQForm (K := ℂ),
    ← hFormEval_hQForm (K := ℂ),
    h_ratFunc_eval_hFormEval m _ _ hQForm hdenRegular hfirstRegular,
    h_ratFunc_eval_hFormEval m _ _ hQForm hxRegular hsecondRegular,
    h_ratFunc_eval_algebraMap_div m firstNumerator
      hFiniteBoundaryLinear hlinear,
    h_ratFunc_eval_algebraMap_div m secondNumerator
      hFiniteBoundaryLinear hlinear,
    h_ratFunc_eval_algebraMap_id] at hQeval
  rw [h_ratFunc_eval_algebraMap_id m hConicParamXNumerator]
    at hPeval hQeval
  simpa only [firstNumerator, secondNumerator,
    hFormEval_hPForm, hFormEval_hQForm] using And.intro hPeval hQeval

/-- The rescaled third difference is the profile numerator divided by the
remaining linear denominator. -/
theorem h_finite_boundary_difference_eq_profile_at
    (N : ℕ) (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X])
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (N / 2) N))
    (m : ℂ) (hlinear : hFiniteBoundaryLinear.eval m ≠ 0) :
    hFormEval (hConicParamDenominator.eval m)
          ((-hConicParamOneFactor * hConicParamWFactor).eval m /
            hFiniteBoundaryLinear.eval m) R -
        hFormEval (hConicParamXNumerator.eval m)
          ((-hConicParamOneFactor * hConicParamCapitalWFactor).eval m /
            hFiniteBoundaryLinear.eval m) R =
      p.eval m / hFiniteBoundaryLinear.eval m ^ (N / 2) := by
  have hscaledRepresentationOriginal :
      algebraMap ℂ[X] (RatFunc ℂ) hConicParamDenominator ^ N *
          hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            ((3 * (Polynomial.X + 1)) ^ (N / 2)) := by
    rw [hrepresentation, hPoleProfileDenominator]
    simp only [map_mul, map_pow]
    field_simp [RatFunc.algebraMap_ne_zero
      h_conic_param_denominator_ne_zero,
      RatFunc.algebraMap_ne_zero
        (h_conic_profile_linear_ne_zero (K := ℂ))]
  have hscaledRepresentation :
      algebraMap ℂ[X] (RatFunc ℂ) hConicParamDenominator ^ N *
          hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hFiniteBoundaryLinear ^ (N / 2)) := by
    simpa only [hFiniteBoundaryLinear] using hscaledRepresentationOriginal
  have hrational :
      hFormEval
          (algebraMap ℂ[X] (RatFunc ℂ) hConicParamDenominator)
          (algebraMap ℂ[X] (RatFunc ℂ)
              (-hConicParamOneFactor * hConicParamWFactor) /
            algebraMap ℂ[X] (RatFunc ℂ) hFiniteBoundaryLinear) R -
        hFormEval
          (algebraMap ℂ[X] (RatFunc ℂ) hConicParamXNumerator)
          (algebraMap ℂ[X] (RatFunc ℂ)
              (-hConicParamOneFactor * hConicParamCapitalWFactor) /
            algebraMap ℂ[X] (RatFunc ℂ) hFiniteBoundaryLinear) R =
      algebraMap ℂ[X] (RatFunc ℂ) p /
        algebraMap ℂ[X] (RatFunc ℂ)
          (hFiniteBoundaryLinear ^ (N / 2)) := by
    rw [← hscaledRepresentation]
    simpa only [hFiniteBoundaryLinear] using
      (h_scaled_infinity_conic_difference R N hR).symm
  let firstNumerator : ℂ[X] :=
    -hConicParamOneFactor * hConicParamWFactor
  let secondNumerator : ℂ[X] :=
    -hConicParamOneFactor * hConicParamCapitalWFactor
  have hfirstRegular : HRatFuncRegularAt m
      (algebraMap ℂ[X] (RatFunc ℂ) firstNumerator /
        algebraMap ℂ[X] (RatFunc ℂ) hFiniteBoundaryLinear) :=
    hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd firstNumerator hFiniteBoundaryLinear) hlinear
  have hsecondRegular : HRatFuncRegularAt m
      (algebraMap ℂ[X] (RatFunc ℂ) secondNumerator /
        algebraMap ℂ[X] (RatFunc ℂ) hFiniteBoundaryLinear) :=
    hRatFuncRegularAt_of_denom_dvd
      (RatFunc.denom_div_dvd secondNumerator hFiniteBoundaryLinear) hlinear
  have hdenRegular := hRatFuncRegularAt_algebraMap
    (K := ℂ) m hConicParamDenominator
  have hxRegular := hRatFuncRegularAt_algebraMap
    (K := ℂ) m hConicParamXNumerator
  have hfirstFormRegular := hRatFuncRegularAt_hFormEval m
    (algebraMap ℂ[X] (RatFunc ℂ) hConicParamDenominator)
    (algebraMap ℂ[X] (RatFunc ℂ) firstNumerator /
      algebraMap ℂ[X] (RatFunc ℂ) hFiniteBoundaryLinear) R
    hdenRegular hfirstRegular
  have hsecondFormRegular := hRatFuncRegularAt_hFormEval m
    (algebraMap ℂ[X] (RatFunc ℂ) hConicParamXNumerator)
    (algebraMap ℂ[X] (RatFunc ℂ) secondNumerator /
      algebraMap ℂ[X] (RatFunc ℂ) hFiniteBoundaryLinear) R
    hxRegular hsecondRegular
  have heval := congrArg (RatFunc.eval (RingHom.id ℂ) m) hrational
  rw [h_ratFunc_eval_sub m _ _ hfirstFormRegular hsecondFormRegular,
    h_ratFunc_eval_hFormEval m _ _ R hdenRegular hfirstRegular,
    h_ratFunc_eval_hFormEval m _ _ R hxRegular hsecondRegular,
    h_ratFunc_eval_algebraMap_div m firstNumerator
      hFiniteBoundaryLinear hlinear,
    h_ratFunc_eval_algebraMap_div m secondNumerator
      hFiniteBoundaryLinear hlinear,
    h_ratFunc_eval_algebraMap_div m p
      (hFiniteBoundaryLinear ^ (N / 2))
      (by simpa [Polynomial.eval_pow] using
        pow_ne_zero (N / 2) hlinear),
    h_ratFunc_eval_algebraMap_id] at heval
  rw [h_ratFunc_eval_algebraMap_id m hConicParamXNumerator] at heval
  simpa only [firstNumerator, secondNumerator,
    Polynomial.eval_pow] using heval

/-- The translated rescaled coordinates lie in one fibre near a root of
`m² + 2`. -/
theorem eventually_hFiniteBoundary_fibre
    (z : ℂ) (hz : z ^ 2 + 2 = 0) :
    ∀ᶠ lambda in nhds 0,
      hP (hFiniteBoundaryFirstX z lambda)
          (hFiniteBoundaryW z lambda) =
        hP (hFiniteBoundarySecondX z lambda)
          (hFiniteBoundaryCapitalW z lambda) ∧
      hQ (hFiniteBoundaryFirstX z lambda)
          (hFiniteBoundaryW z lambda) =
        hQ (hFiniteBoundarySecondX z lambda)
          (hFiniteBoundaryCapitalW z lambda) := by
  have hlinear := h_finite_boundary_linear_ne_zero hz
  have htendsto : Tendsto
      (fun lambda : ℂ ↦ hFiniteBoundaryLinear.eval (z + lambda))
      (nhds 0) (nhds (hFiniteBoundaryLinear.eval z)) := by
    have hcontinuous :=
      (analyticAt_polynomial_eval_add hFiniteBoundaryLinear z).continuousAt
    change Tendsto
      (fun lambda : ℂ ↦ hFiniteBoundaryLinear.eval (z + lambda))
      (nhds 0) (nhds (hFiniteBoundaryLinear.eval (z + 0))) at hcontinuous
    simpa using hcontinuous
  filter_upwards [htendsto.eventually_ne hlinear] with lambda hlinearAt
  simpa only [hFiniteBoundaryFirstX, hFiniteBoundaryW,
    hFiniteBoundarySecondX, hFiniteBoundaryCapitalW] using
      h_finite_boundary_fibre_at (z + lambda) hlinearAt

/-- Near a finite boundary root, the rescaled third difference equals the
translated profile quotient. -/
theorem eventually_hFiniteBoundary_difference_eq_profile
    (N : ℕ) (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X])
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (N / 2) N))
    (z : ℂ) (hz : z ^ 2 + 2 = 0) :
    ∀ᶠ lambda in nhds 0,
      hFormEval (hFiniteBoundaryFirstX z lambda)
          (hFiniteBoundaryW z lambda) R -
        hFormEval (hFiniteBoundarySecondX z lambda)
          (hFiniteBoundaryCapitalW z lambda) R =
      p.eval (z + lambda) /
        hFiniteBoundaryLinear.eval (z + lambda) ^ (N / 2) := by
  have hlinear := h_finite_boundary_linear_ne_zero hz
  have htendsto : Tendsto
      (fun lambda : ℂ ↦ hFiniteBoundaryLinear.eval (z + lambda))
      (nhds 0) (nhds (hFiniteBoundaryLinear.eval z)) := by
    have hcontinuous :=
      (analyticAt_polynomial_eval_add hFiniteBoundaryLinear z).continuousAt
    change Tendsto
      (fun lambda : ℂ ↦ hFiniteBoundaryLinear.eval (z + lambda))
      (nhds 0) (nhds (hFiniteBoundaryLinear.eval (z + 0))) at hcontinuous
    simpa using hcontinuous
  filter_upwards [htendsto.eventually_ne hlinear] with lambda hlinearAt
  simpa only [hFiniteBoundaryFirstX, hFiniteBoundaryW,
    hFiniteBoundarySecondX, hFiniteBoundaryCapitalW] using
      h_finite_boundary_difference_eq_profile_at
        N R hR p hrepresentation (z + lambda) hlinearAt

/-- A profile root at a root of `m² + 2` gives normalized source branch data
with its exact root multiplicity. -/
theorem exists_hFiniteBoundarySourceBranchData_of_profile_root
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X]) (hp : p ≠ 0) (z : ℂ)
    (hz : z ^ 2 + 2 = 0) (hroot : p.IsRoot z)
    (hrepresentation :
      hConicDifference R =
        algebraMap ℂ[X] (RatFunc ℂ) p /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (N / 2) N)) :
    Nonempty (HNormalizedSourceBranchData a N R) := by
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
  let order := p.rootMultiplicity z
  let quotient := p /ₘ (Polynomial.X - Polynomial.C z) ^ order
  have horder : 0 < order :=
    (Polynomial.rootMultiplicity_pos hp).2 hroot
  have hpolynomialFactor :
      p = (Polynomial.X - Polynomial.C z) ^ order * quotient :=
    (Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p z).symm
  have hquotient : quotient.eval z ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero z hp
  let rawUnit : ℂ → ℂ := fun lambda ↦
    quotient.eval (z + lambda) /
      hFiniteBoundaryLinear.eval (z + lambda) ^ (N / 2)
  have hrawUnit : AnalyticAt ℂ rawUnit 0 := by
    exact (analyticAt_polynomial_eval_add quotient z).div
      ((analyticAt_polynomial_eval_add hFiniteBoundaryLinear z).pow (N / 2))
      (by simpa only [Pi.pow_apply, add_zero] using
        pow_ne_zero (N / 2) hlinear)
  have hrawUnit0 : rawUnit 0 ≠ 0 := by
    change quotient.eval (z + 0) /
      hFiniteBoundaryLinear.eval (z + 0) ^ (N / 2) ≠ 0
    rw [add_zero]
    exact div_ne_zero hquotient (pow_ne_zero (N / 2) hlinear)
  have hrawFactor : ∀ᶠ lambda in nhds 0,
      hFormEval (hFiniteBoundaryFirstX z lambda)
          (hFiniteBoundaryW z lambda) R -
        hFormEval (hFiniteBoundarySecondX z lambda)
          (hFiniteBoundaryCapitalW z lambda) R =
      lambda ^ order * rawUnit lambda := by
    filter_upwards
      [eventually_hFiniteBoundary_difference_eq_profile
        N R hR p hrepresentation z hz] with lambda hdifference
    have hpEval := congrArg
      (fun polynomial : ℂ[X] ↦ polynomial.eval (z + lambda))
      hpolynomialFactor
    rw [Polynomial.eval_mul, Polynomial.eval_pow] at hpEval
    have hlinearEval :
        (Polynomial.X - Polynomial.C z).eval (z + lambda) = lambda := by
      simp
    rw [hlinearEval] at hpEval
    rw [hdifference, hpEval]
    simp only [rawUnit, order]
    ring
  exact exists_hNormalizedSourceBranchData
    a N ha R hR
      (hFiniteBoundaryFirstX z) (hFiniteBoundaryW z)
      (hFiniteBoundarySecondX z) (hFiniteBoundaryCapitalW z)
      (analyticAt_hFiniteBoundaryFirstX z)
      (analyticAt_hFiniteBoundaryW z hlinear)
      (analyticAt_hFiniteBoundarySecondX z)
      (analyticAt_hFiniteBoundaryCapitalW z hlinear)
      hw0 hcapitalW0
      (Or.inl (by rw [hfirstX0]; exact hsecondX0.symm))
      (eventually_hFiniteBoundary_fibre z hz)
      order rawUnit horder hrawUnit hrawUnit0 hrawFactor

/-- Weighted order tails exclude an injective representative when the profile
numerator vanishes at a root of `m² + 2`. -/
theorem hFiniteBoundaryWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (p : ℂ[X]) (hp : p ≠ 0) (z : ℂ)
    (hz : z ^ 2 + 2 = 0) (hroot : p.IsRoot z)
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
    exists_hFiniteBoundarySourceBranchData_of_profile_root
      a N ha R hR p hp z hz hroot hrepresentation
  exact hNormalizedWeightedOrderTails_not_hasInjectiveRepresentative
    a N ha R hR data representative hanalytic hzero htail

end OnLeConjecture.DThree
