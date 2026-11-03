/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HNormalizedCollisionNoninjectivity
public import OnLeConjecture.DThree.HProjectiveDifferenceBoundary

/-!
# Analytic factors from finite rational function order

A rational function of exact positive finite order at zero has an explicit
analytic unit factor obtained from its reduced numerator and denominator.
-/

public section

open Filter
open scoped Topology Polynomial WithZero

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- Exact nonnegative finite order of a rational function at zero gives an
analytic unit factor for its evaluation. -/
theorem exists_analyticAt_ratFunc_eval_factor_of_finite_order
    (f : RatFunc ℂ) (k : ℕ)
    (horder : hFiniteOrderAt 0 f = WithZero.exp (k : ℤ)) :
    ∃ unit : ℂ → ℂ,
      AnalyticAt ℂ unit 0 ∧ unit 0 ≠ 0 ∧
        ∀ᶠ lambda in nhds 0,
          RatFunc.eval (RingHom.id ℂ) lambda f =
            lambda ^ k * unit lambda := by
  have hf : f ≠ 0 := h_ratFunc_ne_zero_of_finite_order horder
  obtain ⟨hnumMultiplicity, hdenMultiplicity⟩ :=
    h_divisor_coefficients_of_finite_order hf 0 k horder
  rw [h_finite_zero_divisor_apply] at hnumMultiplicity
  rw [h_finite_pole_divisor_apply] at hdenMultiplicity
  have hdenEval : f.denom.eval 0 ≠ 0 := by
    intro hzero
    have hroot : f.denom.IsRoot 0 := hzero
    have hpositive :=
      (Polynomial.rootMultiplicity_pos f.denom_ne_zero).2 hroot
    omega
  let quotient : ℂ[X] :=
    f.num /ₘ (Polynomial.X - Polynomial.C 0) ^ k
  have hfactor :
      (Polynomial.X - Polynomial.C 0) ^ k * quotient = f.num := by
    have hcanonical :=
      Polynomial.pow_mul_divByMonic_rootMultiplicity_eq f.num 0
    simpa only [quotient, hnumMultiplicity] using hcanonical
  have hquotient : quotient.eval 0 ≠ 0 := by
    have hcanonical :=
      Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero
        0 (RatFunc.num_ne_zero hf)
    simpa only [quotient, hnumMultiplicity] using hcanonical
  let unit : ℂ → ℂ := fun lambda ↦
    quotient.eval lambda / f.denom.eval lambda
  have hunitAnalytic : AnalyticAt ℂ unit 0 := by
    have hquotientAnalytic : AnalyticAt ℂ
        (fun lambda : ℂ ↦ quotient.eval lambda) 0 := by
      simpa using analyticAt_polynomial_eval_add quotient 0
    have hdenAnalytic : AnalyticAt ℂ
        (fun lambda : ℂ ↦ f.denom.eval lambda) 0 := by
      simpa using analyticAt_polynomial_eval_add f.denom 0
    exact hquotientAnalytic.div hdenAnalytic hdenEval
  have hunitZero : unit 0 ≠ 0 :=
    div_ne_zero hquotient hdenEval
  have hdenTendsto : Tendsto
      (fun lambda : ℂ ↦ f.denom.eval lambda)
      (nhds 0) (nhds (f.denom.eval 0)) := by
    have hcontinuous : ContinuousAt
        (fun lambda : ℂ ↦ f.denom.eval lambda) 0 := by
      simpa using (analyticAt_polynomial_eval_add f.denom 0).continuousAt
    exact hcontinuous
  refine ⟨unit, hunitAnalytic, hunitZero, ?_⟩
  filter_upwards [hdenTendsto.eventually_ne hdenEval]
    with lambda hdenAt
  have heval :
      RatFunc.eval (RingHom.id ℂ) lambda f =
        f.num.eval lambda / f.denom.eval lambda := by
    calc
      RatFunc.eval (RingHom.id ℂ) lambda f =
          RatFunc.eval (RingHom.id ℂ) lambda
            (algebraMap ℂ[X] (RatFunc ℂ) f.num /
              algebraMap ℂ[X] (RatFunc ℂ) f.denom) :=
        congrArg (RatFunc.eval (RingHom.id ℂ) lambda)
          (RatFunc.num_div_denom f).symm
      _ = f.num.eval lambda / f.denom.eval lambda :=
        h_ratFunc_eval_algebraMap_div lambda f.num f.denom hdenAt
  have hfactorEval := congrArg
    (fun polynomial : ℂ[X] ↦ polynomial.eval lambda) hfactor
  rw [Polynomial.eval_mul, Polynomial.eval_pow] at hfactorEval
  have hparameter :
      ((Polynomial.X - Polynomial.C (0 : ℂ)) : ℂ[X]).eval lambda =
        lambda := by
    simp
  rw [hparameter] at hfactorEval
  rw [heval, ← hfactorEval]
  simp only [unit]
  ring

end OnLeConjecture.DThree
