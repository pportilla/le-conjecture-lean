/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicInvariantNoRoots
public import OnLeConjecture.DTwo.CyclicResidualCollision
public import OnLeConjecture.DThree.HAnalyticUnitRoot
public import OnLeConjecture.DThree.HHardOddRegularBranch

/-!
# Analytic opposite-sign branches for the cyclic pair

The two first coordinates are eliminated, leaving the second coordinate
of the second point as parameter. This chart includes its zero value.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic OnLeConjecture.DThree

/-- A root of the residual restriction gives an analytic branch on which
the third difference has finite positive order, including when `Y = 0`. -/
theorem exists_cyclicOpposite_branch_finite_order
    (k p : ℕ) (hk : 0 < k) (hp : 0 < p) (c s Y : ℂ)
    (hc : c ≠ 0) (hs : s ≠ 0) (hY : 2 * s ^ p = c * (Y ^ k - 1))
    (F : _root_.Polynomial ℂ) (hF : F ≠ 0) (hroot : F.IsRoot s) :
    ∃ x : ℂ → ℂ, AnalyticAt ℂ x 0 ∧ x 0 = s ∧
      (∀ u, 2 * x u ^ p = c * ((Y + u) ^ k - 1)) ∧
      ∃ m : ℕ, ∃ unit : ℂ → ℂ, 0 < m ∧ AnalyticAt ℂ unit 0 ∧ unit 0 ≠ 0 ∧
        ∀ᶠ u in nhds 0, 2 * x u * F.eval (x u) = u ^ m * unit u := by
  let power : ℂ → ℂ := fun u ↦ c / 2 * ((Y + u) ^ k - 1)
  have hpower : AnalyticAt ℂ power 0 :=
    analyticAt_const.mul (((analyticAt_const.add analyticAt_id).pow k).sub analyticAt_const)
  have hpowerValue : power 0 = s ^ p := by
    dsimp [power]
    simp only [add_zero]
    linear_combination -(1 / 2 : ℂ) * hY
  obtain ⟨x, hx, hxs, hxpower⟩ := exists_analyticAt_root_with_value
    power hpower (by rw [hpowerValue]; exact pow_ne_zero p hs) p hp.ne' s hpowerValue.symm
  have hcurve (u : ℂ) : 2 * x u ^ p = c * ((Y + u) ^ k - 1) := by
    rw [hxpower]
    dsimp [power]
    ring
  let scalar : ℂ → ℂ := fun u ↦ 2 * x u * F.eval (x u)
  have hscalar : AnalyticAt ℂ scalar 0 := by
    have hcomp : AnalyticAt ℂ (fun u ↦ F.eval (x u)) 0 := by
      simpa [_root_.Polynomial.aeval_def] using hx.aeval_polynomial F
    exact (analyticAt_const.mul hx).mul hcomp
  have hscalarZero : scalar 0 = 0 := by
    simp [scalar, hxs, show F.eval s = 0 from hroot]
  have hnonzero : ¬ ∀ᶠ u in nhds 0, scalar u = 0 := by
    intro hzero
    obtain ⟨_, quotient, hfactor, hquotient⟩ := exists_polynomial_local_factorization hF hroot
    have hunit : AnalyticAt ℂ (fun u ↦ quotient.eval (x u)) 0 := by
      simpa [_root_.Polynomial.aeval_def] using hx.aeval_polynomial quotient
    have hxne : ∀ᶠ u in nhds 0, x u ≠ 0 :=
      hx.continuousAt.tendsto.eventually_ne (by simpa [hxs] using hs)
    have hqne : ∀ᶠ u in nhds 0, quotient.eval (x u) ≠ 0 :=
      hunit.continuousAt.tendsto.eventually_ne (by simpa [hxs] using hquotient)
    have hconstant : ∀ᶠ u in nhds 0, x u = s := by
      filter_upwards [hzero, hxne, hqne] with u hzeroAt hxneAt hqneAt
      have hFzero : F.eval (x u) = 0 := by
        exact (mul_eq_zero.mp hzeroAt).resolve_left (mul_ne_zero (by norm_num) hxneAt)
      have hfactored := congrArg (fun P : _root_.Polynomial ℂ ↦ P.eval (x u)) hfactor
      simp only [_root_.Polynomial.eval_mul, _root_.Polynomial.eval_pow,
        _root_.Polynomial.eval_sub, _root_.Polynomial.eval_X,
        _root_.Polynomial.eval_C, hFzero] at hfactored
      have hpow : (x u - s) ^ F.rootMultiplicity s = 0 :=
        (mul_eq_zero.mp hfactored.symm).resolve_right hqneAt
      exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpow)
    let difference : _root_.Polynomial ℂ :=
      _root_.Polynomial.X ^ k - _root_.Polynomial.C (Y ^ k)
    have hdifference : difference ≠ 0 := by
      intro h
      have heq := congrArg (fun P : _root_.Polynomial ℂ ↦ P.coeff k) h
      simp only [difference, _root_.Polynomial.coeff_sub, _root_.Polynomial.coeff_X_pow,
        _root_.Polynomial.coeff_C, if_neg hk.ne',
        _root_.Polynomial.coeff_zero, sub_zero] at heq
      norm_num at heq
    apply not_eventually_polynomial_eval_add_eq_zero difference hdifference Y
    filter_upwards [hconstant] with u hu
    have hcurveAt := hcurve u
    rw [hu] at hcurveAt
    have hdiff : (Y + u) ^ k - Y ^ k = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hc
      linear_combination hY - hcurveAt
    simpa [difference] using hdiff
  obtain ⟨m, unit, hunit, hunitZero, hfactor⟩ :=
    hscalar.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnonzero
  have hm : 0 < m := by
    by_contra h
    have hmzero : m = 0 := by omega
    have hbase := hfactor.self_of_nhds
    simp [hmzero, hscalarZero] at hbase
    exact hunitZero hbase.symm
  refine ⟨x, hx, hxs, hcurve, m, unit, hm, hunit, hunitZero, ?_⟩
  simpa only [scalar, sub_zero, smul_eq_mul] using hfactor

/-- The two plane equations with the two first coordinates variable. -/
@[expose] noncomputable def cyclicOppositePlane (k p : ℕ) (c Y : ℂ)
    (q : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![q.2 0 ^ 2 - q.2 1 ^ 2,
    q.2 0 ^ p + c - (q.2 1 ^ p + c * (Y + q.1) ^ k)]

@[expose] noncomputable def cyclicOppositeDerivative (p : ℕ) (s : ℂ) :
    (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLin' !![2 * s, 2 * s;
    (p : ℂ) * s ^ (p - 1), -(p : ℂ) * s ^ (p - 1)]).toContinuousLinearMap

theorem cyclicOpposite_pointDerivative (k p : ℕ) (hp : Odd p) (c s Y : ℂ) :
    HasStrictFDerivAt (fun v ↦ cyclicOppositePlane k p c Y (0, v))
      (cyclicOppositeDerivative p s) ![s, -s] := by
  have hneg : (-s) ^ (p - 1) = s ^ (p - 1) := by
    have hparity : Even (p - 1) := Nat.Odd.sub_odd hp (by decide : Odd 1)
    exact hparity.neg_pow s
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  · convert ((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![s, -s]).pow 2).sub
      ((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![s, -s]).pow 2) using 1
    all_goals ext v
    all_goals simp [cyclicOppositePlane, cyclicOppositeDerivative,
      Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
  · convert (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![s, -s]).pow p).add_const c).sub
      (((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![s, -s]).pow p).add_const
        (c * Y ^ k)) using 1
    all_goals ext v
    all_goals simp [cyclicOppositePlane, cyclicOppositeDerivative,
      Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ, hneg]
    all_goals ring

theorem cyclicOpposite_derivative_invertible (p : ℕ) (hp : 0 < p) (s : ℂ) (hs : s ≠ 0) :
    (cyclicOppositeDerivative p s).IsInvertible := by
  have hdet : (cyclicOppositeDerivative p s).det ≠ 0 := by
    have heq : (cyclicOppositeDerivative p s).det =
        -4 * (p : ℂ) * s * s ^ (p - 1) := by
      simp [cyclicOppositeDerivative, LinearMap.det_toContinuousLinearMap,
        LinearMap.det_toLin', Matrix.det_fin_two]
      ring
    rw [heq]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Nat.cast_ne_zero.mpr hp.ne')) hs) (pow_ne_zero _ hs)
  exact ⟨(cyclicOppositeDerivative p s).toContinuousLinearEquivOfDetNeZero hdet,
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _⟩

end OnLeConjecture.DTwo
