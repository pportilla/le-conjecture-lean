/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.AnalyticImplicitFunction
public import OnLeConjecture.Analytic.Germ
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Actual analytic branches of the weighted limiting plane equation

After the finite base change and weighted source scaling, the first-plane
equation has a quadratic special fiber. Every point of that fiber where
the second source coordinate is nonzero lifts to an actual analytic
one-parameter branch. The higher correction is retained in the equation.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic

theorem cyclicWeightedLimit_scaling_identity
    (p ν j r : ℕ) (hp : 2 ≤ p) (hr : r = ν + p * j)
    (t s S ε K : ℂ) :
    (t ^ r * s) ^ 2 - (t ^ r * S) ^ 2 +
        (t ^ 2) ^ ν * ((t ^ 2) ^ (p * j) * ε +
          ((t ^ r * s) ^ p - (t ^ r * S) ^ p) * K) =
      t ^ (2 * r) * (s ^ 2 - S ^ 2 + ε +
        t ^ (2 * ν + r * (p - 2)) * (s ^ p - S ^ p) * K) := by
  have he1 : 2 * ν + 2 * (p * j) = 2 * r := by omega
  have he2 : 2 * ν + r * p = 2 * r + (2 * ν + r * (p - 2)) := by
    have h := Nat.sub_add_cancel hp
    nlinarith
  have hpow1 : t ^ (2 * ν) * t ^ (2 * (p * j)) = t ^ (2 * r) := by
    rw [← pow_add, he1]
  have hpow2 : t ^ (2 * ν) * t ^ (r * p) =
      t ^ (2 * r) * t ^ (2 * ν + r * (p - 2)) := by
    rw [← pow_add, he2, pow_add]
  simp only [mul_pow, ← pow_mul, Nat.mul_comm r 2]
  calc
    _ = t ^ (2 * r) * (s ^ 2 - S ^ 2) +
        (t ^ (2 * ν) * t ^ (2 * (p * j))) * ε +
        (t ^ (2 * ν) * t ^ (r * p)) * (s ^ p - S ^ p) * K := by ring
    _ = _ := by rw [hpow1, hpow2]; ring

@[expose] noncomputable def cyclicWeightedLimitEquation
    (p ν r : ℕ) (ε : ℂ → ℂ) (K : Source 3 → ℂ) (s : ℂ) (q : ℂ × ℂ) : ℂ :=
  s ^ 2 - q.2 ^ 2 + ε (q.1 ^ 2) +
    q.1 ^ (2 * ν + r * (p - 2)) * (s ^ p - q.2 ^ p) *
      K (![q.1 ^ r * s, q.1 ^ r * q.2, q.1 ^ 2])

theorem cyclicWeightedLimitEquation_analyticAt
    (p ν r : ℕ) (hr : 0 < r)
    (ε : ℂ → ℂ) (hε : AnalyticAt ℂ ε 0)
    (K : Source 3 → ℂ) (hK : AnalyticAt ℂ K 0) (s S : ℂ) :
    AnalyticAt ℂ (cyclicWeightedLimitEquation p ν r ε K s) (0, S) := by
  have hmap : AnalyticAt ℂ
      (fun q : ℂ × ℂ => (![q.1 ^ r * s, q.1 ^ r * q.2, q.1 ^ 2] : Source 3)) (0, S) := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    · exact (analyticAt_fst.pow r).mul analyticAt_const
    · exact (analyticAt_fst.pow r).mul analyticAt_snd
    · exact analyticAt_fst.pow 2
  have hvec : (![0, 0, 0] : Source 3) = 0 := by ext i; fin_cases i <;> rfl
  have hcomp : AnalyticAt ℂ
      (fun q : ℂ × ℂ => K (![q.1 ^ r * s, q.1 ^ r * q.2, q.1 ^ 2])) (0, S) := by
    apply AnalyticAt.comp (x := ((0, S) : ℂ × ℂ)) _ hmap
    simpa only [zero_pow hr.ne', zero_mul, zero_pow (by decide : 2 ≠ 0), hvec] using hK
  have hunit : AnalyticAt ℂ (fun q : ℂ × ℂ => ε (q.1 ^ 2)) (0, S) := by
    apply AnalyticAt.comp (x := ((0, S) : ℂ × ℂ)) _ (analyticAt_fst.pow 2)
    simpa only [Pi.pow_apply, zero_pow (by decide : 2 ≠ 0)] using hε
  exact ((analyticAt_const.sub (analyticAt_snd.pow 2)).add hunit).add
    (((analyticAt_fst.pow (2 * ν + r * (p - 2))).mul
      (analyticAt_const.sub (analyticAt_snd.pow p))).mul hcomp)

theorem cyclicWeightedLimitEquation_special
    (p ν r : ℕ) (hν : 0 < ν) (ε : ℂ → ℂ) (K : Source 3 → ℂ) (s S : ℂ) :
    cyclicWeightedLimitEquation p ν r ε K s (0, S) = s ^ 2 - S ^ 2 + ε 0 := by
  have hE : 2 * ν + r * (p - 2) ≠ 0 := by omega
  simp [cyclicWeightedLimitEquation, zero_pow hE]

/-- A nonsingular point of the limiting quadratic equation lifts to an
analytic branch of the full rescaled plane equation. -/
theorem exists_cyclicWeightedLimit_analytic_branch
    (p ν r : ℕ) (hν : 0 < ν) (hr : 0 < r)
    (ε : ℂ → ℂ) (hε : AnalyticAt ℂ ε 0)
    (K : Source 3 → ℂ) (hK : AnalyticAt ℂ K 0)
    (s S : ℂ) (hS : S ≠ 0) (hpoint : S ^ 2 = s ^ 2 + ε 0) :
    ∃ B : ℂ → ℂ, AnalyticAt ℂ B 0 ∧ B 0 = S ∧
      ∀ᶠ t in 𝓝 (0 : ℂ), cyclicWeightedLimitEquation p ν r ε K s (t, B t) = 0 := by
  let Φ := cyclicWeightedLimitEquation p ν r ε K s
  have hΦ := cyclicWeightedLimitEquation_analyticAt p ν r hr ε hε K hK s S
  have hzero : Φ (0, S) = 0 := by
    change cyclicWeightedLimitEquation p ν r ε K s (0, S) = 0
    rw [cyclicWeightedLimitEquation_special p ν r hν, hpoint]
    ring
  let a : ℂ := -(2 * S)
  have ha : a ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (by norm_num) hS)
  let e : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 a ha)
  have hderiv : HasFDerivAt (fun z : ℂ => Φ (0, z)) (e : ℂ →L[ℂ] ℂ) S := by
    have hscalar : HasDerivAt (fun z : ℂ => s ^ 2 - z ^ 2 + ε 0) a S := by
      simpa [a] using (((hasDerivAt_pow 2 S).const_sub (s ^ 2)).add_const (ε 0))
    have heq : (fun z : ℂ => Φ (0, z)) = (fun z : ℂ => s ^ 2 - z ^ 2 + ε 0) :=
      funext (cyclicWeightedLimitEquation_special p ν r hν ε K s)
    have he : (e : ℂ →L[ℂ] ℂ) = ContinuousLinearMap.toSpanSingleton ℂ a := by
      ext
      simp [e, ContinuousLinearEquiv.smulLeft, mul_comm]
    rw [heq, he]
    exact hscalar.hasFDerivAt
  have hcomp := hΦ.hasStrictFDerivAt.comp S
    (ContinuousLinearMap.inr ℂ ℂ ℂ).hasStrictFDerivAt
  have hinvertible : (fderiv ℂ Φ (0, S) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible :=
    ⟨e, (hcomp.hasFDerivAt.unique hderiv).symm⟩
  exact exists_analytic_simpleZeroBranch Φ S hzero hΦ hinvertible

end OnLeConjecture.DTwo
