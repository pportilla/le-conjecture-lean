/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HNormalizedCollisionBranch
public import OnLeConjecture.DThree.HZeroSecondCollisionPersistence

/-!
# Source branches with one zero weighted coordinate

An analytic weighted fibre whose second weighted coordinate vanishes to
order `2 * a` lifts to the source chart with second coordinate zero at the
base point.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Analytic weighted fibre data with a second weighted coordinate of order
`2 * a` produces a source branch in the zero second coordinate chart. -/
theorem exists_hZeroSecondSourceBranchData
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (x w X WUnit : ℂ → ℂ)
    (hx : AnalyticAt ℂ x 0) (hw : AnalyticAt ℂ w 0)
    (hX : AnalyticAt ℂ X 0) (hWUnit : AnalyticAt ℂ WUnit 0)
    (hw0 : w 0 ≠ 0) (hWUnit0 : WUnit 0 ≠ 0)
    (hfibre : ∀ᶠ lambda in nhds 0,
      hP (x lambda) (w lambda) =
          hP (X lambda) (lambda ^ (2 * a) * WUnit lambda) ∧
        hQ (x lambda) (w lambda) =
          hQ (X lambda) (lambda ^ (2 * a) * WUnit lambda))
    (m : ℕ) (rawUnit : ℂ → ℂ) (hm : 0 < m)
    (hrawUnit : AnalyticAt ℂ rawUnit 0) (hrawUnit0 : rawUnit 0 ≠ 0)
    (hrawFactor : ∀ᶠ lambda in nhds 0,
      hFormEval (x lambda) (w lambda) R -
          hFormEval (X lambda)
            (lambda ^ (2 * a) * WUnit lambda) R =
        lambda ^ m * rawUnit lambda) :
    Nonempty (HZeroSecondSourceBranchData a N R) := by
  have hrootDegree : 0 < 2 * a := by omega
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (w 0) hrootDegree
  obtain ⟨S, hS⟩ := IsAlgClosed.exists_pow_nat_eq
    (WUnit 0) hrootDegree
  have hs0 : s ≠ 0 := by
    intro hsZero
    apply hw0
    rw [← hs, hsZero, zero_pow (by omega)]
  have hS0 : S ≠ 0 := by
    intro hSZero
    apply hWUnit0
    rw [← hS, hSZero, zero_pow (by omega)]
  obtain ⟨y, hyAnalytic, hyZero, hyPower⟩ :=
    exists_analyticAt_root_with_value w hw hw0
      (2 * a) (by omega) s hs
  obtain ⟨V, hVAnalytic, hVZero, hVPower⟩ :=
    exists_analyticAt_root_with_value WUnit hWUnit hWUnit0
      (2 * a) (by omega) S hS
  let Y : ℂ → ℂ := fun lambda ↦ lambda * V lambda
  let T : ℂ → ℂ := fun lambda ↦ Y lambda / y lambda
  let point : ℂ → Fin 2 → ℂ := fun lambda ↦
    ![x lambda / y lambda ^ a, X lambda / y lambda ^ a]
  let firstX : ℂ := x 0 / s ^ a
  let secondX : ℂ := X 0 / s ^ a
  have hYAnalytic : AnalyticAt ℂ Y 0 := analyticAt_id.mul hVAnalytic
  have hTAnalytic : AnalyticAt ℂ T 0 := by
    exact hYAnalytic.div hyAnalytic (by simpa [hyZero] using hs0)
  have hpointAnalytic : AnalyticAt ℂ point 0 := by
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · exact hx.div (hyAnalytic.pow a)
        (by simpa only [Pi.pow_apply, hyZero] using pow_ne_zero a hs0)
    · exact hX.div (hyAnalytic.pow a)
        (by simpa only [Pi.pow_apply, hyZero] using pow_ne_zero a hs0)
  have hTZero : T 0 = 0 := by
    simp [T, Y]
  have hpointZero : point 0 = ![firstX, secondX] := by
    funext i
    fin_cases i <;> simp [point, firstX, secondX, hyZero]
  have hYPower (lambda : ℂ) :
      Y lambda ^ (2 * a) = lambda ^ (2 * a) * WUnit lambda := by
    change (lambda * V lambda) ^ (2 * a) = _
    rw [mul_pow, hVPower]
  have hyTendsto : Tendsto y (nhds 0) (nhds s) := by
    have ht := hyAnalytic.continuousAt
    change Tendsto y (nhds 0) (nhds (y 0)) at ht
    rw [hyZero] at ht
    exact ht
  have hyEventually : ∀ᶠ lambda in nhds 0, y lambda ≠ 0 :=
    hyTendsto.eventually_ne hs0
  have hplane : ∀ᶠ lambda in nhds 0,
      hZeroSecondPlaneDifference a T (lambda, point lambda) = 0 := by
    filter_upwards [hfibre, hyEventually]
      with lambda hfibreAt hyAt
    obtain ⟨hPfiber, hQfiber⟩ := h_normalized_fibre
      a (x lambda) (y lambda) (X lambda) (Y lambda)
        (w lambda) (lambda ^ (2 * a) * WUnit lambda)
          (hyPower lambda) (hYPower lambda) hyAt
            hfibreAt.1 hfibreAt.2
    funext i
    fin_cases i
    · simpa [hZeroSecondPlaneDifference, point, T] using
        sub_eq_zero.mpr hPfiber
    · simpa [hZeroSecondPlaneDifference, point, T] using
        sub_eq_zero.mpr hQfiber
  let unit : ℂ → ℂ := fun lambda ↦
    rawUnit lambda / (y lambda ^ a) ^ N
  have hunit : AnalyticAt ℂ unit 0 :=
    hrawUnit.div ((hyAnalytic.pow a).pow N)
      (by simpa only [Pi.pow_apply, hyZero] using
        pow_ne_zero N (pow_ne_zero a hs0))
  have hunit0 : unit 0 ≠ 0 := by
    change rawUnit 0 / (y 0 ^ a) ^ N ≠ 0
    rw [hyZero]
    exact div_ne_zero hrawUnit0
      (pow_ne_zero N (pow_ne_zero a hs0))
  have hthird : ∀ᶠ lambda in nhds 0,
      hFormEval (point lambda 0) 1 R -
          hFormEval (point lambda 1) (T lambda ^ (2 * a)) R =
        lambda ^ m * unit lambda := by
    filter_upwards [hrawFactor, hyEventually]
      with lambda hrawAt hyAt
    have hnormalized := h_normalized_difference
      a N R hR (x lambda) (y lambda) (X lambda) (Y lambda)
        (w lambda) (lambda ^ (2 * a) * WUnit lambda)
          (hyPower lambda) (hYPower lambda) hyAt
    change hFormEval (x lambda / y lambda ^ a) 1 R -
        hFormEval (X lambda / y lambda ^ a)
          ((Y lambda / y lambda) ^ (2 * a)) R = _
    rw [hnormalized, hrawAt]
    simp only [unit]
    ring
  exact ⟨
    { T := T
      point := point
      firstX := firstX
      secondX := secondX
      order := m
      unit := unit
      T_analyticAt := hTAnalytic
      point_analyticAt := hpointAnalytic
      T_zero := hTZero
      point_zero := hpointZero
      plane_zero := hplane
      order_pos := hm
      unit_analyticAt := hunit
      unit_zero_ne := hunit0
      third_factor := hthird }
    ⟩

end OnLeConjecture.DThree
