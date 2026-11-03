/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HRegularProfileCollision

/-!
# Normalization of analytic H fibre branches

An analytic branch in the weighted variables `(x,w,X,W)` whose two weighted
second coordinates are units lifts to the source variables and normalizes to
the affine chart whose first second coordinate equals one.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DThree

/-- Normalization of an arbitrary weighted fibre pair. -/
theorem h_normalized_fibre
    (a : ℕ) (x y X Y w W : ℂ)
    (hy : y ^ (2 * a) = w) (hY : Y ^ (2 * a) = W)
    (hy0 : y ≠ 0)
    (hPfiber : hP x w = hP X W)
    (hQfiber : hQ x w = hQ X W) :
    hP (x / y ^ a) 1 =
        hP (X / y ^ a) ((Y / y) ^ (2 * a)) ∧
      hQ (x / y ^ a) 1 =
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
  have hfirstP := hP_weighted_smul mu (x / mu) 1
  have hsecondP := hP_weighted_smul mu (X / mu) ((Y / y) ^ (2 * a))
  have hfirstQ := hQ_weighted_smul mu (x / mu) 1
  have hsecondQ := hQ_weighted_smul mu (X / mu) ((Y / y) ^ (2 * a))
  have hfirstP' : hP x w =
      mu ^ 3 * hP (x / mu) 1 := by
    simpa [mul_div_cancel₀ x hmu, hmuSq] using hfirstP
  have hsecondP' : hP X W =
      mu ^ 3 * hP (X / mu) ((Y / y) ^ (2 * a)) := by
    simpa [mul_div_cancel₀ X hmu, hsecondWeighted] using hsecondP
  have hfirstQ' : hQ x w =
      mu ^ 4 * hQ (x / mu) 1 := by
    simpa [mul_div_cancel₀ x hmu, hmuSq] using hfirstQ
  have hsecondQ' : hQ X W =
      mu ^ 4 * hQ (X / mu) ((Y / y) ^ (2 * a)) := by
    simpa [mul_div_cancel₀ X hmu, hsecondWeighted] using hsecondQ
  constructor
  · apply mul_left_cancel₀ (pow_ne_zero 3 hmu)
    calc
      mu ^ 3 * hP (x / y ^ a) 1 = hP x w := by
        simpa [mu] using hfirstP'.symm
      _ = hP X W := hPfiber
      _ = mu ^ 3 * hP (X / y ^ a) ((Y / y) ^ (2 * a)) := by
        simpa [mu] using hsecondP'
  · apply mul_left_cancel₀ (pow_ne_zero 4 hmu)
    calc
      mu ^ 4 * hQ (x / y ^ a) 1 = hQ x w := by
        simpa [mu] using hfirstQ'.symm
      _ = hQ X W := hQfiber
      _ = mu ^ 4 * hQ (X / y ^ a) ((Y / y) ^ (2 * a)) := by
        simpa [mu] using hsecondQ'

/-- Normalization divides a weighted homogeneous difference by an analytic
unit. -/
theorem h_normalized_difference
    (a N : ℕ) (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (x y X Y w W : ℂ)
    (hy : y ^ (2 * a) = w) (hY : Y ^ (2 * a) = W)
    (hy0 : y ≠ 0) :
    hFormEval (x / y ^ a) 1 R -
        hFormEval (X / y ^ a) ((Y / y) ^ (2 * a)) R =
      (hFormEval x w R - hFormEval X W R) / (y ^ a) ^ N := by
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
    mu (x / mu) 1
  have hsecond := hFormEval_weighted_smul R N hR
    mu (X / mu) ((Y / y) ^ (2 * a))
  have hfirst' : hFormEval x w R =
      mu ^ N * hFormEval (x / mu) 1 R := by
    simpa [mul_div_cancel₀ x hmu, hmuSq] using hfirst
  have hsecond' : hFormEval X W R =
      mu ^ N * hFormEval (X / mu) ((Y / y) ^ (2 * a)) R := by
    simpa [mul_div_cancel₀ X hmu, hsecondWeighted] using hsecond
  apply (eq_div_iff (pow_ne_zero N hmu)).2
  change
    (hFormEval (x / mu) 1 R -
        hFormEval (X / mu) ((Y / y) ^ (2 * a)) R) * mu ^ N = _
  calc
    (hFormEval (x / mu) 1 R -
          hFormEval (X / mu) ((Y / y) ^ (2 * a)) R) * mu ^ N =
        mu ^ N * hFormEval (x / mu) 1 R -
          mu ^ N * hFormEval (X / mu) ((Y / y) ^ (2 * a)) R := by ring
    _ = hFormEval x w R - hFormEval X W R := by
      rw [← hfirst', ← hsecond']

/-- Source branch data for a normalized collision. -/
structure HNormalizedSourceBranchData
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
  chart_points_ne : (firstX 0, 1) ≠ (secondX, secondT)
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

/-- Analytic weighted fibre data with a positive scalar order produces a
normalized source branch. -/
theorem exists_hNormalizedSourceBranchData
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (x w X W : ℂ → ℂ)
    (hx : AnalyticAt ℂ x 0) (hw : AnalyticAt ℂ w 0)
    (hX : AnalyticAt ℂ X 0) (hW : AnalyticAt ℂ W 0)
    (hw0 : w 0 ≠ 0) (hW0 : W 0 ≠ 0)
    (hdistinct : x 0 ≠ X 0 ∨ w 0 ≠ W 0)
    (hfibre : ∀ᶠ lambda in nhds 0,
      hP (x lambda) (w lambda) = hP (X lambda) (W lambda) ∧
        hQ (x lambda) (w lambda) = hQ (X lambda) (W lambda))
    (m : ℕ) (rawUnit : ℂ → ℂ) (hm : 0 < m)
    (hrawUnit : AnalyticAt ℂ rawUnit 0) (hrawUnit0 : rawUnit 0 ≠ 0)
    (hrawFactor : ∀ᶠ lambda in nhds 0,
      hFormEval (x lambda) (w lambda) R -
          hFormEval (X lambda) (W lambda) R =
        lambda ^ m * rawUnit lambda) :
    Nonempty (HNormalizedSourceBranchData a N R) := by
  have hrootDegree : 0 < 2 * a := by omega
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (w 0) hrootDegree
  obtain ⟨S, hS⟩ := IsAlgClosed.exists_pow_nat_eq (W 0) hrootDegree
  have hs0 : s ≠ 0 := by
    intro hsZero
    apply hw0
    rw [← hs, hsZero, zero_pow (by omega)]
  have hS0 : S ≠ 0 := by
    intro hSZero
    apply hW0
    rw [← hS, hSZero, zero_pow (by omega)]
  obtain ⟨y, hyAnalytic, hyZero, hyPower⟩ :=
    exists_analyticAt_root_with_value w hw hw0
      (2 * a) (by omega) s hs
  obtain ⟨Y, hYAnalytic, hYZero, hYPower⟩ :=
    exists_analyticAt_root_with_value W hW hW0
      (2 * a) (by omega) S hS
  let firstX : ℂ → ℂ := fun lambda ↦ x lambda / y lambda ^ a
  let secondPoint : ℂ → Fin 2 → ℂ := fun lambda ↦
    ![X lambda / y lambda ^ a, Y lambda / y lambda]
  let secondX : ℂ := X 0 / s ^ a
  let secondT : ℂ := S / s
  have hfirstX : AnalyticAt ℂ firstX 0 :=
    hx.div (hyAnalytic.pow a)
      (by simpa only [Pi.pow_apply, hyZero] using pow_ne_zero a hs0)
  have hsecondPoint : AnalyticAt ℂ secondPoint 0 := by
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · exact hX.div (hyAnalytic.pow a)
        (by simpa only [Pi.pow_apply, hyZero] using pow_ne_zero a hs0)
    · exact hYAnalytic.div hyAnalytic (by simpa [hyZero] using hs0)
  have hsecondZero : secondPoint 0 = ![secondX, secondT] := by
    funext i
    fin_cases i
    · simp [secondPoint, secondX, hyZero]
    · simp [secondPoint, secondT, hyZero, hYZero]
  have hsecondT : secondT ≠ 0 := div_ne_zero hS0 hs0
  have hchart : (firstX 0, 1) ≠ (secondX, secondT) := by
    intro hequal
    have hfirst := congrArg Prod.fst hequal
    have hsecond := congrArg Prod.snd hequal
    have hxx : x 0 = X 0 := by
      apply (div_left_inj' (pow_ne_zero a hs0)).mp
      simpa [firstX, secondX, hyZero] using hfirst
    have hsy : s = S := by
      have hratio : S / s = 1 := by
        simpa [secondT] using hsecond.symm
      exact ((div_eq_one_iff_eq hs0).mp hratio).symm
    have hww : w 0 = W 0 := by
      rw [← hs, ← hS, hsy]
    exact hdistinct.elim (fun hne ↦ hne hxx) (fun hne ↦ hne hww)
  have hyTendsto : Tendsto y (nhds 0) (nhds s) := by
    have ht := hyAnalytic.continuousAt
    change Tendsto y (nhds 0) (nhds (y 0)) at ht
    rw [hyZero] at ht
    exact ht
  have hyEventually : ∀ᶠ lambda in nhds 0, y lambda ≠ 0 :=
    hyTendsto.eventually_ne hs0
  have hplane : ∀ᶠ lambda in nhds 0,
      hCollisionPlaneDifference a firstX
        (lambda, secondPoint lambda) = 0 := by
    filter_upwards [hfibre, hyEventually] with lambda hfibreAt hyAt
    obtain ⟨hPfiber, hQfiber⟩ := h_normalized_fibre
      a (x lambda) (y lambda) (X lambda) (Y lambda)
        (w lambda) (W lambda) (hyPower lambda) (hYPower lambda)
          hyAt hfibreAt.1 hfibreAt.2
    funext i
    fin_cases i
    · simpa [hCollisionPlaneDifference, firstX, secondPoint] using
        sub_eq_zero.mpr hPfiber
    · simpa [hCollisionPlaneDifference, firstX, secondPoint] using
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
      hFormEval (firstX lambda) 1 R -
          hFormEval (secondPoint lambda 0)
            (secondPoint lambda 1 ^ (2 * a)) R =
        lambda ^ m * unit lambda := by
    filter_upwards [hrawFactor, hyEventually]
      with lambda hrawAt hyAt
    have hnormalized := h_normalized_difference
      a N R hR (x lambda) (y lambda) (X lambda) (Y lambda)
        (w lambda) (W lambda) (hyPower lambda) (hYPower lambda) hyAt
    change hFormEval (x lambda / y lambda ^ a) 1 R -
        hFormEval (X lambda / y lambda ^ a)
          ((Y lambda / y lambda) ^ (2 * a)) R = _
    rw [hnormalized, hrawAt]
    simp only [unit]
    ring
  exact ⟨
    { firstX := firstX
      secondPoint := secondPoint
      secondX := secondX
      secondT := secondT
      order := m
      unit := unit
      firstX_analyticAt := hfirstX
      secondPoint_analyticAt := hsecondPoint
      secondPoint_zero := hsecondZero
      secondT_ne_zero := hsecondT
      chart_points_ne := hchart
      plane_zero := hplane
      order_pos := hm
      unit_analyticAt := hunit
      unit_zero_ne := hunit0
      third_factor := hthird }
    ⟩

end OnLeConjecture.DThree
