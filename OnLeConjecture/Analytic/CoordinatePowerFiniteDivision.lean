/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteDivisionRemainder
public import OnLeConjecture.Analytic.Hyperplane

/-!
# Analytic division by a coordinate power minus an analytic parameter

Scaling the companion operator makes its nilpotent value at the origin
arbitrarily small. Banach algebra evaluation then produces a convergent
quotient and remainder for a dividend with any finite number of variables.
-/

public section

open Filter Metric
open scoped BigOperators NNReal ENNReal Topology

namespace OnLeConjecture.Analytic.Germ

/-- Analytic dependence of a scaled companion input on analytic scalar,
retained-coordinate, and coefficient maps. -/
theorem analyticAt_scaledDivisionInput {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}
    (d : ℕ) (c : ℂ) (x : E → ℂ) (y : E → Source n)
    (a : E → GeneralCoefficientSpace d)
    (hx : AnalyticAt ℂ x 0) (hy : AnalyticAt ℂ y 0) (ha : AnalyticAt ℂ a 0) :
    AnalyticAt ℂ (fun z => scaledDivisionInput d c (x z) (y z) (a z)) 0 := by
  apply AnalyticAt.pi
  intro i
  induction i using Fin.cases with
  | zero =>
      have hpair : AnalyticAt ℂ (fun z => (c⁻¹ * x z, a z)) 0 :=
        (analyticAt_const.mul hx).prod ha
      have hop : AnalyticAt ℂ (fun z => generalDivisionOperator (c⁻¹ * x z) (a z)) 0 := by
        simpa only [Function.comp_def] using
          AnalyticAt.comp (x := (0 : E))
            (analyticAt_generalDivisionOperator (d := d) (c⁻¹ * x 0, a 0)) hpair
      exact hop.const_smul (c := c)
  | succ i =>
      have hi : AnalyticAt ℂ (fun z => y z i) 0 := by
        simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt (y 0)).comp hy
      exact hi.smul analyticAt_const

/-- A nonzero scaling places the base companion tuple inside every
convergence ball of positive radius. -/
theorem exists_scaledDivisionInput_base_mem {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Source (n + 1)) ℂ) (d : ℕ)
    (hp : 0 < p.radius) :
    ∃ c : ℂ, c ≠ 0 ∧ scaledDivisionInput (n := n) d c 0 0 0 ∈ Metric.eball 0
      (finiteBanachExtensionSeries (A := GeneralDivisionEndomorphism d) p).radius := by
  let B : Fin (n + 1) → GeneralDivisionEndomorphism d :=
    Fin.cases (generalDivisionOperator 0 0) (fun _ => 0)
  have hcontinuous : ContinuousAt (fun c : ℂ => c • B) 0 := by fun_prop
  have hnear : ∀ᶠ c : ℂ in nhds 0, c • B ∈ Metric.eball 0
      (finiteBanachExtensionSeries (A := GeneralDivisionEndomorphism d) p).radius := by
    have hz : (0 : ℂ) • B = 0 := by
      module
    apply hcontinuous.eventually
    change Metric.eball 0 (finiteBanachExtensionSeries
      (A := GeneralDivisionEndomorphism d) p).radius ∈ nhds ((0 : ℂ) • B)
    rw [hz]
    exact Metric.eball_mem_nhds (0 : Fin (n + 1) → GeneralDivisionEndomorphism d)
      (finiteBanachExtensionSeries_radius_pos (A := GeneralDivisionEndomorphism d) p hp)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let c : ℂ := (ε / 2 : ℝ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (half_pos hε).ne'
  have hcsmall : c ∈ Metric.ball (0 : ℂ) ε := by
    simp only [Metric.mem_ball, dist_zero_right, c, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  refine ⟨c, hc, ?_⟩
  have heq : scaledDivisionInput (n := n) d c 0 0 0 = c • B := by
    funext i
    induction i using Fin.cases with
    | zero => simp [scaledDivisionInput, B]
    | succ i =>
        change (0 : ℂ) • (1 : GeneralDivisionEndomorphism d) =
          c • (0 : GeneralDivisionEndomorphism d)
        module
  rw [heq]
  exact hball hcsmall

/-- The rescaled lower coefficients of `x^(d+1)-h(y)`. -/
@[expose] noncomputable def coordinatePowerDivisionCoefficients {n : ℕ}
    (d : ℕ) (c : ℂ) (h : Source n → ℂ) (y : Source n) :
    GeneralCoefficientSpace d := Pi.single 0 (-(c⁻¹) ^ (d + 1) * h y)

theorem analyticAt_coordinatePowerDivisionCoefficients {n : ℕ}
    (d : ℕ) (c : ℂ) (h : Source n → ℂ) (hh : AnalyticAt ℂ h 0) :
    AnalyticAt ℂ (coordinatePowerDivisionCoefficients d c h) 0 := by
  apply AnalyticAt.pi
  intro i
  by_cases hi : i = 0
  · subst i
    simpa only [coordinatePowerDivisionCoefficients, Pi.single_eq_same,
      Pi.smul_def, smul_eq_mul] using hh.const_smul (c := -(c⁻¹) ^ (d + 1))
  · simpa [coordinatePowerDivisionCoefficients, Pi.single_apply, hi, Ne.symm hi]
      using (analyticAt_const : AnalyticAt ℂ (fun _ : Source n => (0 : ℂ)) 0)

theorem coordinatePowerDivisionCoefficients_zero {n : ℕ}
    (d : ℕ) (c : ℂ) (h : Source n → ℂ) (hh : h 0 = 0) :
    coordinatePowerDivisionCoefficients d c h 0 = 0 := by
  simp [coordinatePowerDivisionCoefficients, hh]

/-- The scaled companion still intertwines with the unscaled scalar
coordinate tuple. -/
theorem evaluation_scaledDivisionInput {n : ℕ} (d : ℕ) (c : ℂ) (hc : c ≠ 0)
    (z : Source (n + 1)) (a : GeneralCoefficientSpace d)
    (i : Fin (n + 1)) (s : GeneralDivisionState d) :
    generalDivisionStateEvaluationLinear (c⁻¹ * z 0) a
      (scaledDivisionInput d c (z 0) (hyperplaneTail n z) a i s) =
        z i * generalDivisionStateEvaluationLinear (c⁻¹ * z 0) a s := by
  induction i using Fin.cases with
  | zero =>
      simp only [scaledDivisionInput, Fin.cases_zero, smul_apply, map_smul,
        generalDivisionStateEvaluationLinear_apply, generalDivisionStateEvaluation_operator,
        smul_eq_mul]
      field_simp
  | succ i =>
      simp only [scaledDivisionInput, Fin.cases_succ, smul_apply, one_apply_eq_self,
        map_smul, smul_eq_mul, hyperplaneTail_apply]

/-- Analytic division of an arbitrary finite-dimensional Taylor sum by
the monic polynomial `x^(d+1)-h(y)`. -/
theorem exists_analytic_coordinatePower_division {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Source (n + 1)) ℂ) (d : ℕ)
    (hp : 0 < p.radius) (h : Source n → ℂ)
    (hh : AnalyticAt ℂ h 0) (hhZero : h 0 = 0) :
    ∃ Q : Source (n + 1) → ℂ, ∃ R : Source n → GeneralCoefficientSpace d,
      AnalyticAt ℂ Q 0 ∧ AnalyticAt ℂ R 0 ∧
      ∀ᶠ z in nhds 0,
        p.sum z = (z 0 ^ (d + 1) - h (hyperplaneTail n z)) * Q z +
          ∑ i : Fin (d + 1), z 0 ^ i.1 * R (hyperplaneTail n z) i := by
  obtain ⟨c, hc, hbase⟩ := exists_scaledDivisionInput_base_mem p d hp
  let a := coordinatePowerDivisionCoefficients d c h
  have ha : AnalyticAt ℂ a 0 := analyticAt_coordinatePowerDivisionCoefficients d c h hh
  have haZero : a 0 = 0 := coordinatePowerDivisionCoefficients_zero d c h hhZero
  let q := finiteBanachExtensionSeries (A := GeneralDivisionEndomorphism d) p
  let input : Source (n + 1) → Fin (n + 1) → GeneralDivisionEndomorphism d :=
    fun z => scaledDivisionInput d c (z 0) (hyperplaneTail n z) (a (hyperplaneTail n z))
  let inputZero : Source n → Fin (n + 1) → GeneralDivisionEndomorphism d :=
    fun y => scaledDivisionInput d c 0 y (a y)
  have htail := (hyperplaneTail n).analyticAt (0 : Source (n + 1))
  have haTail : AnalyticAt ℂ (fun z => a (hyperplaneTail n z)) 0 := by
    exact AnalyticAt.comp_of_eq (g := a) (f := hyperplaneTail n) ha htail (map_zero _)
  have hinput : AnalyticAt ℂ input 0 :=
    analyticAt_scaledDivisionInput d c _ _ _
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ)
        (0 : Fin (n + 1))).analyticAt 0) htail haTail
  have hinputZero : AnalyticAt ℂ inputZero 0 :=
    analyticAt_scaledDivisionInput d c _ _ _ analyticAt_const analyticAt_id ha
  have hinputBase : input 0 ∈ Metric.eball 0 q.radius := by
    simpa only [input, map_zero, haZero, Pi.zero_apply] using hbase
  have hinputZeroBase : inputZero 0 ∈ Metric.eball 0 q.radius := by
    simpa only [inputZero, haZero] using hbase
  let state : Source (n + 1) → GeneralDivisionState d := fun z =>
    q.sum (input z) (generalDivisionInitialState d)
  let stateZero : Source n → GeneralDivisionState d := fun y =>
    q.sum (inputZero y) (generalDivisionInitialState d)
  have hstate : AnalyticAt ℂ state 0 := by
    have hsum := (finiteBanachExtensionSeries_analyticAt_of_mem p hp
      (input 0) hinputBase).comp hinput
    exact (ContinuousLinearMap.apply ℂ (GeneralDivisionState d)
      (generalDivisionInitialState d)).analyticAt _ |>.comp hsum
  have hstateZero : AnalyticAt ℂ stateZero 0 := by
    have hsum := (finiteBanachExtensionSeries_analyticAt_of_mem p hp (inputZero 0)
      hinputZeroBase).comp hinputZero
    exact (ContinuousLinearMap.apply ℂ (GeneralDivisionState d)
      (generalDivisionInitialState d)).analyticAt _ |>.comp hsum
  let Q : Source (n + 1) → ℂ := fun z => (c⁻¹) ^ (d + 1) * (state z).1
  let R : Source n → GeneralCoefficientSpace d := fun y i => (c⁻¹) ^ i.1 * (stateZero y).2 i
  have hstateFst : AnalyticAt ℂ (fun z => (state z).1) 0 := by
    exact AnalyticAt.comp (f := state) (g := Prod.fst)
      ((ContinuousLinearMap.fst ℂ ℂ (GeneralCoefficientSpace d)).analyticAt (state 0)) hstate
  have hstateZeroSnd : AnalyticAt ℂ (fun y => (stateZero y).2) 0 := by
    exact AnalyticAt.comp (f := stateZero) (g := Prod.snd)
      ((ContinuousLinearMap.snd ℂ ℂ (GeneralCoefficientSpace d)).analyticAt
        (stateZero 0)) hstateZero
  have hQ : AnalyticAt ℂ Q 0 := by
    simpa only [Q, Pi.smul_def, smul_eq_mul] using hstateFst.const_smul (c := (c⁻¹) ^ (d + 1))
  have hR : AnalyticAt ℂ R 0 := by
    apply AnalyticAt.pi
    intro i
    have hi : AnalyticAt ℂ (fun y => (stateZero y).2 i) 0 := by
      simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
        AnalyticAt.comp (f := fun y => (stateZero y).2)
          (g := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i).analyticAt
            ((stateZero 0).2)) hstateZeroSnd
    simpa only [R, Pi.smul_def, smul_eq_mul] using hi.const_smul (c := (c⁻¹) ^ i.1)
  have hpMem : ∀ᶠ z : Source (n + 1) in nhds 0, z ∈ Metric.eball 0 p.radius :=
    Metric.eball_mem_nhds 0 hp
  have hinputMem : ∀ᶠ z in nhds 0, input z ∈ Metric.eball 0 q.radius :=
    hinput.continuousAt.eventually (Metric.isOpen_eball.mem_nhds hinputBase)
  have hzeroMem : ∀ᶠ z : Source (n + 1) in nhds 0,
      inputZero (hyperplaneTail n z) ∈ Metric.eball 0 q.radius := by
    have hi : AnalyticAt ℂ (fun z => inputZero (hyperplaneTail n z)) 0 :=
      AnalyticAt.comp_of_eq (g := inputZero) (f := hyperplaneTail n)
        hinputZero htail (map_zero _)
    apply hi.continuousAt.eventually
    change Metric.eball 0 q.radius ∈ nhds (inputZero (hyperplaneTail n 0))
    rw [map_zero]
    exact Metric.isOpen_eball.mem_nhds hinputZeroBase
  refine ⟨Q, R, hQ, hR, ?_⟩
  filter_upwards [hpMem, hinputMem, hzeroMem] with z hpz hxz hzeroz
  have hevaluation := linearEvaluation_finiteBanachExtensionSeries_sum p
    (generalDivisionStateEvaluationLinear (c⁻¹ * z 0) (a (hyperplaneTail n z)))
    (input z) z (evaluation_scaledDivisionInput d c hc z (a (hyperplaneTail n z)))
    (generalDivisionInitialState d) hxz hpz
  have hinitial : generalDivisionStateEvaluationLinear (c⁻¹ * z 0)
      (a (hyperplaneTail n z)) (generalDivisionInitialState d) = 1 := by
    simp [generalDivisionStateEvaluationLinear_apply, generalDivisionStateEvaluation,
      generalDivisionInitialState]
  rw [hinitial, mul_one] at hevaluation
  have hremainder : (state z).2 = (stateZero (hyperplaneTail n z)).2 :=
    scaledDivisionInput_extension_remainder_independent p d c (z 0) 0
      (hyperplaneTail n z) (a (hyperplaneTail n z)) hxz hzeroz
  have hpolynomial : generalDivisionPolynomialValue (c⁻¹ * z 0) (a (hyperplaneTail n z)) =
      (c⁻¹) ^ (d + 1) * (z 0 ^ (d + 1) - h (hyperplaneTail n z)) := by
    simp [a, coordinatePowerDivisionCoefficients, generalDivisionPolynomialValue,
      Pi.single_apply, mul_pow]
    ring
  change generalDivisionStateEvaluationLinear (c⁻¹ * z 0)
    (a (hyperplaneTail n z)) (state z) = p.sum z at hevaluation
  rw [generalDivisionStateEvaluationLinear_apply, generalDivisionStateEvaluation,
    hpolynomial, hremainder] at hevaluation
  rw [← hevaluation]
  congr 1
  · dsimp [Q]
    ring
  · apply Finset.sum_congr rfl
    intro i _hi
    dsimp [R]
    rw [mul_pow]
    ring

/-- Division by a coordinate power minus an analytic parameter for an
arbitrary analytic function, with convergent quotient and remainder. -/
theorem exists_analytic_function_coordinatePower_division {n : ℕ}
    (F : Source (n + 1) → ℂ) (hF : AnalyticAt ℂ F 0) (d : ℕ)
    (h : Source n → ℂ) (hh : AnalyticAt ℂ h 0) (hhZero : h 0 = 0) :
    ∃ Q : Source (n + 1) → ℂ, ∃ R : Source n → GeneralCoefficientSpace d,
      AnalyticAt ℂ Q 0 ∧ AnalyticAt ℂ R 0 ∧
      ∀ᶠ z in nhds 0,
        F z = (z 0 ^ (d + 1) - h (hyperplaneTail n z)) * Q z +
          ∑ i : Fin (d + 1), z 0 ^ i.1 * R (hyperplaneTail n z) i := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨Q, R, hQ, hR, hdivision⟩ :=
    exists_analytic_coordinatePower_division p d hp.radius_pos h hh hhZero
  refine ⟨Q, R, hQ, hR, ?_⟩
  have hpsum := (p.hasFPowerSeriesOnBall hp.radius_pos).hasFPowerSeriesAt
  filter_upwards [hp.eventually_hasSum_sub, hpsum.eventually_hasSum_sub, hdivision]
    with z hz hzsum hzdivision
  have heq : F z = p.sum z := hz.unique hzsum
  exact heq.trans hzdivision

end OnLeConjecture.Analytic.Germ
