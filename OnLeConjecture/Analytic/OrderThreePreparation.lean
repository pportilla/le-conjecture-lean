/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CubicFunctionalPreparation
public import OnLeConjecture.Analytic.OrderThreeReduction
public import OnLeConjecture.PlaneCurve.Tschirnhausen

/-!
# Analytic Weierstrass preparation in order three

Radial rescaling places the cubic division operator inside the convergence
ball of the Banach algebra Taylor extension. The functional cubic preparation
then produces analytic coefficients and an analytic unit. A Tschirnhausen
coordinate transformation removes the quadratic coefficient.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Metric
open scoped NNReal ENNReal Topology

namespace Germ

/-- Every analytic germ has a function representative analytic at the
origin. -/
theorem exists_analyticRepresentative {n : ℕ} (f : Germ n) :
    ∃ F : Source n → ℂ, ∃ hF : AnalyticAt ℂ F 0,
      f = Germ.ofFunction F hF := by
  rcases f with ⟨f, hf⟩
  change IsAnalyticGerm f at hf
  induction f using Filter.Germ.inductionOn with
  | _ F =>
      rw [isAnalyticGerm_ofFun] at hf
      exact ⟨F, hf, rfl⟩

/-- Scalar multiplication on the two dimensional source as a continuous
linear map. -/
@[expose] noncomputable def radialScaleContinuousLinearMap (c : ℂ) :
    Source 2 →L[ℂ] Source 2 :=
  c • ContinuousLinearMap.id ℂ (Source 2)

@[simp]
theorem radialScaleContinuousLinearMap_apply (c : ℂ) (z : Source 2) :
    Germ.radialScaleContinuousLinearMap c z = c • z := by
  simp [Germ.radialScaleContinuousLinearMap]

/-- Radial rescaling of a plane Taylor series, normalized so that an exact
cubic first coordinate axis remains equal to `x³`. -/
@[expose] noncomputable def radiallyScaledCubicSeries
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (c : ℂ) :
    FormalMultilinearSeries ℂ (Source 2) ℂ :=
  (c ^ 3)⁻¹ •
    p.compContinuousLinearMap (Germ.radialScaleContinuousLinearMap c)

/-- Formula for each homogeneous coefficient of the normalized radial
rescaling. -/
theorem radiallyScaledCubicSeries_apply
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (c : ℂ)
    (d : ℕ) (v : Fin d → Source 2) :
    Germ.radiallyScaledCubicSeries p c d v =
      (c ^ 3)⁻¹ * c ^ d * p d v := by
  simp only [Germ.radiallyScaledCubicSeries,
    FormalMultilinearSeries.smul_apply, smul_apply,
    FormalMultilinearSeries.compContinuousLinearMap_apply]
  have hv :
      (Germ.radialScaleContinuousLinearMap c : Source 2 → Source 2) ∘ v =
        fun i ↦ c • v i := by
    funext i
    exact Germ.radialScaleContinuousLinearMap_apply c (v i)
  rw [hv]
  rw [(p d).map_smul_univ (fun _ ↦ c) v]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  ring

/-- Every mixed coefficient acquires the same radial factor in a fixed total
degree. -/
theorem mixedCoefficient_radiallyScaledCubicSeries
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (c : ℂ)
    (d i : ℕ) :
    Germ.mixedCoefficient (Germ.radiallyScaledCubicSeries p c) d i =
      (c ^ 3)⁻¹ * c ^ d * Germ.mixedCoefficient p d i := by
  simp only [Germ.mixedCoefficient,
    Germ.radiallyScaledCubicSeries_apply]
  rw [Finset.mul_sum]

/-- A nonzero normalized radial rescaling preserves the exact cubic first
coordinate axis. -/
theorem radiallyScaledCubicSeries_exact_axis
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (c : ℂ)
    (hc : c ≠ 0)
    (haxis : ∀ d, Germ.mixedCoefficient p d d =
      if d = 3 then 1 else 0) :
    ∀ d, Germ.mixedCoefficient (Germ.radiallyScaledCubicSeries p c) d d =
      if d = 3 then 1 else 0 := by
  intro d
  rw [Germ.mixedCoefficient_radiallyScaledCubicSeries, haxis]
  by_cases hd : d = 3
  · subst d
    simp [hc]
  · simp [hd]

/-- Scalar multiplication on the product Banach algebra used by functional
cubic division. -/
@[expose] noncomputable def radialAlgebraScaleContinuousLinearMap
    (c : ℂ) :
    (Germ.CubicDivisionEndomorphism × Germ.CubicDivisionEndomorphism) →L[ℂ]
      Germ.CubicDivisionEndomorphism × Germ.CubicDivisionEndomorphism :=
  c • ContinuousLinearMap.id ℂ
    (Germ.CubicDivisionEndomorphism × Germ.CubicDivisionEndomorphism)

@[simp]
theorem radialAlgebraScaleContinuousLinearMap_apply
    (c : ℂ)
    (z : Germ.CubicDivisionEndomorphism ×
      Germ.CubicDivisionEndomorphism) :
    Germ.radialAlgebraScaleContinuousLinearMap c z = c • z := by
  simp [Germ.radialAlgebraScaleContinuousLinearMap]

/-- Banach algebra extension commutes with normalized radial rescaling. -/
theorem banachAlgebraExtensionSeries_radiallyScaledCubicSeries
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (c : ℂ) :
    Germ.banachAlgebraExtensionSeries
        (A := Germ.CubicDivisionEndomorphism)
        (Germ.radiallyScaledCubicSeries p c) =
      (c ^ 3)⁻¹ •
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.CubicDivisionEndomorphism) p).compContinuousLinearMap
            (Germ.radialAlgebraScaleContinuousLinearMap c) := by
  funext d
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [FormalMultilinearSeries.smul_apply, smul_apply,
    FormalMultilinearSeries.compContinuousLinearMap_apply]
  have hv :
      (Germ.radialAlgebraScaleContinuousLinearMap c :
          (Germ.CubicDivisionEndomorphism ×
            Germ.CubicDivisionEndomorphism) →
          Germ.CubicDivisionEndomorphism ×
            Germ.CubicDivisionEndomorphism) ∘ v =
        fun i ↦ c • v i := by
    funext i
    exact Germ.radialAlgebraScaleContinuousLinearMap_apply c (v i)
  rw [hv]
  rw [(Germ.banachAlgebraExtensionSeries
    (A := Germ.CubicDivisionEndomorphism) p d).map_smul_univ
      (fun _ ↦ c) v]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [Germ.banachAlgebraExtensionSeries, sum_apply,
    Germ.mixedCoefficient_radiallyScaledCubicSeries]
  simp only [Finset.smul_sum, smul_apply, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

/-- The convergence radius after normalized radial rescaling is bounded
below by the standard radius bound for composition with the algebra scale. -/
theorem div_le_radius_banachAlgebraExtensionSeries_radiallyScaled
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (c : ℂ)
    (hc : c ≠ 0) :
    (Germ.banachAlgebraExtensionSeries
          (A := Germ.CubicDivisionEndomorphism) p).radius /
        ‖Germ.radialAlgebraScaleContinuousLinearMap c‖ₑ ≤
      (Germ.banachAlgebraExtensionSeries
        (A := Germ.CubicDivisionEndomorphism)
        (Germ.radiallyScaledCubicSeries p c)).radius := by
  rw [Germ.banachAlgebraExtensionSeries_radiallyScaledCubicSeries]
  rw [FormalMultilinearSeries.radius_smul_eq]
  · exact (Germ.banachAlgebraExtensionSeries
      (A := Germ.CubicDivisionEndomorphism) p).div_le_radius_compContinuousLinearMap
        (Germ.radialAlgebraScaleContinuousLinearMap c)
  · exact inv_ne_zero (pow_ne_zero 3 hc)

/-- A nonzero normalized radial rescaling retains positive scalar Taylor
radius. -/
theorem radiallyScaledCubicSeries_radius_pos
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (c : ℂ)
    (hp : 0 < p.radius) (hc : c ≠ 0) :
    0 < (Germ.radiallyScaledCubicSeries p c).radius := by
  rw [Germ.radiallyScaledCubicSeries,
    FormalMultilinearSeries.radius_smul_eq _ (inv_ne_zero (pow_ne_zero 3 hc))]
  refine (show 0 < p.radius /
      ‖Germ.radialScaleContinuousLinearMap c‖ₑ by
        exact ENNReal.div_pos hp.ne' enorm_ne_top).trans_le ?_
  exact p.div_le_radius_compContinuousLinearMap
    (Germ.radialScaleContinuousLinearMap c)

/-- Operator norm bound for scalar multiplication on the algebra input. -/
theorem norm_radialAlgebraScaleContinuousLinearMap_le (c : ℂ) :
    ‖Germ.radialAlgebraScaleContinuousLinearMap c‖ ≤ ‖c‖ := by
  calc
    ‖Germ.radialAlgebraScaleContinuousLinearMap c‖ ≤
        ‖c‖ * ‖ContinuousLinearMap.id ℂ
          (Germ.CubicDivisionEndomorphism ×
            Germ.CubicDivisionEndomorphism)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ = ‖c‖ := by simp

/-- Some nonzero radial scale places the base cubic division operator inside
the convergence ball of the scaled Banach algebra extension. -/
theorem exists_radialScale_cubicFunctionalInput_mem
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (hp : 0 < p.radius) :
    ∃ c : ℂ, c ≠ 0 ∧
      Germ.cubicFunctionalInput
          (0, (0 : Germ.CubicCoefficientSpace)) ∈
        Metric.eball 0
          (Germ.banachAlgebraExtensionSeries
            (A := Germ.CubicDivisionEndomorphism)
            (Germ.radiallyScaledCubicSeries p c)).radius := by
  let q := Germ.banachAlgebraExtensionSeries
    (A := Germ.CubicDivisionEndomorphism) p
  let base := Germ.cubicFunctionalInput
    (0, (0 : Germ.CubicCoefficientSpace))
  have hqRadius : 0 < q.radius :=
    Germ.banachAlgebraExtensionSeries_radius_pos p hp
  obtain ⟨delta, hdelta, hdeltaSmall⟩ :=
    ENNReal.exists_nnreal_pos_mul_lt
      (a := ((‖base‖₊ + 1 : ℝ≥0) : ℝ≥0∞))
      (b := q.radius) (by simp) hqRadius.ne'
  let c : ℂ := (delta : ℝ)
  have hc : c ≠ 0 := by
    simpa [c] using hdelta.ne'
  let scale := Germ.radialAlgebraScaleContinuousLinearMap c
  have hscaleNorm : ‖scale‖ₑ ≤ (delta : ℝ≥0∞) := by
    rw [enorm_eq_nnnorm]
    have hnorm := Germ.norm_radialAlgebraScaleContinuousLinearMap_le c
    have hcNorm : ‖c‖ = (delta : ℝ) := by simp [c]
    rw [hcNorm] at hnorm
    dsimp only [scale]
    exact_mod_cast hnorm
  have hproduct : ‖base‖ₑ * ‖scale‖ₑ < q.radius := by
    calc
      ‖base‖ₑ * ‖scale‖ₑ ≤
          (‖base‖₊ : ℝ≥0∞) * (delta : ℝ≥0∞) := by
        rw [enorm_eq_nnnorm]
        gcongr
      _ = (delta : ℝ≥0∞) * (‖base‖₊ : ℝ≥0∞) := by
        rw [mul_comm]
      _ ≤ (delta : ℝ≥0∞) *
          ((‖base‖₊ + 1 : ℝ≥0) : ℝ≥0∞) := by
        gcongr
        exact_mod_cast le_add_of_nonneg_right zero_le_one
      _ < q.radius := hdeltaSmall
  have hdiv : ‖base‖ₑ < q.radius / ‖scale‖ₑ := by
    rw [ENNReal.lt_div_iff_mul_lt]
    · exact hproduct
    · exact Or.inr enorm_ne_top
    · exact Or.inl enorm_ne_top
  have hradius : ‖base‖ₑ <
      (Germ.banachAlgebraExtensionSeries
        (A := Germ.CubicDivisionEndomorphism)
        (Germ.radiallyScaledCubicSeries p c)).radius :=
    hdiv.trans_le
      (Germ.div_le_radius_banachAlgebraExtensionSeries_radiallyScaled
        p c hc)
  refine ⟨c, hc, ?_⟩
  exact mem_eball_zero_iff.2 hradius

/-- Near the origin, the sum of the normalized scaled series is the
normalized radial pullback of the original sum. -/
theorem eventually_radiallyScaledCubicSeries_sum_eq
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (c : ℂ)
    (hp : 0 < p.radius) (hc : c ≠ 0) :
    (Germ.radiallyScaledCubicSeries p c).sum =ᶠ[nhds 0]
      fun z ↦ (c ^ 3)⁻¹ * p.sum (c • z) := by
  have hpAt : HasFPowerSeriesAt p.sum p 0 :=
    (p.hasFPowerSeriesOnBall hp).hasFPowerSeriesAt
  have hpAtImage : HasFPowerSeriesAt p.sum p
      (Germ.radialScaleContinuousLinearMap c (0 : Source 2)) := by
    simpa using hpAt
  have hcomp := hpAtImage.compContinuousLinearMap
    (u := Germ.radialScaleContinuousLinearMap c) (x := (0 : Source 2))
  have hcompZero : HasFPowerSeriesAt
      (p.sum ∘ Germ.radialScaleContinuousLinearMap c)
      (p.compContinuousLinearMap
        (Germ.radialScaleContinuousLinearMap c)) 0 := by
    simpa using hcomp
  have hnormalized : HasFPowerSeriesAt
      ((c ^ 3)⁻¹ •
        (p.sum ∘ Germ.radialScaleContinuousLinearMap c))
      ((c ^ 3)⁻¹ •
        p.compContinuousLinearMap
          (Germ.radialScaleContinuousLinearMap c)) 0 :=
    hcompZero.const_smul
  have hscaledRadius :=
    Germ.radiallyScaledCubicSeries_radius_pos p c hp hc
  have hscaled : HasFPowerSeriesAt
      (Germ.radiallyScaledCubicSeries p c).sum
      (Germ.radiallyScaledCubicSeries p c) 0 :=
    ((Germ.radiallyScaledCubicSeries p c).hasFPowerSeriesOnBall
      hscaledRadius).hasFPowerSeriesAt
  filter_upwards [hscaled.eventually_hasSum_sub,
    hnormalized.eventually_hasSum_sub] with z hzScaled hzNormalized
  have heq := hzScaled.unique hzNormalized
  simpa [Germ.radiallyScaledCubicSeries, Function.comp_def,
    Germ.radialScaleContinuousLinearMap_apply, smul_eq_mul] using heq

/-- Analytic cubic preparation of an exactly normalized scalar Taylor
series, with no convergence ball condition. -/
theorem exists_analytic_cubicPreparation
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (hp : 0 < p.radius)
    (haxis : ∀ d, Germ.mixedCoefficient p d d =
      if d = 3 then 1 else 0) :
    ∃ b₂ b₁ b₀ : ℂ → ℂ, ∃ Q : ℂ × ℂ → ℂ,
      AnalyticAt ℂ b₂ 0 ∧ AnalyticAt ℂ b₁ 0 ∧
      AnalyticAt ℂ b₀ 0 ∧
      b₂ 0 = 0 ∧ b₁ 0 = 0 ∧ b₀ 0 = 0 ∧
      AnalyticAt ℂ Q (0, 0) ∧ Q (0, 0) = 1 ∧
      ∀ᶠ z in nhds (0, 0),
        p.sum (Germ.planePoint z.1 z.2) =
          Germ.cubicDivisionPolynomialValue z.1
              (b₂ z.2) (b₁ z.2) (b₀ z.2) * Q z := by
  obtain ⟨c, hc, hbase⟩ :=
    Germ.exists_radialScale_cubicFunctionalInput_mem p hp
  let pScaled := Germ.radiallyScaledCubicSeries p c
  have hpScaled : 0 < pScaled.radius :=
    Germ.radiallyScaledCubicSeries_radius_pos p c hp hc
  have haxisScaled : ∀ d, Germ.mixedCoefficient pScaled d d =
      if d = 3 then 1 else 0 :=
    Germ.radiallyScaledCubicSeries_exact_axis p c hc haxis
  obtain ⟨a, QScaled, ha, haZero, hQScaled, hQScaledZero,
      hfactorScaled⟩ :=
    Germ.exists_analytic_cubicPreparation_of_base_mem
      pScaled hpScaled haxisScaled hbase
  let inverseScalar : ℂ → ℂ := fun y ↦ c⁻¹ * y
  let inversePair : ℂ × ℂ → ℂ × ℂ := fun z ↦
    (inverseScalar z.1, inverseScalar z.2)
  let b₂ : ℂ → ℂ := fun y ↦ c * a (inverseScalar y) 2
  let b₁ : ℂ → ℂ := fun y ↦ c ^ 2 * a (inverseScalar y) 1
  let b₀ : ℂ → ℂ := fun y ↦ c ^ 3 * a (inverseScalar y) 0
  let Q : ℂ × ℂ → ℂ := fun z ↦ QScaled (inversePair z)
  have hinverseScalar : AnalyticAt ℂ inverseScalar 0 := by
    dsimp only [inverseScalar]
    fun_prop
  have haAtInverseZero : AnalyticAt ℂ a (inverseScalar 0) := by
    simpa [inverseScalar] using ha
  have haComp : AnalyticAt ℂ (fun y ↦ a (inverseScalar y)) 0 := by
    simpa [Function.comp_def] using
      (AnalyticAt.comp (x := 0) haAtInverseZero hinverseScalar)
  have haCoordinate (i : Fin 3) : AnalyticAt ℂ
      (fun y ↦ a (inverseScalar y) i) 0 := by
    simpa [Function.comp_def] using
      (AnalyticAt.comp (x := 0)
        ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt
          (a (inverseScalar 0))) haComp)
  have hb₂ : AnalyticAt ℂ b₂ 0 := by
    exact analyticAt_const.mul (haCoordinate 2)
  have hb₁ : AnalyticAt ℂ b₁ 0 := by
    exact analyticAt_const.mul (haCoordinate 1)
  have hb₀ : AnalyticAt ℂ b₀ 0 := by
    exact analyticAt_const.mul (haCoordinate 0)
  have hb₂Zero : b₂ 0 = 0 := by simp [b₂, inverseScalar, haZero]
  have hb₁Zero : b₁ 0 = 0 := by simp [b₁, inverseScalar, haZero]
  have hb₀Zero : b₀ 0 = 0 := by simp [b₀, inverseScalar, haZero]
  have hinversePair : AnalyticAt ℂ inversePair (0, 0) := by
    exact hinverseScalar.comp (x := (0, 0)) analyticAt_fst |>.prod
      (hinverseScalar.comp (x := (0, 0)) analyticAt_snd)
  have hinversePairZero : inversePair (0, 0) = (0, 0) := by
    simp [inversePair, inverseScalar]
  have hQScaledAt : AnalyticAt ℂ QScaled (inversePair (0, 0)) := by
    simpa [hinversePairZero] using hQScaled
  have hQ : AnalyticAt ℂ Q (0, 0) := by
    simpa [Q, Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0)) hQScaledAt hinversePair)
  have hQZero : Q (0, 0) = 1 := by
    simpa [Q, inversePair, inverseScalar] using hQScaledZero
  have hsumScaled :=
    Germ.eventually_radiallyScaledCubicSeries_sum_eq p c hp hc
  have hplaneTendsto : Tendsto
      (fun z : ℂ × ℂ ↦ Germ.planePoint z.1 z.2)
      (nhds (0, 0)) (nhds 0) := by
    have hfun : (fun z : ℂ × ℂ ↦ Germ.planePoint z.1 z.2) =
        (Germ.planePointContinuousLinearMap : ℂ × ℂ → Source 2) := by
      funext z
      exact (Germ.planePointContinuousLinearMap_apply z).symm
    rw [hfun]
    have hclm :=
      Germ.planePointContinuousLinearMap.continuous.continuousAt
        (x := ((0, 0) : ℂ × ℂ))
    have hzero : Germ.planePointContinuousLinearMap
        ((0, 0) : ℂ × ℂ) = 0 :=
      map_zero Germ.planePointContinuousLinearMap
    rw [← hzero]
    exact hclm
  have hsumPair : ∀ᶠ z : ℂ × ℂ in nhds (0, 0),
      pScaled.sum (Germ.planePoint z.1 z.2) =
        (c ^ 3)⁻¹ * p.sum (c • Germ.planePoint z.1 z.2) :=
    hplaneTendsto.eventually hsumScaled
  have hsumPairAt : ∀ᶠ z : ℂ × ℂ in nhds (inversePair (0, 0)),
      pScaled.sum (Germ.planePoint z.1 z.2) =
        (c ^ 3)⁻¹ * p.sum (c • Germ.planePoint z.1 z.2) := by
    simpa [hinversePairZero] using hsumPair
  have hfactorScaledAt : ∀ᶠ z : ℂ × ℂ in
      nhds (inversePair (0, 0)),
      pScaled.sum (Germ.planePoint z.1 z.2) =
        Germ.cubicDivisionPolynomialValue z.1
            (a z.2 2) (a z.2 1) (a z.2 0) * QScaled z := by
    simpa [hinversePairZero] using hfactorScaled
  have hsumAtInverse :=
    hinversePair.continuousAt.eventually hsumPairAt
  have hfactorAtInverse :=
    hinversePair.continuousAt.eventually hfactorScaledAt
  refine ⟨b₂, b₁, b₀, Q, hb₂, hb₁, hb₀,
    hb₂Zero, hb₁Zero, hb₀Zero, hQ, hQZero, ?_⟩
  filter_upwards [hsumAtInverse, hfactorAtInverse] with z hsum hfactor
  have hscaled : (c ^ 3)⁻¹ *
      p.sum (Germ.planePoint z.1 z.2) =
        Germ.cubicDivisionPolynomialValue (inverseScalar z.1)
            (a (inverseScalar z.2) 2) (a (inverseScalar z.2) 1)
            (a (inverseScalar z.2) 0) * QScaled (inversePair z) := by
    rw [← hfactor]
    rw [hsum]
    congr 2
    ext i
    fin_cases i
    · simp [inversePair, inverseScalar, Germ.planePoint, hc]
    · simp [inversePair, inverseScalar, Germ.planePoint, hc]
  calc
    p.sum (Germ.planePoint z.1 z.2) =
        c ^ 3 * ((c ^ 3)⁻¹ *
          p.sum (Germ.planePoint z.1 z.2)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 hc), one_mul]
    _ = c ^ 3 *
        (Germ.cubicDivisionPolynomialValue (inverseScalar z.1)
            (a (inverseScalar z.2) 2) (a (inverseScalar z.2) 1)
            (a (inverseScalar z.2) 0) * QScaled (inversePair z)) := by
      rw [hscaled]
    _ = Germ.cubicDivisionPolynomialValue z.1
          (b₂ z.2) (b₁ z.2) (b₀ z.2) * Q z := by
      dsimp only [Germ.cubicDivisionPolynomialValue, inverseScalar,
        inversePair, b₂, b₁, b₀, Q]
      field_simp [hc]

/-- The polynomial attached to three one variable coefficient germs. -/
@[expose] noncomputable def cubicWeierstrassPolynomial
    (a₂ a₁ a₀ : Germ 1) : Polynomial (Germ 1) :=
  Polynomial.monomial 3 1 + Polynomial.monomial 2 a₂ +
    Polynomial.monomial 1 a₁ + Polynomial.monomial 0 a₀

/-- Evaluation of the cubic polynomial is the corresponding plane cubic
germ. -/
theorem firstCoordinatePolynomialEvaluation_cubicWeierstrassPolynomial
    (a₂ a₁ a₀ : Germ 1) :
    Germ.firstCoordinatePolynomialEvaluation
        (Germ.cubicWeierstrassPolynomial a₂ a₁ a₀) =
      Germ.monicCubic a₂ a₁ a₀ := by
  rw [Germ.firstCoordinatePolynomialEvaluation]
  simp only [Germ.cubicWeierstrassPolynomial, Polynomial.eval₂_add,
    Polynomial.eval₂_monomial, map_one, pow_zero, pow_one, one_mul]
  rw [Germ.monicCubic]
  simp only [Germ.planeCoefficientExtension_apply]
  ring

theorem cubicWeierstrassPolynomial_natDegree
    (a₂ a₁ a₀ : Germ 1) :
    (Germ.cubicWeierstrassPolynomial a₂ a₁ a₀).natDegree = 3 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    simp only [Germ.cubicWeierstrassPolynomial,
      Polynomial.coeff_add, Polynomial.coeff_monomial]
    simp [show 3 ≠ k by omega, show 2 ≠ k by omega,
      show 1 ≠ k by omega, show 0 ≠ k by omega]
  · simp only [Germ.cubicWeierstrassPolynomial,
      Polynomial.coeff_add, Polynomial.coeff_monomial]
    norm_num

/-- The cubic Weierstrass polynomial is monic of degree three. -/
theorem cubicWeierstrassPolynomial_monic
    (a₂ a₁ a₀ : Germ 1) :
    (Germ.cubicWeierstrassPolynomial a₂ a₁ a₀).Monic := by
  change (Germ.cubicWeierstrassPolynomial a₂ a₁ a₀).coeff
      (Germ.cubicWeierstrassPolynomial a₂ a₁ a₀).natDegree = 1
  rw [Germ.cubicWeierstrassPolynomial_natDegree]
  simp only [Germ.cubicWeierstrassPolynomial,
    Polynomial.coeff_add, Polynomial.coeff_monomial]
  norm_num

/-- The three lower coefficients of the cubic polynomial are the supplied
coefficient germs. -/
theorem cubicWeierstrassPolynomial_coeff_of_lt
    (a₂ a₁ a₀ : Germ 1) (k : ℕ) (hk : k < 3) :
    (Germ.cubicWeierstrassPolynomial a₂ a₁ a₀).coeff k =
      if k = 2 then a₂ else if k = 1 then a₁ else a₀ := by
  interval_cases k <;>
    simp [Germ.cubicWeierstrassPolynomial,
      Polynomial.coeff_add, Polynomial.coeff_monomial]

/-- Vanishing of the three coefficient germs at the origin makes the cubic
polynomial distinguished. -/
theorem cubicWeierstrassPolynomial_coeff_mem_maximalIdeal
    {a₂ a₁ a₀ : Germ 1}
    (ha₂ : a₂ ∈ Germ.maximalIdeal 1)
    (ha₁ : a₁ ∈ Germ.maximalIdeal 1)
    (ha₀ : a₀ ∈ Germ.maximalIdeal 1) :
    ∀ k, k < 3 →
      (Germ.cubicWeierstrassPolynomial a₂ a₁ a₀).coeff k ∈
        Germ.maximalIdeal 1 := by
  intro k hk
  rw [Germ.cubicWeierstrassPolynomial_coeff_of_lt a₂ a₁ a₀ k hk]
  split_ifs <;> assumption

/-- Every monic cubic is recovered from its three lower coefficients. -/
theorem cubicWeierstrassPolynomial_coefficients
    (P : Polynomial (Germ 1)) (hPMonic : P.Monic)
    (hPDegree : P.natDegree = 3) :
    Germ.cubicWeierstrassPolynomial
        (P.coeff 2) (P.coeff 1) (P.coeff 0) = P := by
  apply Polynomial.ext
  intro k
  by_cases hk : k ≤ 3
  · interval_cases k
    · simp [Germ.cubicWeierstrassPolynomial]
    · simp [Germ.cubicWeierstrassPolynomial,
        Polynomial.coeff_add, Polynomial.coeff_monomial]
    · simp [Germ.cubicWeierstrassPolynomial,
        Polynomial.coeff_add, Polynomial.coeff_monomial]
    · have hcoeffThree : P.coeff 3 = 1 := by
        have hleading := hPMonic
        change P.coeff P.natDegree = 1 at hleading
        simpa [hPDegree] using hleading
      simp [Germ.cubicWeierstrassPolynomial,
        Polynomial.coeff_add, Polynomial.coeff_monomial, hcoeffThree]
  · have hkLarge : P.natDegree < k := by omega
    have hPZero := Polynomial.coeff_eq_zero_of_natDegree_lt hkLarge
    simp only [Germ.cubicWeierstrassPolynomial,
      Polynomial.coeff_add, Polynomial.coeff_monomial]
    simp [show 3 ≠ k by omega, show 2 ≠ k by omega,
      show 1 ≠ k by omega, show 0 ≠ k by omega, hPZero]

/-- An analytic function with an exactly cubic first coordinate axis admits
a cubic Weierstrass factorization as an analytic germ. -/
theorem hasAnalyticWeierstrassFactorizationOfOrder_three_of_exact_axis_series
    (F : Source 2 → ℂ)
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (hp : HasFPowerSeriesAt F p 0)
    (haxis : ∀ d, Germ.mixedCoefficient p d d =
      if d = 3 then 1 else 0) :
    Germ.HasAnalyticWeierstrassFactorizationOfOrder
      (Germ.ofFunction F hp.analyticAt) 3 := by
  obtain ⟨b₂, b₁, b₀, Q, hb₂, hb₁, hb₀,
      hb₂Zero, hb₁Zero, hb₀Zero, hQ, hQZero, hfactor⟩ :=
    Germ.exists_analytic_cubicPreparation p hp.radius_pos haxis
  have hb₂Source : AnalyticAt ℂ
      (fun y : Source 1 ↦ b₂ (y 0)) 0 := by
    have hprojection : AnalyticAt ℂ
        (fun y : Source 1 ↦ y 0) 0 :=
      (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 1 ↦ ℂ) (0 : Fin 1)).analyticAt 0
    have hb₂At : AnalyticAt ℂ b₂ ((0 : Source 1) 0) := by
      simpa using hb₂
    exact AnalyticAt.fun_comp
      (f := fun y : Source 1 ↦ y 0) hb₂At hprojection
  have hb₁Source : AnalyticAt ℂ
      (fun y : Source 1 ↦ b₁ (y 0)) 0 := by
    have hprojection : AnalyticAt ℂ
        (fun y : Source 1 ↦ y 0) 0 :=
      (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 1 ↦ ℂ) (0 : Fin 1)).analyticAt 0
    have hb₁At : AnalyticAt ℂ b₁ ((0 : Source 1) 0) := by
      simpa using hb₁
    exact AnalyticAt.fun_comp
      (f := fun y : Source 1 ↦ y 0) hb₁At hprojection
  have hb₀Source : AnalyticAt ℂ
      (fun y : Source 1 ↦ b₀ (y 0)) 0 := by
    have hprojection : AnalyticAt ℂ
        (fun y : Source 1 ↦ y 0) 0 :=
      (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 1 ↦ ℂ) (0 : Fin 1)).analyticAt 0
    have hb₀At : AnalyticAt ℂ b₀ ((0 : Source 1) 0) := by
      simpa using hb₀
    exact AnalyticAt.fun_comp
      (f := fun y : Source 1 ↦ y 0) hb₀At hprojection
  have hQSource : AnalyticAt ℂ
      (fun z : Source 2 ↦ Q (z 0, z 1)) 0 := by
    have hfirst : AnalyticAt ℂ (fun z : Source 2 ↦ z 0) 0 :=
      (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) (0 : Fin 2)).analyticAt 0
    have hsecond : AnalyticAt ℂ (fun z : Source 2 ↦ z 1) 0 :=
      (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0
    have hpair : AnalyticAt ℂ (fun z : Source 2 ↦ (z 0, z 1)) 0 :=
      hfirst.prod hsecond
    have hQAt : AnalyticAt ℂ Q
        (((0 : Source 2) 0), ((0 : Source 2) 1)) := by
      simpa using hQ
    exact AnalyticAt.fun_comp
      (f := fun z : Source 2 ↦ (z 0, z 1)) hQAt hpair
  let a₂ : Germ 1 := Germ.ofFunction
    (fun y : Source 1 ↦ b₂ (y 0)) hb₂Source
  let a₁ : Germ 1 := Germ.ofFunction
    (fun y : Source 1 ↦ b₁ (y 0)) hb₁Source
  let a₀ : Germ 1 := Germ.ofFunction
    (fun y : Source 1 ↦ b₀ (y 0)) hb₀Source
  let u : Germ 2 := Germ.ofFunction
    (fun z : Source 2 ↦ Q (z 0, z 1)) hQSource
  have ha₂ : a₂ ∈ Germ.maximalIdeal 1 := by
    rw [Germ.mem_maximalIdeal_iff]
    simp [a₂, Germ.valueRingHom_ofFunction, hb₂Zero]
  have ha₁ : a₁ ∈ Germ.maximalIdeal 1 := by
    rw [Germ.mem_maximalIdeal_iff]
    simp [a₁, Germ.valueRingHom_ofFunction, hb₁Zero]
  have ha₀ : a₀ ∈ Germ.maximalIdeal 1 := by
    rw [Germ.mem_maximalIdeal_iff]
    simp [a₀, Germ.valueRingHom_ofFunction, hb₀Zero]
  have hu : IsUnit u := by
    apply Germ.isUnit_of_valueRingHom_ne_zero
    rw [Germ.valueRingHom_ofFunction]
    intro hzero
    rw [show Q ((0 : Source 2) 0, (0 : Source 2) 1) = 1 by
      simpa using hQZero] at hzero
    exact one_ne_zero hzero
  let coordinatePair : Source 2 → ℂ × ℂ :=
    ContinuousLinearEquiv.finTwoArrow ℂ ℂ
  have hcoordinatePair : Tendsto coordinatePair
      (nhds 0) (nhds (0, 0)) := by
    change Tendsto coordinatePair (nhds 0) (nhds (0 : ℂ × ℂ))
    have hcontinuous :=
      (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).continuous.continuousAt
        (x := (0 : Source 2))
    simpa only [ContinuousAt, coordinatePair, map_zero] using hcontinuous
  have hfactorSource := hcoordinatePair.eventually hfactor
  have hpSum : HasFPowerSeriesAt p.sum p 0 :=
    (p.hasFPowerSeriesOnBall hp.radius_pos).hasFPowerSeriesAt
  have hsum : F =ᶠ[nhds 0] p.sum := by
    filter_upwards [hp.eventually_hasSum_sub,
      hpSum.eventually_hasSum_sub] with z hzF hzSum
    simpa only [sub_zero] using hzF.unique hzSum
  have heq : Germ.ofFunction F hp.analyticAt =
      Germ.monicCubic a₂ a₁ a₀ * u := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hsum, hfactorSource] with z hzSum hzFactor
    change F z =
      (z 0 ^ 3 + b₂ (z 1) * z 0 ^ 2 +
        b₁ (z 1) * z 0 + b₀ (z 1)) * Q (z 0, z 1)
    rw [hzSum]
    simpa only [coordinatePair,
      ContinuousLinearEquiv.finTwoArrow_apply,
      Germ.planePoint_coordinates,
      Germ.cubicDivisionPolynomialValue] using hzFactor
  let P := Germ.cubicWeierstrassPolynomial a₂ a₁ a₀
  refine ⟨P, u, Germ.cubicWeierstrassPolynomial_monic a₂ a₁ a₀,
    Germ.cubicWeierstrassPolynomial_natDegree a₂ a₁ a₀,
    Germ.cubicWeierstrassPolynomial_coeff_mem_maximalIdeal ha₂ ha₁ ha₀,
    hu, ?_⟩
  rw [Germ.firstCoordinatePolynomialEvaluation_cubicWeierstrassPolynomial]
  exact heq

/-- On the first coordinate axis, a regular germ is its regular power times
the restriction of the corresponding analytic quotient. -/
theorem lineRestriction_eq_pow_mul_tailIterate_of_regular
    {d : ℕ} {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f d) :
    Germ.lineRestriction (Germ.firstCoordinateVector 1) f =
      Germ.coordinate (0 : Fin 1) ^ d *
        Germ.lineRestriction (Germ.firstCoordinateVector 1)
          (Germ.firstCoordinateTailIterate d f) := by
  have hexpansion := congrArg
    (Germ.lineRestrictionAlgHom (Germ.firstCoordinateVector 1))
    (Germ.firstCoordinate_finite_expansion (d := d) f)
  simp only [map_add, map_mul, map_pow, map_sum,
    Germ.lineRestrictionAlgHom_apply,
    Germ.lineRestriction_firstCoordinate,
    Germ.lineRestriction_hyperplaneExtension_firstCoordinate] at hexpansion
  have hsum : ∑ k ∈ Finset.range d,
      Germ.coordinate (0 : Fin 1) ^ k *
        Germ.constRingHom 1
          (Germ.valueRingHom 1
            (Germ.firstCoordinateTaylorCoefficient k f)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hklt : k < d := Finset.mem_range.mp hk
    rw [(Germ.isRegularInFirstCoordinateOfOrder_iff.mp hregular).2 k hklt]
    simp
  calc
    Germ.lineRestriction (Germ.firstCoordinateVector 1) f =
        (∑ k ∈ Finset.range d,
          Germ.coordinate (0 : Fin 1) ^ k *
            Germ.constRingHom 1
              (Germ.valueRingHom 1
                (Germ.firstCoordinateTaylorCoefficient k f))) +
          Germ.coordinate (0 : Fin 1) ^ d *
            Germ.lineRestriction (Germ.firstCoordinateVector 1)
              (Germ.firstCoordinateTailIterate d f) := hexpansion
    _ = Germ.coordinate (0 : Fin 1) ^ d *
          Germ.lineRestriction (Germ.firstCoordinateVector 1)
            (Germ.firstCoordinateTailIterate d f) := by
      rw [hsum, zero_add]

/-- Analytic Weierstrass preparation holds for every plane analytic germ
that is regular of order three in the first coordinate. -/
theorem hasAnalyticWeierstrassFactorizationOfOrder_three
    {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f 3) :
    Germ.HasAnalyticWeierstrassFactorizationOfOrder f 3 := by
  let v : Germ 2 := Germ.firstCoordinateTailIterate 3 f
  have hv : IsUnit v :=
    Germ.isUnit_firstCoordinateTailIterate_of_regular hregular
  let s : Germ 2 := (↑(hv.unit⁻¹) : Germ 2)
  have hs : IsUnit s := Units.isUnit hv.unit⁻¹
  have hvs : v * s = 1 := by
    calc
      v * s = (↑hv.unit : Germ 2) * (↑(hv.unit⁻¹) : Germ 2) := by
        rw [hv.unit_spec]
      _ = 1 := Units.mul_inv hv.unit
  let g : Germ 2 := f * s
  have hlineF : Germ.lineRestriction
      (Germ.firstCoordinateVector 1) f =
        Germ.coordinate (0 : Fin 1) ^ 3 *
          Germ.lineRestriction (Germ.firstCoordinateVector 1) v := by
    simpa only [v] using
      Germ.lineRestriction_eq_pow_mul_tailIterate_of_regular hregular
  have hlineG : Germ.lineRestriction
      (Germ.firstCoordinateVector 1) g =
        Germ.coordinate (0 : Fin 1) ^ 3 := by
    change Germ.lineRestriction (Germ.firstCoordinateVector 1) (f * s) = _
    change (Germ.lineRestrictionAlgHom
        (Germ.firstCoordinateVector 1)) (f * s) = _
    rw [map_mul, Germ.lineRestrictionAlgHom_apply,
      Germ.lineRestrictionAlgHom_apply, hlineF, mul_assoc,
      ← map_mul, hvs, map_one, mul_one]
  obtain ⟨F, hF, hg⟩ := Germ.exists_analyticRepresentative g
  rcases hF with ⟨p, hp⟩
  have hlineRepresentative : Germ.lineRestriction
      (Germ.firstCoordinateVector 1)
        (Germ.ofFunction F hp.analyticAt) =
      Germ.coordinate (0 : Fin 1) ^ 3 := by
    rw [← hg]
    exact hlineG
  have haxisTaylor : Germ.firstCoordinateAxisTaylorSeries
      (Germ.ofFunction F hp.analyticAt) =
        (PowerSeries.X : PowerSeries ℂ) ^ 3 := by
    rw [Germ.firstCoordinateAxisTaylorSeries,
      hlineRepresentative]
    change Germ.oneVariableTaylorRingHom
        (Germ.coordinate (0 : Fin 1) ^ 3) = _
    rw [map_pow, Germ.oneVariableTaylorRingHom_apply,
      Germ.oneVariableTaylorSeries_coordinate]
  have haxis : ∀ d,
      Germ.mixedCoefficient p d d =
        if d = 3 then 1 else 0 := by
    intro d
    rw [Germ.mixedCoefficient_self_eq_value_firstCoordinateTaylorCoefficient
      hp d]
    rw [← Germ.firstCoordinateAxisTaylorSeries_coeff,
      haxisTaylor]
    simp [PowerSeries.coeff_X_pow]
  have hgPreparation : Germ.HasAnalyticWeierstrassFactorizationOfOrder
      g 3 := by
    rw [hg]
    exact
      Germ.hasAnalyticWeierstrassFactorizationOfOrder_three_of_exact_axis_series
        F p hp haxis
  obtain ⟨P, w, hPMonic, hPDegree, hPCoeff, hw, hgw⟩ :=
    hgPreparation
  let t : Germ 2 := (↑(hs.unit⁻¹) : Germ 2)
  have ht : IsUnit t := Units.isUnit hs.unit⁻¹
  have hst : s * t = 1 := by
    calc
      s * t = (↑hs.unit : Germ 2) * (↑(hs.unit⁻¹) : Germ 2) := by
        rw [hs.unit_spec]
      _ = 1 := Units.mul_inv hs.unit
  refine ⟨P, w * t, hPMonic, hPDegree, hPCoeff, hw.mul ht, ?_⟩
  calc
    f = f * (s * t) := by rw [hst, mul_one]
    _ = g * t := by
      change f * (s * t) = (f * s) * t
      rw [mul_assoc]
    _ = (Germ.firstCoordinatePolynomialEvaluation P * w) * t := by
      rw [hgw]
    _ = Germ.firstCoordinatePolynomialEvaluation P * (w * t) := by
      rw [mul_assoc]

/-- Every order three regular germ has a parameter preserving analytic
coordinate transformation whose prepared factor has depressed cubic form. -/
theorem exists_parameterPreserving_depressedCubicPreparation
    {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f 3) :
    ∃ e : PointedEquivGerm 2, ∃ a₁ a₀ : Germ 1, ∃ u : Germ 2,
      a₁ ∈ Germ.maximalIdeal 1 ∧
      a₀ ∈ Germ.maximalIdeal 1 ∧
      IsUnit u ∧
      e.pullbackAlgEquiv f =
        (Germ.coordinate (0 : Fin 2) ^ 3 +
          Germ.planeCoefficientExtension a₁ *
            Germ.coordinate (0 : Fin 2) +
          Germ.planeCoefficientExtension a₀) * u ∧
      ∀ q : Germ 1,
        e.pullbackAlgEquiv (Germ.planeCoefficientExtension q) =
          Germ.planeCoefficientExtension q := by
  obtain ⟨P, w, hPMonic, hPDegree, hPCoeff, hw, hfactor⟩ :=
    Germ.hasAnalyticWeierstrassFactorizationOfOrder_three hregular
  let a₂ : Germ 1 := P.coeff 2
  let a₁ : Germ 1 := P.coeff 1
  let a₀ : Germ 1 := P.coeff 0
  have ha₂ : a₂ ∈ Germ.maximalIdeal 1 :=
    hPCoeff 2 (by omega)
  have ha₁ : a₁ ∈ Germ.maximalIdeal 1 :=
    hPCoeff 1 (by omega)
  have ha₀ : a₀ ∈ Germ.maximalIdeal 1 :=
    hPCoeff 0 (by omega)
  have hPForm : Germ.cubicWeierstrassPolynomial a₂ a₁ a₀ = P := by
    exact Germ.cubicWeierstrassPolynomial_coefficients
      P hPMonic hPDegree
  have hEvaluation : Germ.firstCoordinatePolynomialEvaluation P =
      Germ.monicCubic a₂ a₁ a₀ := by
    rw [← hPForm]
    exact Germ.firstCoordinatePolynomialEvaluation_cubicWeierstrassPolynomial
      a₂ a₁ a₀
  have hfCubic : f = Germ.monicCubic a₂ a₁ a₀ * w := by
    rw [← hEvaluation]
    exact hfactor
  obtain ⟨e, heDepressed, heParameter⟩ :=
    Germ.exists_cubic_tschirnhausen a₂ a₁ a₀ ha₂
  let b₁ : Germ 1 := Germ.depressedCubicLinear a₂ a₁
  let b₀ : Germ 1 := Germ.depressedCubicConstant a₂ a₁ a₀
  have ha₂Square : a₂ ^ 2 ∈ Germ.maximalIdeal 1 := by
    simpa [pow_two] using
      (Germ.maximalIdeal 1).mul_mem_left a₂ ha₂
  have ha₂Cube : a₂ ^ 3 ∈ Germ.maximalIdeal 1 := by
    rw [show a₂ ^ 3 = a₂ ^ 2 * a₂ by ring]
    exact (Germ.maximalIdeal 1).mul_mem_left (a₂ ^ 2) ha₂
  have ha₁a₂ : a₁ * a₂ ∈ Germ.maximalIdeal 1 :=
    (Germ.maximalIdeal 1).mul_mem_left a₁ ha₂
  have hb₁ : b₁ ∈ Germ.maximalIdeal 1 := by
    exact (Germ.maximalIdeal 1).sub_mem ha₁
      ((Germ.maximalIdeal 1).smul_mem _ ha₂Square)
  have hb₀ : b₀ ∈ Germ.maximalIdeal 1 := by
    exact (Germ.maximalIdeal 1).add_mem
      ((Germ.maximalIdeal 1).sub_mem ha₀
        ((Germ.maximalIdeal 1).smul_mem _ ha₁a₂))
      ((Germ.maximalIdeal 1).smul_mem _ ha₂Cube)
  let u : Germ 2 := e.pullbackAlgEquiv w
  have hu : IsUnit u := hw.map e.pullbackAlgEquiv
  refine ⟨e, b₁, b₀, u, hb₁, hb₀, hu, ?_, heParameter⟩
  rw [hfCubic, map_mul, heDepressed]

/-- The completed image closure condition holds in order three. -/
theorem completedWeierstrassImageClosureAtOrder_three :
    Germ.CompletedWeierstrassImageClosureAtOrder 3 :=
  (Germ.completedWeierstrassImageClosureAtOrder_iff 3).2
    fun _f hregular ↦
      Germ.hasAnalyticWeierstrassFactorizationOfOrder_three hregular

end Germ

end OnLeConjecture.Analytic
