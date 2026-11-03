/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GeneralFunctionalPreparation
public import OnLeConjecture.Analytic.CoordinateJetOrder
public import OnLeConjecture.Analytic.OrderThreeReduction

/-!
# Analytic Weierstrass preparation in every positive order

Degree dependent radial rescaling places the finite division state in the
convergence ball of the Banach algebra Taylor extension. The general
functional preparation theorem then produces the lower coefficients and an
analytic unit.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Metric
open scoped BigOperators NNReal ENNReal Topology

namespace Germ

/-- Scalar multiplication on the two dimensional source. -/
@[expose] noncomputable def generalRadialScaleContinuousLinearMap (c : ℂ) :
    Source 2 →L[ℂ] Source 2 :=
  c • ContinuousLinearMap.id ℂ (Source 2)

@[simp]
theorem generalRadialScaleContinuousLinearMap_apply
    (c : ℂ) (z : Source 2) :
    Germ.generalRadialScaleContinuousLinearMap c z = c • z := by
  simp [Germ.generalRadialScaleContinuousLinearMap]

/-- Radial rescaling normalized so that a first coordinate axis of degree
`d + 1` remains monic. -/
@[expose] noncomputable def radiallyScaledGeneralSeries
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (d : ℕ) (c : ℂ) :
    FormalMultilinearSeries ℂ (Source 2) ℂ :=
  (c ^ (d + 1))⁻¹ •
    p.compContinuousLinearMap
      (Germ.generalRadialScaleContinuousLinearMap c)

/-- Formula for each homogeneous coefficient of the normalized radial
rescaling. -/
theorem radiallyScaledGeneralSeries_apply
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (d : ℕ) (c : ℂ) (n : ℕ) (v : Fin n → Source 2) :
    Germ.radiallyScaledGeneralSeries p d c n v =
      (c ^ (d + 1))⁻¹ * c ^ n * p n v := by
  simp only [Germ.radiallyScaledGeneralSeries,
    FormalMultilinearSeries.smul_apply, smul_apply,
    FormalMultilinearSeries.compContinuousLinearMap_apply]
  have hv :
      (Germ.generalRadialScaleContinuousLinearMap c :
        Source 2 → Source 2) ∘ v = fun i ↦ c • v i := by
    funext i
    exact Germ.generalRadialScaleContinuousLinearMap_apply c (v i)
  rw [hv]
  rw [(p n).map_smul_univ (fun _ ↦ c) v]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  ring

/-- Every mixed coefficient acquires the same radial factor in a fixed total
degree. -/
theorem mixedCoefficient_radiallyScaledGeneralSeries
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (d : ℕ) (c : ℂ) (n i : ℕ) :
    Germ.mixedCoefficient (Germ.radiallyScaledGeneralSeries p d c) n i =
      (c ^ (d + 1))⁻¹ * c ^ n * Germ.mixedCoefficient p n i := by
  simp only [Germ.mixedCoefficient,
    Germ.radiallyScaledGeneralSeries_apply]
  rw [Finset.mul_sum]

/-- A nonzero normalized radial rescaling preserves the exact monic first
coordinate axis. -/
theorem radiallyScaledGeneralSeries_exact_axis
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (d : ℕ) (c : ℂ) (hc : c ≠ 0)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0) :
    ∀ n, Germ.mixedCoefficient
        (Germ.radiallyScaledGeneralSeries p d c) n n =
      if n = d + 1 then 1 else 0 := by
  intro n
  rw [Germ.mixedCoefficient_radiallyScaledGeneralSeries, haxis]
  by_cases hn : n = d + 1
  · subst n
    simp [hc]
  · simp [hn]

/-- Scalar multiplication on the product Banach algebra used by the general
functional division. -/
@[expose] noncomputable def generalRadialAlgebraScaleContinuousLinearMap
    (d : ℕ) (c : ℂ) :
    (Germ.GeneralDivisionEndomorphism d ×
      Germ.GeneralDivisionEndomorphism d) →L[ℂ]
    (Germ.GeneralDivisionEndomorphism d ×
      Germ.GeneralDivisionEndomorphism d) :=
  c • ContinuousLinearMap.id ℂ
    (Germ.GeneralDivisionEndomorphism d ×
      Germ.GeneralDivisionEndomorphism d)

@[simp]
theorem generalRadialAlgebraScaleContinuousLinearMap_apply
    (d : ℕ) (c : ℂ)
    (z : Germ.GeneralDivisionEndomorphism d ×
      Germ.GeneralDivisionEndomorphism d) :
    Germ.generalRadialAlgebraScaleContinuousLinearMap d c z = c • z := by
  simp [Germ.generalRadialAlgebraScaleContinuousLinearMap]

/-- Banach algebra extension commutes with normalized radial rescaling. -/
theorem banachAlgebraExtensionSeries_radiallyScaledGeneralSeries
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (d : ℕ) (c : ℂ) :
    Germ.banachAlgebraExtensionSeries
        (A := Germ.GeneralDivisionEndomorphism d)
        (Germ.radiallyScaledGeneralSeries p d c) =
      (c ^ (d + 1))⁻¹ •
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).compContinuousLinearMap
            (Germ.generalRadialAlgebraScaleContinuousLinearMap d c) := by
  funext n
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [FormalMultilinearSeries.smul_apply, smul_apply,
    FormalMultilinearSeries.compContinuousLinearMap_apply]
  have hv :
      (Germ.generalRadialAlgebraScaleContinuousLinearMap d c :
          (Germ.GeneralDivisionEndomorphism d ×
            Germ.GeneralDivisionEndomorphism d) →
          Germ.GeneralDivisionEndomorphism d ×
            Germ.GeneralDivisionEndomorphism d) ∘ v =
        fun i ↦ c • v i := by
    funext i
    exact Germ.generalRadialAlgebraScaleContinuousLinearMap_apply d c (v i)
  rw [hv]
  rw [(Germ.banachAlgebraExtensionSeries
    (A := Germ.GeneralDivisionEndomorphism d) p n).map_smul_univ
      (fun _ ↦ c) v]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [Germ.banachAlgebraExtensionSeries, sum_apply,
    Germ.mixedCoefficient_radiallyScaledGeneralSeries]
  simp only [Finset.smul_sum, smul_apply, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

/-- The scaled extension radius is bounded below by the standard composition
radius bound. -/
theorem div_le_radius_banachAlgebraExtensionSeries_radiallyScaledGeneral
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (d : ℕ) (c : ℂ) (hc : c ≠ 0) :
    (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius /
        ‖Germ.generalRadialAlgebraScaleContinuousLinearMap d c‖ₑ ≤
      (Germ.banachAlgebraExtensionSeries
        (A := Germ.GeneralDivisionEndomorphism d)
        (Germ.radiallyScaledGeneralSeries p d c)).radius := by
  rw [Germ.banachAlgebraExtensionSeries_radiallyScaledGeneralSeries]
  rw [FormalMultilinearSeries.radius_smul_eq]
  · exact (Germ.banachAlgebraExtensionSeries
      (A := Germ.GeneralDivisionEndomorphism d) p).div_le_radius_compContinuousLinearMap
        (Germ.generalRadialAlgebraScaleContinuousLinearMap d c)
  · exact inv_ne_zero (pow_ne_zero (d + 1) hc)

/-- A nonzero normalized radial rescaling retains positive scalar Taylor
radius. -/
theorem radiallyScaledGeneralSeries_radius_pos
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (d : ℕ) (c : ℂ) (hp : 0 < p.radius) (hc : c ≠ 0) :
    0 < (Germ.radiallyScaledGeneralSeries p d c).radius := by
  rw [Germ.radiallyScaledGeneralSeries,
    FormalMultilinearSeries.radius_smul_eq _
      (inv_ne_zero (pow_ne_zero (d + 1) hc))]
  refine (show 0 < p.radius /
      ‖Germ.generalRadialScaleContinuousLinearMap c‖ₑ by
        exact ENNReal.div_pos hp.ne' enorm_ne_top).trans_le ?_
  exact p.div_le_radius_compContinuousLinearMap
    (Germ.generalRadialScaleContinuousLinearMap c)

/-- Operator norm bound for scalar multiplication on the algebra input. -/
theorem norm_generalRadialAlgebraScaleContinuousLinearMap_le
    (d : ℕ) (c : ℂ) :
    ‖Germ.generalRadialAlgebraScaleContinuousLinearMap d c‖ ≤ ‖c‖ := by
  calc
    ‖Germ.generalRadialAlgebraScaleContinuousLinearMap d c‖ ≤
        ‖c‖ * ‖ContinuousLinearMap.id ℂ
          (Germ.GeneralDivisionEndomorphism d ×
            Germ.GeneralDivisionEndomorphism d)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ = ‖c‖ := by simp

/-- Some nonzero radial scale places the base division operator inside the
convergence ball of the scaled Banach algebra extension. -/
theorem exists_radialScale_generalFunctionalInput_mem
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (d : ℕ) (hp : 0 < p.radius) :
    ∃ c : ℂ, c ≠ 0 ∧
      Germ.generalFunctionalInput d
          (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
        Metric.eball 0
          (Germ.banachAlgebraExtensionSeries
            (A := Germ.GeneralDivisionEndomorphism d)
            (Germ.radiallyScaledGeneralSeries p d c)).radius := by
  let q := Germ.banachAlgebraExtensionSeries
    (A := Germ.GeneralDivisionEndomorphism d) p
  let base := Germ.generalFunctionalInput d
    (0, (0 : Germ.GeneralCoefficientSpace d))
  have hqRadius : 0 < q.radius :=
    Germ.banachAlgebraExtensionSeries_radius_pos p hp
  obtain ⟨delta, hdelta, hdeltaSmall⟩ :=
    ENNReal.exists_nnreal_pos_mul_lt
      (a := ((‖base‖₊ + 1 : ℝ≥0) : ℝ≥0∞))
      (b := q.radius) (by simp) hqRadius.ne'
  let c : ℂ := (delta : ℝ)
  have hc : c ≠ 0 := by
    simpa [c] using hdelta.ne'
  let scale := Germ.generalRadialAlgebraScaleContinuousLinearMap d c
  have hscaleNorm : ‖scale‖ₑ ≤ (delta : ℝ≥0∞) := by
    rw [enorm_eq_nnnorm]
    have hnorm :=
      Germ.norm_generalRadialAlgebraScaleContinuousLinearMap_le d c
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
        (A := Germ.GeneralDivisionEndomorphism d)
        (Germ.radiallyScaledGeneralSeries p d c)).radius :=
    hdiv.trans_le
      (Germ.div_le_radius_banachAlgebraExtensionSeries_radiallyScaledGeneral
        p d c hc)
  refine ⟨c, hc, ?_⟩
  exact mem_eball_zero_iff.2 hradius

/-- Near the origin, the scaled sum is the normalized radial pullback of the
original sum. -/
theorem eventually_radiallyScaledGeneralSeries_sum_eq
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (d : ℕ) (c : ℂ) (hp : 0 < p.radius) (hc : c ≠ 0) :
    (Germ.radiallyScaledGeneralSeries p d c).sum =ᶠ[nhds 0]
      fun z ↦ (c ^ (d + 1))⁻¹ * p.sum (c • z) := by
  have hpAt : HasFPowerSeriesAt p.sum p 0 :=
    (p.hasFPowerSeriesOnBall hp).hasFPowerSeriesAt
  have hpAtImage : HasFPowerSeriesAt p.sum p
      (Germ.generalRadialScaleContinuousLinearMap c (0 : Source 2)) := by
    simpa using hpAt
  have hcomp := hpAtImage.compContinuousLinearMap
    (u := Germ.generalRadialScaleContinuousLinearMap c)
    (x := (0 : Source 2))
  have hcompZero : HasFPowerSeriesAt
      (p.sum ∘ Germ.generalRadialScaleContinuousLinearMap c)
      (p.compContinuousLinearMap
        (Germ.generalRadialScaleContinuousLinearMap c)) 0 := by
    simpa using hcomp
  have hnormalized : HasFPowerSeriesAt
      ((c ^ (d + 1))⁻¹ •
        (p.sum ∘ Germ.generalRadialScaleContinuousLinearMap c))
      ((c ^ (d + 1))⁻¹ •
        p.compContinuousLinearMap
          (Germ.generalRadialScaleContinuousLinearMap c)) 0 :=
    hcompZero.const_smul
  have hscaledRadius :=
    Germ.radiallyScaledGeneralSeries_radius_pos p d c hp hc
  have hscaled : HasFPowerSeriesAt
      (Germ.radiallyScaledGeneralSeries p d c).sum
      (Germ.radiallyScaledGeneralSeries p d c) 0 :=
    ((Germ.radiallyScaledGeneralSeries p d c).hasFPowerSeriesOnBall
      hscaledRadius).hasFPowerSeriesAt
  filter_upwards [hscaled.eventually_hasSum_sub,
    hnormalized.eventually_hasSum_sub] with z hzScaled hzNormalized
  have heq := hzScaled.unique hzNormalized
  simpa [Germ.radiallyScaledGeneralSeries, Function.comp_def,
    Germ.generalRadialScaleContinuousLinearMap_apply,
    smul_eq_mul] using heq

/-- Scaling a monic polynomial and its coefficients by reciprocal weights
recovers the polynomial in the original coordinate. -/
theorem pow_mul_generalDivisionPolynomialValue_inverse
    (d : ℕ) (c x : ℂ) (a : Germ.GeneralCoefficientSpace d)
    (hc : c ≠ 0) :
    c ^ (d + 1) *
        Germ.generalDivisionPolynomialValue (c⁻¹ * x) a =
      Germ.generalDivisionPolynomialValue x
        (fun i ↦ c ^ (d + 1 - i.1) * a i) := by
  have hpower (k : ℕ) (hk : k ≤ d + 1) :
      c ^ (d + 1) * (c⁻¹) ^ k = c ^ (d + 1 - k) := by
    calc
      c ^ (d + 1) * (c⁻¹) ^ k =
          (c ^ (d + 1 - k) * c ^ k) * (c⁻¹) ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hk]
      _ = c ^ (d + 1 - k) := by
        rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hc, one_pow,
          mul_one]
  unfold Germ.generalDivisionPolynomialValue
  rw [mul_add, Finset.mul_sum]
  congr 1
  · rw [mul_pow]
    calc
      c ^ (d + 1) * ((c⁻¹) ^ (d + 1) * x ^ (d + 1)) =
          (c ^ (d + 1) * (c⁻¹) ^ (d + 1)) *
            x ^ (d + 1) := by ring
      _ = x ^ (d + 1) := by
        rw [hpower (d + 1) le_rfl]
        simp
  · apply Finset.sum_congr rfl
    intro i hi
    have hile : i.1 ≤ d + 1 := by omega
    rw [mul_pow]
    calc
      c ^ (d + 1) * (a i * ((c⁻¹) ^ i.1 * x ^ i.1)) =
          (c ^ (d + 1) * (c⁻¹) ^ i.1) * a i * x ^ i.1 := by
        ring
      _ = c ^ (d + 1 - i.1) * a i * x ^ i.1 := by
        rw [hpower i.1 hile]
      _ = (c ^ (d + 1 - i.1) * a i) * x ^ i.1 := by ring

/-- Analytic preparation of an exactly normalized scalar Taylor series in
every positive degree. -/
theorem exists_analytic_generalPreparation
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0) :
    ∃ b : ℂ → Germ.GeneralCoefficientSpace d,
      ∃ Q : ℂ × ℂ → ℂ,
      AnalyticAt ℂ b 0 ∧
      b 0 = 0 ∧
      AnalyticAt ℂ Q (0, 0) ∧
      Q (0, 0) = 1 ∧
      ∀ᶠ z in nhds (0, 0),
        p.sum (Germ.planePoint z.1 z.2) =
          Germ.generalDivisionPolynomialValue z.1 (b z.2) * Q z := by
  obtain ⟨c, hc, hbase⟩ :=
    Germ.exists_radialScale_generalFunctionalInput_mem p d hp
  let pScaled := Germ.radiallyScaledGeneralSeries p d c
  have hpScaled : 0 < pScaled.radius :=
    Germ.radiallyScaledGeneralSeries_radius_pos p d c hp hc
  have haxisScaled : ∀ n, Germ.mixedCoefficient pScaled n n =
      if n = d + 1 then 1 else 0 :=
    Germ.radiallyScaledGeneralSeries_exact_axis p d c hc haxis
  obtain ⟨a, QScaled, ha, haZero, hQScaled, hQScaledZero,
      hfactorScaled⟩ :=
    Germ.exists_analytic_generalPreparation_of_base_mem
      pScaled d hpScaled haxisScaled hbase
  let inverseScalar : ℂ → ℂ := fun y ↦ c⁻¹ * y
  let inversePair : ℂ × ℂ → ℂ × ℂ := fun z ↦
    (inverseScalar z.1, inverseScalar z.2)
  let b : ℂ → Germ.GeneralCoefficientSpace d := fun y i ↦
    c ^ (d + 1 - i.1) * a (inverseScalar y) i
  let Q : ℂ × ℂ → ℂ := fun z ↦ QScaled (inversePair z)
  have hinverseScalar : AnalyticAt ℂ inverseScalar 0 := by
    dsimp only [inverseScalar]
    fun_prop
  have haAtInverseZero : AnalyticAt ℂ a (inverseScalar 0) := by
    simpa [inverseScalar] using ha
  have haComp : AnalyticAt ℂ (fun y ↦ a (inverseScalar y)) 0 := by
    simpa [Function.comp_def] using
      (AnalyticAt.comp (x := 0) haAtInverseZero hinverseScalar)
  have hb : AnalyticAt ℂ b 0 := by
    have hcoordinate (i : Fin (d + 1)) : AnalyticAt ℂ
        (fun y ↦ c ^ (d + 1 - i.1) * a (inverseScalar y) i) 0 := by
      have hproj : AnalyticAt ℂ
          (fun y ↦ a (inverseScalar y) i) 0 := by
        simpa [Function.comp_def] using
          (AnalyticAt.comp (x := 0)
            ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt
              (a (inverseScalar 0))) haComp)
      exact analyticAt_const.mul hproj
    exact AnalyticAt.pi hcoordinate
  have hbZero : b 0 = 0 := by
    funext i
    simp [b, inverseScalar, haZero]
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
    Germ.eventually_radiallyScaledGeneralSeries_sum_eq p d c hp hc
  have hplaneTendsto : Tendsto
      (fun z : ℂ × ℂ ↦ Germ.planePoint z.1 z.2)
      (nhds (0, 0)) (nhds 0) := by
    have hfun : (fun z : ℂ × ℂ ↦ Germ.planePoint z.1 z.2) =
        (Germ.generalPlanePointContinuousLinearMap :
          ℂ × ℂ → Source 2) := by
      funext z
      exact (Germ.generalPlanePointContinuousLinearMap_apply z).symm
    rw [hfun]
    have hclm :=
      Germ.generalPlanePointContinuousLinearMap.continuous.continuousAt
        (x := ((0, 0) : ℂ × ℂ))
    have hzero : Germ.generalPlanePointContinuousLinearMap
        ((0, 0) : ℂ × ℂ) = 0 :=
      map_zero Germ.generalPlanePointContinuousLinearMap
    rw [← hzero]
    exact hclm
  have hsumPair : ∀ᶠ z : ℂ × ℂ in nhds (0, 0),
      pScaled.sum (Germ.planePoint z.1 z.2) =
        (c ^ (d + 1))⁻¹ * p.sum (c • Germ.planePoint z.1 z.2) :=
    hplaneTendsto.eventually hsumScaled
  have hsumPairAt : ∀ᶠ z : ℂ × ℂ in nhds (inversePair (0, 0)),
      pScaled.sum (Germ.planePoint z.1 z.2) =
        (c ^ (d + 1))⁻¹ * p.sum (c • Germ.planePoint z.1 z.2) := by
    simpa [hinversePairZero] using hsumPair
  have hfactorScaledAt : ∀ᶠ z : ℂ × ℂ in
      nhds (inversePair (0, 0)),
      pScaled.sum (Germ.planePoint z.1 z.2) =
        Germ.generalDivisionPolynomialValue z.1 (a z.2) * QScaled z := by
    simpa [hinversePairZero] using hfactorScaled
  have hsumAtInverse :=
    hinversePair.continuousAt.eventually hsumPairAt
  have hfactorAtInverse :=
    hinversePair.continuousAt.eventually hfactorScaledAt
  refine ⟨b, Q, hb, hbZero, hQ, hQZero, ?_⟩
  filter_upwards [hsumAtInverse, hfactorAtInverse] with z hsum hfactor
  have hscaled : (c ^ (d + 1))⁻¹ *
      p.sum (Germ.planePoint z.1 z.2) =
        Germ.generalDivisionPolynomialValue (inverseScalar z.1)
            (a (inverseScalar z.2)) * QScaled (inversePair z) := by
    rw [← hfactor]
    rw [hsum]
    congr 2
    ext i
    fin_cases i
    · simp [inversePair, inverseScalar, Germ.planePoint, hc]
    · simp [inversePair, inverseScalar, Germ.planePoint, hc]
  calc
    p.sum (Germ.planePoint z.1 z.2) =
        c ^ (d + 1) * ((c ^ (d + 1))⁻¹ *
          p.sum (Germ.planePoint z.1 z.2)) := by
      rw [← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero (d + 1) hc), one_mul]
    _ = c ^ (d + 1) *
        (Germ.generalDivisionPolynomialValue (inverseScalar z.1)
          (a (inverseScalar z.2)) * QScaled (inversePair z)) := by
      rw [hscaled]
    _ = Germ.generalDivisionPolynomialValue z.1 (b z.2) * Q z := by
      rw [← mul_assoc,
        Germ.pow_mul_generalDivisionPolynomialValue_inverse d c z.1
          (a (inverseScalar z.2)) hc]

/-- The monic polynomial attached to a vector of lower coefficient germs. -/
@[expose] noncomputable def generalWeierstrassPolynomial
    (d : ℕ) (a : Fin (d + 1) → Germ 1) : Polynomial (Germ 1) :=
  Polynomial.monomial (d + 1) 1 +
    ∑ i : Fin (d + 1), Polynomial.monomial i.1 (a i)

/-- The leading coefficient of the general Weierstrass polynomial is one. -/
theorem generalWeierstrassPolynomial_coeff_degree
    (d : ℕ) (a : Fin (d + 1) → Germ 1) :
    (Germ.generalWeierstrassPolynomial d a).coeff (d + 1) = 1 := by
  simp only [Germ.generalWeierstrassPolynomial, Polynomial.coeff_add]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, if_true]
  have hsum : (∑ i : Fin (d + 1),
      if i.1 = d + 1 then a i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg (by omega)]
  rw [hsum, add_zero]

/-- Every lower coefficient is recovered from the supplied coefficient
vector. -/
theorem generalWeierstrassPolynomial_coeff_of_lt
    (d : ℕ) (a : Fin (d + 1) → Germ 1)
    (k : ℕ) (hk : k < d + 1) :
    (Germ.generalWeierstrassPolynomial d a).coeff k =
      a ⟨k, hk⟩ := by
  simp only [Germ.generalWeierstrassPolynomial, Polynomial.coeff_add]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [if_neg (by omega : d + 1 ≠ k), zero_add]
  let ik : Fin (d + 1) := ⟨k, hk⟩
  rw [Finset.sum_eq_single ik]
  · simp [ik]
  · intro i hi hne
    rw [if_neg]
    intro heq
    apply hne
    apply Fin.ext
    simpa [ik] using heq
  · simp

/-- Coefficients above the prescribed degree vanish. -/
theorem generalWeierstrassPolynomial_coeff_of_degree_lt
    (d : ℕ) (a : Fin (d + 1) → Germ 1)
    (k : ℕ) (hk : d + 1 < k) :
    (Germ.generalWeierstrassPolynomial d a).coeff k = 0 := by
  simp only [Germ.generalWeierstrassPolynomial, Polynomial.coeff_add]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [if_neg (by omega : d + 1 ≠ k), zero_add]
  apply Finset.sum_eq_zero
  intro i hi
  rw [if_neg (by omega)]

/-- The general Weierstrass polynomial has degree `d + 1`. -/
theorem generalWeierstrassPolynomial_natDegree
    (d : ℕ) (a : Fin (d + 1) → Germ 1) :
    (Germ.generalWeierstrassPolynomial d a).natDegree = d + 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    exact Germ.generalWeierstrassPolynomial_coeff_of_degree_lt d a k hk
  · rw [Germ.generalWeierstrassPolynomial_coeff_degree]
    exact one_ne_zero

/-- The general Weierstrass polynomial is monic. -/
theorem generalWeierstrassPolynomial_monic
    (d : ℕ) (a : Fin (d + 1) → Germ 1) :
    (Germ.generalWeierstrassPolynomial d a).Monic := by
  change (Germ.generalWeierstrassPolynomial d a).coeff
      (Germ.generalWeierstrassPolynomial d a).natDegree = 1
  rw [Germ.generalWeierstrassPolynomial_natDegree,
    Germ.generalWeierstrassPolynomial_coeff_degree]

/-- Vanishing of the lower coefficient germs at the origin makes the
polynomial distinguished. -/
theorem generalWeierstrassPolynomial_coeff_mem_maximalIdeal
    (d : ℕ) {a : Fin (d + 1) → Germ 1}
    (ha : ∀ i, a i ∈ Germ.maximalIdeal 1) :
    ∀ k, k < d + 1 →
      (Germ.generalWeierstrassPolynomial d a).coeff k ∈
        Germ.maximalIdeal 1 := by
  intro k hk
  rw [Germ.generalWeierstrassPolynomial_coeff_of_lt d a k hk]
  exact ha ⟨k, hk⟩

/-- Evaluation of the general Weierstrass polynomial is its expected plane
germ expression. -/
theorem firstCoordinatePolynomialEvaluation_generalWeierstrassPolynomial
    (d : ℕ) (a : Fin (d + 1) → Germ 1) :
    Germ.firstCoordinatePolynomialEvaluation
        (Germ.generalWeierstrassPolynomial d a) =
      Germ.coordinate (0 : Fin 2) ^ (d + 1) +
        ∑ i : Fin (d + 1),
          Germ.hyperplaneExtension 1 (a i) *
            Germ.coordinate (0 : Fin 2) ^ i.1 := by
  rw [Germ.firstCoordinatePolynomialEvaluation,
    Germ.generalWeierstrassPolynomial, Polynomial.eval₂_add,
    Polynomial.eval₂_monomial, map_one, one_mul,
    Polynomial.eval₂_finsetSum]
  apply congrArg
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval₂_monomial]

/-- Every analytic germ has a function representative analytic at the
origin. -/
theorem exists_analyticRepresentative_allOrders
    {n : ℕ} (f : Germ n) :
    ∃ F : Source n → ℂ, ∃ hF : AnalyticAt ℂ F 0,
      f = Germ.ofFunction F hF := by
  rcases f with ⟨f, hf⟩
  change IsAnalyticGerm f at hf
  induction f using Filter.Germ.inductionOn with
  | _ F =>
      rw [isAnalyticGerm_ofFun] at hf
      exact ⟨F, hf, rfl⟩

/-- An analytic function with an exactly normalized first coordinate axis
admits a Weierstrass factorization in every positive degree. -/
theorem hasAnalyticWeierstrassFactorizationOfOrder_succ_of_exact_axis_series
    (F : Source 2 → ℂ)
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (d : ℕ) (hp : HasFPowerSeriesAt F p 0)
    (haxis : ∀ n, Germ.mixedCoefficient p n n =
      if n = d + 1 then 1 else 0) :
    Germ.HasAnalyticWeierstrassFactorizationOfOrder
      (Germ.ofFunction F hp.analyticAt) (d + 1) := by
  obtain ⟨b, Q, hb, hbZero, hQ, hQZero, hfactor⟩ :=
    Germ.exists_analytic_generalPreparation p d hp.radius_pos haxis
  have hprojectionOne : AnalyticAt ℂ
      (fun y : Source 1 ↦ y 0) 0 :=
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 1 ↦ ℂ) (0 : Fin 1)).analyticAt 0
  have hbSource (i : Fin (d + 1)) : AnalyticAt ℂ
      (fun y : Source 1 ↦ b (y 0) i) 0 := by
    have hbCoordinate : AnalyticAt ℂ (fun y ↦ b y i) 0 := by
      simpa [Function.comp_def] using
        (AnalyticAt.comp (x := 0)
          ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt (b 0)) hb)
    exact AnalyticAt.fun_comp
      (f := fun y : Source 1 ↦ y 0) hbCoordinate hprojectionOne
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
  let a : Fin (d + 1) → Germ 1 := fun i ↦ Germ.ofFunction
    (fun y : Source 1 ↦ b (y 0) i) (hbSource i)
  let u : Germ 2 := Germ.ofFunction
    (fun z : Source 2 ↦ Q (z 0, z 1)) hQSource
  have ha : ∀ i, a i ∈ Germ.maximalIdeal 1 := by
    intro i
    rw [Germ.mem_maximalIdeal_iff]
    simp [a, Germ.valueRingHom_ofFunction, hbZero]
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
  let P := Germ.generalWeierstrassPolynomial d a
  have heq : Germ.ofFunction F hp.analyticAt =
      Germ.firstCoordinatePolynomialEvaluation P * u := by
    rw [show Germ.firstCoordinatePolynomialEvaluation P =
        Germ.coordinate (0 : Fin 2) ^ (d + 1) +
          ∑ i : Fin (d + 1),
            Germ.hyperplaneExtension 1 (a i) *
              Germ.coordinate (0 : Fin 2) ^ i.1 by
      exact Germ.firstCoordinatePolynomialEvaluation_generalWeierstrassPolynomial
        d a]
    apply Subtype.ext
    let lead : Source 2 → ℂ := fun z ↦ z 0 ^ (d + 1)
    let term : Fin (d + 1) → Source 2 → ℂ := fun i z ↦
      b (z 1) i * z 0 ^ i.1
    let quotient : Source 2 → ℂ := fun z ↦ Q (z 0, z 1)
    have hfun : (F : FunctionGerm 2) =
        (((lead + ∑ i, term i) * quotient : Source 2 → ℂ) :
          FunctionGerm 2) := by
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [hsum, hfactorSource] with z hzSum hzFactor
      dsimp only [lead, term, quotient]
      simp only [Pi.add_apply, Pi.mul_apply, Finset.sum_apply]
      rw [hzSum]
      simpa only [coordinatePair,
        ContinuousLinearEquiv.finTwoArrow_apply,
        Germ.planePoint_coordinates,
        Germ.generalDivisionPolynomialValue] using hzFactor
    have hcoordinatePow (k : ℕ) :
        (((fun z : Source 2 ↦ z 0 ^ k) : Source 2 → ℂ) :
            FunctionGerm 2) =
          ((Germ.coordinate (0 : Fin 2) ^ k : Germ 2) :
            FunctionGerm 2) := by
      calc
        (((fun z : Source 2 ↦ z 0 ^ k) : Source 2 → ℂ) :
            FunctionGerm 2) =
            (((fun z : Source 2 ↦ z 0) ^ k : Source 2 → ℂ) :
              FunctionGerm 2) := rfl
        _ = (((fun z : Source 2 ↦ z 0) : FunctionGerm 2) ^ k) :=
          Filter.Germ.coe_pow (l := nhds (0 : Source 2))
            (fun z : Source 2 ↦ z 0) k
        _ = (((Germ.coordinate (0 : Fin 2) : Germ 2) :
            FunctionGerm 2) ^ k) := by
          rw [Germ.coe_coordinate]
        _ = ((Germ.coordinate (0 : Fin 2) ^ k : Germ 2) :
            FunctionGerm 2) :=
          (map_pow (analyticGermSubring 2).subtype
            (Germ.coordinate (0 : Fin 2)) k).symm
    have hhyperplane (i : Fin (d + 1)) :
        (((fun z : Source 2 ↦ b (z 1) i) : Source 2 → ℂ) :
            FunctionGerm 2) =
          ((Germ.hyperplaneExtension 1 (a i) : Germ 2) :
            FunctionGerm 2) := by
      rw [show Germ.hyperplaneExtension 1 (a i) =
          Germ.ofFunction (fun z : Source 2 ↦ b (z 1) i)
            (by
              have hbAtImage : AnalyticAt ℂ
                  (fun y : Source 1 ↦ b (y 0) i)
                  (Germ.hyperplaneTail 1 (0 : Source 2)) := by
                simpa using hbSource i
              have hcomposition := AnalyticAt.comp
                (x := (0 : Source 2)) hbAtImage
                  ((Germ.hyperplaneTail 1).analyticAt 0)
              simpa [Function.comp_def] using hcomposition) by
        simp [a, Germ.hyperplaneExtension_ofFunction,
          Function.comp_def]]
      rfl
    have hterm (i : Fin (d + 1)) :
        ((term i : Source 2 → ℂ) : FunctionGerm 2) =
          ((Germ.hyperplaneExtension 1 (a i) *
              Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
            FunctionGerm 2) := by
      calc
        ((term i : Source 2 → ℂ) : FunctionGerm 2) =
            ((((fun z : Source 2 ↦ b (z 1) i) *
              fun z : Source 2 ↦ z 0 ^ i.1) : Source 2 → ℂ) :
                FunctionGerm 2) := rfl
        _ = (((fun z : Source 2 ↦ b (z 1) i) : FunctionGerm 2) *
            ((fun z : Source 2 ↦ z 0 ^ i.1) : FunctionGerm 2)) :=
          Filter.Germ.coe_mul (l := nhds (0 : Source 2))
            (fun z : Source 2 ↦ b (z 1) i)
            (fun z : Source 2 ↦ z 0 ^ i.1)
        _ = (((Germ.hyperplaneExtension 1 (a i) : Germ 2) :
              FunctionGerm 2) *
            ((Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
              FunctionGerm 2)) := by
          rw [hhyperplane, hcoordinatePow]
        _ = ((Germ.hyperplaneExtension 1 (a i) *
              Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
            FunctionGerm 2) :=
          ((analyticGermSubring 2).subtype.map_mul
            (Germ.hyperplaneExtension 1 (a i))
            (Germ.coordinate (0 : Fin 2) ^ i.1)).symm
    have hterms :
        (((∑ i, term i) : Source 2 → ℂ) : FunctionGerm 2) =
          ((∑ i : Fin (d + 1),
              Germ.hyperplaneExtension 1 (a i) *
                Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
            FunctionGerm 2) := by
      calc
        (((∑ i, term i) : Source 2 → ℂ) : FunctionGerm 2) =
            ∑ i : Fin (d + 1),
              ((term i : Source 2 → ℂ) : FunctionGerm 2) := by
          simpa only using Germ.coe_sum (nhds (0 : Source 2)) ℂ
            term Finset.univ
        _ = ∑ i : Fin (d + 1),
            ((Germ.hyperplaneExtension 1 (a i) *
                Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
              FunctionGerm 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hterm i
        _ = ((∑ i : Fin (d + 1),
              Germ.hyperplaneExtension 1 (a i) *
                Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
            FunctionGerm 2) :=
          (map_sum (analyticGermSubring 2).subtype
            (fun i : Fin (d + 1) ↦
              Germ.hyperplaneExtension 1 (a i) *
                Germ.coordinate (0 : Fin 2) ^ i.1)
            Finset.univ).symm
    have hpolynomial :
        (((lead + ∑ i, term i) : Source 2 → ℂ) :
            FunctionGerm 2) =
          ((Germ.coordinate (0 : Fin 2) ^ (d + 1) +
              ∑ i : Fin (d + 1),
                Germ.hyperplaneExtension 1 (a i) *
                  Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
            FunctionGerm 2) := by
      calc
        (((lead + ∑ i, term i) : Source 2 → ℂ) :
            FunctionGerm 2) =
            ((lead : Source 2 → ℂ) : FunctionGerm 2) +
              (((∑ i, term i) : Source 2 → ℂ) :
                FunctionGerm 2) :=
          Filter.Germ.coe_add (l := nhds (0 : Source 2)) lead
            (∑ i, term i)
        _ = ((Germ.coordinate (0 : Fin 2) ^ (d + 1) : Germ 2) :
              FunctionGerm 2) +
            ((∑ i : Fin (d + 1),
                Germ.hyperplaneExtension 1 (a i) *
                  Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
              FunctionGerm 2) := by
          rw [show ((lead : Source 2 → ℂ) : FunctionGerm 2) =
              ((Germ.coordinate (0 : Fin 2) ^ (d + 1) : Germ 2) :
                FunctionGerm 2) by exact hcoordinatePow (d + 1), hterms]
        _ = ((Germ.coordinate (0 : Fin 2) ^ (d + 1) +
              ∑ i : Fin (d + 1),
                Germ.hyperplaneExtension 1 (a i) *
                  Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
            FunctionGerm 2) :=
          ((analyticGermSubring 2).subtype.map_add
            (Germ.coordinate (0 : Fin 2) ^ (d + 1))
            (∑ i : Fin (d + 1),
              Germ.hyperplaneExtension 1 (a i) *
                Germ.coordinate (0 : Fin 2) ^ i.1)).symm
    calc
      ((Germ.ofFunction F hp.analyticAt : Germ 2) : FunctionGerm 2) =
          (F : FunctionGerm 2) := rfl
      _ = (((lead + ∑ i, term i) * quotient : Source 2 → ℂ) :
          FunctionGerm 2) := hfun
      _ = (((lead + ∑ i, term i) : Source 2 → ℂ) :
            FunctionGerm 2) *
          ((quotient : Source 2 → ℂ) : FunctionGerm 2) :=
        Filter.Germ.coe_mul (l := nhds (0 : Source 2))
          (lead + ∑ i, term i) quotient
      _ = ((Germ.coordinate (0 : Fin 2) ^ (d + 1) +
              ∑ i : Fin (d + 1),
                Germ.hyperplaneExtension 1 (a i) *
                  Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
            FunctionGerm 2) * ((u : Germ 2) : FunctionGerm 2) := by
        rw [hpolynomial]
        rfl
      _ = (((Germ.coordinate (0 : Fin 2) ^ (d + 1) +
              ∑ i : Fin (d + 1),
                Germ.hyperplaneExtension 1 (a i) *
                  Germ.coordinate (0 : Fin 2) ^ i.1) * u : Germ 2) :
            FunctionGerm 2) :=
        ((analyticGermSubring 2).subtype.map_mul
          (Germ.coordinate (0 : Fin 2) ^ (d + 1) +
            ∑ i : Fin (d + 1),
              Germ.hyperplaneExtension 1 (a i) *
                Germ.coordinate (0 : Fin 2) ^ i.1) u).symm
  refine ⟨P, u, Germ.generalWeierstrassPolynomial_monic d a,
    Germ.generalWeierstrassPolynomial_natDegree d a,
    Germ.generalWeierstrassPolynomial_coeff_mem_maximalIdeal d ha,
    hu, heq⟩

/-- On the first coordinate axis, a regular germ is its regular power times
the restriction of the corresponding analytic quotient. -/
theorem lineRestriction_eq_pow_mul_tailIterate_of_regular_allOrders
    {n : ℕ} {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f n) :
    Germ.lineRestriction (Germ.firstCoordinateVector 1) f =
      Germ.coordinate (0 : Fin 1) ^ n *
        Germ.lineRestriction (Germ.firstCoordinateVector 1)
          (Germ.firstCoordinateTailIterate n f) := by
  have hexpansion := congrArg
    (Germ.lineRestrictionAlgHom (Germ.firstCoordinateVector 1))
    (Germ.firstCoordinate_finite_expansion (d := n) f)
  simp only [map_add, map_mul, map_pow, map_sum,
    Germ.lineRestrictionAlgHom_apply,
    Germ.lineRestriction_firstCoordinate,
    Germ.lineRestriction_hyperplaneExtension_firstCoordinate] at hexpansion
  have hsum : ∑ k ∈ Finset.range n,
      Germ.coordinate (0 : Fin 1) ^ k *
        Germ.constRingHom 1
          (Germ.valueRingHom 1
            (Germ.firstCoordinateTaylorCoefficient k f)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    rw [(Germ.isRegularInFirstCoordinateOfOrder_iff.mp hregular).2 k hklt]
    simp
  calc
    Germ.lineRestriction (Germ.firstCoordinateVector 1) f =
        (∑ k ∈ Finset.range n,
          Germ.coordinate (0 : Fin 1) ^ k *
            Germ.constRingHom 1
              (Germ.valueRingHom 1
                (Germ.firstCoordinateTaylorCoefficient k f))) +
          Germ.coordinate (0 : Fin 1) ^ n *
            Germ.lineRestriction (Germ.firstCoordinateVector 1)
              (Germ.firstCoordinateTailIterate n f) := hexpansion
    _ = Germ.coordinate (0 : Fin 1) ^ n *
          Germ.lineRestriction (Germ.firstCoordinateVector 1)
            (Germ.firstCoordinateTailIterate n f) := by
      rw [hsum, zero_add]

/-- Analytic Weierstrass preparation holds for every plane analytic germ
that is regular of positive order in the first coordinate. -/
theorem hasAnalyticWeierstrassFactorizationOfOrder_succ
    {d : ℕ} {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f (d + 1)) :
    Germ.HasAnalyticWeierstrassFactorizationOfOrder f (d + 1) := by
  let v : Germ 2 := Germ.firstCoordinateTailIterate (d + 1) f
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
        Germ.coordinate (0 : Fin 1) ^ (d + 1) *
          Germ.lineRestriction (Germ.firstCoordinateVector 1) v := by
    simpa only [v] using
      Germ.lineRestriction_eq_pow_mul_tailIterate_of_regular_allOrders
        hregular
  have hlineG : Germ.lineRestriction
      (Germ.firstCoordinateVector 1) g =
        Germ.coordinate (0 : Fin 1) ^ (d + 1) := by
    change Germ.lineRestriction (Germ.firstCoordinateVector 1) (f * s) = _
    change (Germ.lineRestrictionAlgHom
        (Germ.firstCoordinateVector 1)) (f * s) = _
    rw [map_mul, Germ.lineRestrictionAlgHom_apply,
      Germ.lineRestrictionAlgHom_apply, hlineF, mul_assoc,
      ← map_mul, hvs, map_one, mul_one]
  obtain ⟨F, hF, hg⟩ := Germ.exists_analyticRepresentative_allOrders g
  rcases hF with ⟨p, hp⟩
  have hlineRepresentative : Germ.lineRestriction
      (Germ.firstCoordinateVector 1)
        (Germ.ofFunction F hp.analyticAt) =
      Germ.coordinate (0 : Fin 1) ^ (d + 1) := by
    rw [← hg]
    exact hlineG
  have haxisTaylor : Germ.firstCoordinateAxisTaylorSeries
      (Germ.ofFunction F hp.analyticAt) =
        (PowerSeries.X : PowerSeries ℂ) ^ (d + 1) := by
    rw [Germ.firstCoordinateAxisTaylorSeries,
      hlineRepresentative]
    change Germ.oneVariableTaylorRingHom
        (Germ.coordinate (0 : Fin 1) ^ (d + 1)) = _
    rw [map_pow, Germ.oneVariableTaylorRingHom_apply,
      Germ.oneVariableTaylorSeries_coordinate]
  have haxis : ∀ n,
      Germ.mixedCoefficient p n n =
        if n = d + 1 then 1 else 0 := by
    intro n
    rw [Germ.mixedCoefficient_self_eq_value_firstCoordinateTaylorCoefficient
      hp n]
    rw [← Germ.firstCoordinateAxisTaylorSeries_coeff,
      haxisTaylor]
    simp [PowerSeries.coeff_X_pow]
  have hgPreparation : Germ.HasAnalyticWeierstrassFactorizationOfOrder
      g (d + 1) := by
    rw [hg]
    exact
      Germ.hasAnalyticWeierstrassFactorizationOfOrder_succ_of_exact_axis_series
        F p d hp haxis
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

/-- Analytic Weierstrass preparation holds at every positive regular order. -/
theorem hasAnalyticWeierstrassFactorizationOfOrder_of_pos
    {n : ℕ} (hn : 0 < n) {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f n) :
    Germ.HasAnalyticWeierstrassFactorizationOfOrder f n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact Germ.hasAnalyticWeierstrassFactorizationOfOrder_succ hregular

/-- The completed image closure condition holds in every positive order. -/
theorem completedWeierstrassImageClosureAtOrder_of_pos
    {n : ℕ} (hn : 0 < n) :
    Germ.CompletedWeierstrassImageClosureAtOrder n :=
  (Germ.completedWeierstrassImageClosureAtOrder_iff n).2
    fun _f hregular ↦
      Germ.hasAnalyticWeierstrassFactorizationOfOrder_of_pos hn hregular

end Germ

end OnLeConjecture.Analytic
