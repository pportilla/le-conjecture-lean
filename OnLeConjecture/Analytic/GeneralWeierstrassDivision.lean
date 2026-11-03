/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.AllOrdersPreparation
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Analytic Weierstrass division in every positive degree

The finite division state gives quotient and remainder functions for an
arbitrary analytic dividend and a monic polynomial whose lower coefficients
are analytic functions of the second coordinate. Radial rescaling removes
the convergence condition on the division operator.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Metric
open scoped BigOperators NNReal ENNReal Topology

namespace Germ

/-- Conditional functional Weierstrass division. The base operator condition
is removed below by radial rescaling. -/
theorem exists_analytic_generalDivision_of_base_mem
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius)
    (hbase : Germ.generalFunctionalInput d
        (0, (0 : Germ.GeneralCoefficientSpace d)) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius)
    (a : ℂ → Germ.GeneralCoefficientSpace d)
    (ha : AnalyticAt ℂ a 0) (haZero : a 0 = 0) :
    ∃ Q : ℂ × ℂ → ℂ,
      ∃ R : ℂ → Germ.GeneralCoefficientSpace d,
      AnalyticAt ℂ Q (0, 0) ∧
      AnalyticAt ℂ R 0 ∧
      ∀ᶠ z in nhds (0, 0),
        p.sum (Germ.planePoint z.1 z.2) =
          Germ.generalDivisionPolynomialValue z.1 (a z.2) * Q z +
            ∑ i : Fin (d + 1), z.1 ^ i.1 * R z.2 i := by
  let Q : ℂ × ℂ → ℂ := fun z ↦
    Germ.generalFunctionalQuotient p d z.1 z.2 (a z.2)
  let R : ℂ → Germ.GeneralCoefficientSpace d := fun y ↦
    Germ.generalFunctionalRemainder p d (y, a y)
  have hQ : AnalyticAt ℂ Q (0, 0) :=
    Germ.analyticAt_generalFunctionalQuotient_comp
      p d hp hbase a ha haZero
  have hpair : AnalyticAt ℂ
      (fun y : ℂ ↦ (y, a y)) 0 :=
    analyticAt_id.prod ha
  have hRBase : AnalyticAt ℂ (Germ.generalFunctionalRemainder p d)
      (0, (0 : Germ.GeneralCoefficientSpace d)) :=
    Germ.analyticAt_generalFunctionalRemainder p d hp hbase
  have hRAt : AnalyticAt ℂ (Germ.generalFunctionalRemainder p d)
      ((0 : ℂ), a 0) := by
    simpa [haZero] using hRBase
  have hR : AnalyticAt ℂ R 0 := by
    simpa [R, Function.comp_def] using
      (AnalyticAt.comp (x := 0) hRAt hpair)
  have hpEventually : ∀ᶠ z : ℂ × ℂ in nhds (0, 0),
      Germ.planePoint z.1 z.2 ∈ Metric.eball 0 p.radius := by
    have htendsto :=
      Germ.generalPlanePointContinuousLinearMap.continuous.continuousAt
        (x := ((0, 0) : ℂ × ℂ))
    have hball : Metric.eball 0 p.radius ∈
        nhds (Germ.generalPlanePointContinuousLinearMap (0, 0)) := by
      simpa [Germ.planePoint] using Metric.eball_mem_nhds 0 hp
    exact htendsto.eventually hball
  have hinputAnalytic := Germ.analyticAt_generalFunctionalFullInput d a ha
  have hbaseFull : Germ.generalFunctionalFullInput d a (0, 0) ∈
      Metric.eball 0
        (Germ.banachAlgebraExtensionSeries
          (A := Germ.GeneralDivisionEndomorphism d) p).radius := by
    simpa [Germ.generalFunctionalFullInput, Germ.generalFunctionalInput,
      haZero] using hbase
  have hxEventually : ∀ᶠ z : ℂ × ℂ in nhds (0, 0),
      Germ.generalFunctionalFullInput d a z ∈
        Metric.eball 0
          (Germ.banachAlgebraExtensionSeries
            (A := Germ.GeneralDivisionEndomorphism d) p).radius :=
    hinputAnalytic.continuousAt.eventually
      (Metric.isOpen_eball.mem_nhds hbaseFull)
  have hzeroSource : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦ ((0 : ℂ), z.2)) (0, 0) :=
    analyticAt_const.prod analyticAt_snd
  have hzeroInput : AnalyticAt ℂ
      (fun z : ℂ × ℂ ↦
        Germ.generalFunctionalFullInput d a (0, z.2)) (0, 0) := by
    simpa [Function.comp_def] using
      (AnalyticAt.comp (x := (0, 0)) hinputAnalytic hzeroSource)
  have hzeroEventually : ∀ᶠ z : ℂ × ℂ in nhds (0, 0),
      Germ.generalFunctionalFullInput d a (0, z.2) ∈
        Metric.eball 0
          (Germ.banachAlgebraExtensionSeries
            (A := Germ.GeneralDivisionEndomorphism d) p).radius :=
    hzeroInput.continuousAt.eventually
      (Metric.isOpen_eball.mem_nhds hbaseFull)
  refine ⟨Q, R, hQ, hR, ?_⟩
  filter_upwards [hpEventually, hxEventually, hzeroEventually] with
      z hpz hxz hzeroz
  have hevaluation := Germ.generalDivisionStateEvaluation_functionalState
    p d z.1 z.2 (a z.2) hpz hxz
  have hremainder :
      (Germ.generalFunctionalState p d z.1 (a z.2) z.2).2 = R z.2 := by
    simpa [R] using Germ.generalFunctionalState_remainder_eq
      p d z.1 z.2 (a z.2) hxz hzeroz
  rw [Germ.generalDivisionStateEvaluation, hremainder] at hevaluation
  simpa [Q, Germ.generalFunctionalQuotient] using hevaluation.symm

/-- Radial normalization of the lower coefficients of a monic polynomial. -/
@[expose] noncomputable def radiallyScaledGeneralCoefficients
    (d : ℕ) (c : ℂ)
    (a : ℂ → Germ.GeneralCoefficientSpace d) :
    ℂ → Germ.GeneralCoefficientSpace d := fun y i ↦
  (c ^ (d + 1 - i.1))⁻¹ * a (c * y) i

/-- Scaling back the normalized coefficient vector recovers the original
coefficient vector. -/
theorem pow_mul_radiallyScaledGeneralCoefficients_inverse
    (d : ℕ) (c y : ℂ)
    (a : ℂ → Germ.GeneralCoefficientSpace d) (hc : c ≠ 0) :
    (fun i ↦ c ^ (d + 1 - i.1) *
      Germ.radiallyScaledGeneralCoefficients d c a (c⁻¹ * y) i) =
        a y := by
  funext i
  simp [Germ.radiallyScaledGeneralCoefficients, hc]

/-- Radial normalization preserves analyticity of a polynomial coefficient
vector. -/
theorem analyticAt_radiallyScaledGeneralCoefficients
    (d : ℕ) (c : ℂ)
    (a : ℂ → Germ.GeneralCoefficientSpace d)
    (ha : AnalyticAt ℂ a 0) :
    AnalyticAt ℂ (Germ.radiallyScaledGeneralCoefficients d c a) 0 := by
  have hscale : AnalyticAt ℂ (fun y : ℂ ↦ c * y) 0 := by
    fun_prop
  have haAtScaledZero : AnalyticAt ℂ a (c * (0 : ℂ)) := by
    simpa using ha
  have haComp : AnalyticAt ℂ (fun y : ℂ ↦ a (c * y)) 0 := by
    simpa [Function.comp_def] using
      (AnalyticAt.comp (x := 0) haAtScaledZero hscale)
  apply AnalyticAt.pi
  intro i
  have hcoordinate : AnalyticAt ℂ (fun y : ℂ ↦ a (c * y) i) 0 := by
    simpa [Function.comp_def] using
      (AnalyticAt.comp (x := 0)
        ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt (a (c * 0)))
        haComp)
  exact analyticAt_const.mul hcoordinate

@[simp]
theorem radiallyScaledGeneralCoefficients_zero
    (d : ℕ) (c : ℂ)
    (a : ℂ → Germ.GeneralCoefficientSpace d) (haZero : a 0 = 0) :
    Germ.radiallyScaledGeneralCoefficients d c a 0 = 0 := by
  funext i
  simp [Germ.radiallyScaledGeneralCoefficients, haZero]

/-- Scaling a polynomial remainder at the inverse radial coordinate gives
the corresponding remainder in the original coordinate. -/
theorem pow_mul_generalRemainderSum_inverse
    (d : ℕ) (c x : ℂ)
    (r : Germ.GeneralCoefficientSpace d) (hc : c ≠ 0) :
    c ^ (d + 1) *
        (∑ i : Fin (d + 1), (c⁻¹ * x) ^ i.1 * r i) =
      ∑ i : Fin (d + 1),
        x ^ i.1 * (c ^ (d + 1 - i.1) * r i) := by
  have hpower (k : ℕ) (hk : k ≤ d + 1) :
      c ^ (d + 1) * (c⁻¹) ^ k = c ^ (d + 1 - k) := by
    calc
      c ^ (d + 1) * (c⁻¹) ^ k =
          (c ^ (d + 1 - k) * c ^ k) * (c⁻¹) ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hk]
      _ = c ^ (d + 1 - k) := by
        rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hc, one_pow,
          mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hile : i.1 ≤ d + 1 := by omega
  rw [mul_pow]
  calc
    c ^ (d + 1) * ((c⁻¹) ^ i.1 * x ^ i.1 * r i) =
        (c ^ (d + 1) * (c⁻¹) ^ i.1) * x ^ i.1 * r i := by
      ring
    _ = c ^ (d + 1 - i.1) * x ^ i.1 * r i := by
      rw [hpower i.1 hile]
    _ = x ^ i.1 * (c ^ (d + 1 - i.1) * r i) := by
      ring

/-- Functional Weierstrass division for every positive degree. -/
theorem exists_analytic_generalDivision
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hp : 0 < p.radius)
    (a : ℂ → Germ.GeneralCoefficientSpace d)
    (ha : AnalyticAt ℂ a 0) (haZero : a 0 = 0) :
    ∃ Q : ℂ × ℂ → ℂ,
      ∃ R : ℂ → Germ.GeneralCoefficientSpace d,
      AnalyticAt ℂ Q (0, 0) ∧
      AnalyticAt ℂ R 0 ∧
      ∀ᶠ z in nhds (0, 0),
        p.sum (Germ.planePoint z.1 z.2) =
          Germ.generalDivisionPolynomialValue z.1 (a z.2) * Q z +
            ∑ i : Fin (d + 1), z.1 ^ i.1 * R z.2 i := by
  obtain ⟨c, hc, hbase⟩ :=
    Germ.exists_radialScale_generalFunctionalInput_mem p d hp
  let pScaled := Germ.radiallyScaledGeneralSeries p d c
  let aScaled := Germ.radiallyScaledGeneralCoefficients d c a
  have hpScaled : 0 < pScaled.radius :=
    Germ.radiallyScaledGeneralSeries_radius_pos p d c hp hc
  have haScaled : AnalyticAt ℂ aScaled 0 :=
    Germ.analyticAt_radiallyScaledGeneralCoefficients d c a ha
  have haScaledZero : aScaled 0 = 0 :=
    Germ.radiallyScaledGeneralCoefficients_zero d c a haZero
  obtain ⟨QScaled, RScaled, hQScaled, hRScaled, hdivisionScaled⟩ :=
    Germ.exists_analytic_generalDivision_of_base_mem
      pScaled d hpScaled hbase aScaled haScaled haScaledZero
  let inverseScalar : ℂ → ℂ := fun y ↦ c⁻¹ * y
  let inversePair : ℂ × ℂ → ℂ × ℂ := fun z ↦
    (inverseScalar z.1, inverseScalar z.2)
  let Q : ℂ × ℂ → ℂ := fun z ↦ QScaled (inversePair z)
  let R : ℂ → Germ.GeneralCoefficientSpace d := fun y i ↦
    c ^ (d + 1 - i.1) * RScaled (inverseScalar y) i
  have hinverseScalar : AnalyticAt ℂ inverseScalar 0 := by
    dsimp only [inverseScalar]
    fun_prop
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
  have hRScaledAt : AnalyticAt ℂ RScaled (inverseScalar 0) := by
    simpa [inverseScalar] using hRScaled
  have hRComp : AnalyticAt ℂ
      (fun y ↦ RScaled (inverseScalar y)) 0 := by
    simpa [Function.comp_def] using
      (AnalyticAt.comp (x := 0) hRScaledAt hinverseScalar)
  have hR : AnalyticAt ℂ R 0 := by
    apply AnalyticAt.pi
    intro i
    have hcoordinate : AnalyticAt ℂ
        (fun y ↦ RScaled (inverseScalar y) i) 0 := by
      simpa [Function.comp_def] using
        (AnalyticAt.comp (x := 0)
          ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt
            (RScaled (inverseScalar 0))) hRComp)
    exact analyticAt_const.mul hcoordinate
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
  have hdivisionScaledAt : ∀ᶠ z : ℂ × ℂ in
      nhds (inversePair (0, 0)),
      pScaled.sum (Germ.planePoint z.1 z.2) =
        Germ.generalDivisionPolynomialValue z.1 (aScaled z.2) * QScaled z +
          ∑ i : Fin (d + 1), z.1 ^ i.1 * RScaled z.2 i := by
    simpa [hinversePairZero] using hdivisionScaled
  have hsumAtInverse :=
    hinversePair.continuousAt.eventually hsumPairAt
  have hdivisionAtInverse :=
    hinversePair.continuousAt.eventually hdivisionScaledAt
  refine ⟨Q, R, hQ, hR, ?_⟩
  filter_upwards [hsumAtInverse, hdivisionAtInverse] with z hsum hdivision
  have hscaled : (c ^ (d + 1))⁻¹ *
      p.sum (Germ.planePoint z.1 z.2) =
        Germ.generalDivisionPolynomialValue (inverseScalar z.1)
            (aScaled (inverseScalar z.2)) * QScaled (inversePair z) +
          ∑ i : Fin (d + 1),
            (inverseScalar z.1) ^ i.1 *
              RScaled (inverseScalar z.2) i := by
    rw [← hdivision]
    rw [hsum]
    congr 2
    ext i
    fin_cases i
    · simp [inversePair, inverseScalar, Germ.planePoint, hc]
    · simp [inversePair, inverseScalar, Germ.planePoint, hc]
  have hpolynomial : c ^ (d + 1) *
      Germ.generalDivisionPolynomialValue (inverseScalar z.1)
        (aScaled (inverseScalar z.2)) =
      Germ.generalDivisionPolynomialValue z.1 (a z.2) := by
    rw [Germ.pow_mul_generalDivisionPolynomialValue_inverse
      d c z.1 (aScaled (inverseScalar z.2)) hc]
    congr 1
    simpa [inverseScalar, aScaled] using
      Germ.pow_mul_radiallyScaledGeneralCoefficients_inverse
        d c z.2 a hc
  have hremainder : c ^ (d + 1) *
      (∑ i : Fin (d + 1),
        (inverseScalar z.1) ^ i.1 *
          RScaled (inverseScalar z.2) i) =
      ∑ i : Fin (d + 1), z.1 ^ i.1 * R z.2 i := by
    simpa [inverseScalar, R] using
      Germ.pow_mul_generalRemainderSum_inverse d c z.1
        (RScaled (inverseScalar z.2)) hc
  calc
    p.sum (Germ.planePoint z.1 z.2) =
        c ^ (d + 1) * ((c ^ (d + 1))⁻¹ *
          p.sum (Germ.planePoint z.1 z.2)) := by
      rw [← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero (d + 1) hc), one_mul]
    _ = c ^ (d + 1) *
        (Germ.generalDivisionPolynomialValue (inverseScalar z.1)
            (aScaled (inverseScalar z.2)) * QScaled (inversePair z) +
          ∑ i : Fin (d + 1),
            (inverseScalar z.1) ^ i.1 *
              RScaled (inverseScalar z.2) i) := by
      rw [hscaled]
    _ = (c ^ (d + 1) *
          Germ.generalDivisionPolynomialValue (inverseScalar z.1)
            (aScaled (inverseScalar z.2))) * QScaled (inversePair z) +
        c ^ (d + 1) *
          (∑ i : Fin (d + 1),
            (inverseScalar z.1) ^ i.1 *
              RScaled (inverseScalar z.2) i) := by
      ring
    _ = Germ.generalDivisionPolynomialValue z.1 (a z.2) * Q z +
          ∑ i : Fin (d + 1), z.1 ^ i.1 * R z.2 i := by
      rw [hpolynomial, hremainder]

/-- Writing a one variable representative on scalar coordinates and then
returning to `Source 1` recovers the original function. -/
theorem oneVariableRepresentative_comp_coordinate
    (F : Source 1 → ℂ) :
    (fun y : Source 1 ↦ Germ.oneVariableRepresentative F (y 0)) = F := by
  funext y
  rw [Germ.oneVariableRepresentative_apply]
  congr 1
  apply Germ.oneVariableEquiv.injective
  simp [Germ.oneVariableEquiv]

/-- Analytic Weierstrass division by a monic polynomial of arbitrary positive
degree whose lower coefficients vanish at the origin. -/
theorem exists_generalWeierstrassDivision
    (d : ℕ) (a : Fin (d + 1) → Germ 1)
    (ha : ∀ i, a i ∈ Germ.maximalIdeal 1) (f : Germ 2) :
    ∃ q : Germ 2, ∃ r : Fin (d + 1) → Germ 1,
      f = Germ.firstCoordinatePolynomialEvaluation
            (Germ.generalWeierstrassPolynomial d a) * q +
        ∑ i : Fin (d + 1),
          Germ.coordinate (0 : Fin 2) ^ i.1 *
            Germ.hyperplaneExtension 1 (r i) := by
  obtain ⟨F, hF, hf⟩ := Germ.exists_analyticRepresentative_allOrders f
  rcases hF with ⟨p, hp⟩
  choose A hA hAeq using fun i ↦
    Germ.exists_analyticRepresentative_allOrders (a i)
  let aScalar : ℂ → Germ.GeneralCoefficientSpace d := fun y i ↦
    Germ.oneVariableRepresentative (A i) y
  have haScalar : AnalyticAt ℂ aScalar 0 := by
    apply AnalyticAt.pi
    intro i
    exact Germ.oneVariableRepresentative_analyticAt (hA i)
  have hAZero (i : Fin (d + 1)) : A i 0 = 0 := by
    have hi := ha i
    rw [Germ.mem_maximalIdeal_iff, hAeq i,
      Germ.valueRingHom_ofFunction] at hi
    exact hi
  have haScalarZero : aScalar 0 = 0 := by
    funext i
    change A i (Germ.oneVariableEquiv.symm 0) = 0
    rw [show Germ.oneVariableEquiv.symm 0 = (0 : Source 1) by
      exact map_zero _]
    exact hAZero i
  obtain ⟨Q, R, hQ, hR, hdivision⟩ :=
    Germ.exists_analytic_generalDivision
      p d hp.radius_pos aScalar haScalar haScalarZero
  have hprojectionOne : AnalyticAt ℂ
      (fun y : Source 1 ↦ y 0) 0 :=
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 1 ↦ ℂ) (0 : Fin 1)).analyticAt 0
  have haScalarSource (i : Fin (d + 1)) : AnalyticAt ℂ
      (fun y : Source 1 ↦ aScalar (y 0) i) 0 := by
    have hcoordinate : AnalyticAt ℂ (fun y ↦ aScalar y i) 0 := by
      simpa [Function.comp_def] using
        (AnalyticAt.comp (x := 0)
          ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt (aScalar 0))
          haScalar)
    exact AnalyticAt.fun_comp
      (f := fun y : Source 1 ↦ y 0) hcoordinate hprojectionOne
  have haLift (i : Fin (d + 1)) :
      a i = Germ.ofFunction
        (fun y : Source 1 ↦ aScalar (y 0) i) (haScalarSource i) := by
    calc
      a i = Germ.ofFunction (A i) (hA i) := hAeq i
      _ = Germ.ofFunction
          (fun y : Source 1 ↦ aScalar (y 0) i)
            (haScalarSource i) := by
        apply Subtype.ext
        exact congrArg (fun H : Source 1 → ℂ ↦ (H : FunctionGerm 1))
          (by simpa [aScalar] using
            (Germ.oneVariableRepresentative_comp_coordinate (A i)).symm)
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
    exact AnalyticAt.fun_comp
      (f := fun z : Source 2 ↦ (z 0, z 1)) hQ hpair
  have hRSource (i : Fin (d + 1)) : AnalyticAt ℂ
      (fun y : Source 1 ↦ R (y 0) i) 0 := by
    have hcoordinate : AnalyticAt ℂ (fun y ↦ R y i) 0 := by
      simpa [Function.comp_def] using
        (AnalyticAt.comp (x := 0)
          ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt (R 0)) hR)
    exact AnalyticAt.fun_comp
      (f := fun y : Source 1 ↦ y 0) hcoordinate hprojectionOne
  let q : Germ 2 := Germ.ofFunction
    (fun z : Source 2 ↦ Q (z 0, z 1)) hQSource
  let r : Fin (d + 1) → Germ 1 := fun i ↦ Germ.ofFunction
    (fun y : Source 1 ↦ R (y 0) i) (hRSource i)
  refine ⟨q, r, ?_⟩
  rw [hf]
  apply Subtype.ext
  let coordinatePair : Source 2 → ℂ × ℂ :=
    ContinuousLinearEquiv.finTwoArrow ℂ ℂ
  have hcoordinatePair : Tendsto coordinatePair
      (nhds 0) (nhds (0, 0)) := by
    change Tendsto coordinatePair (nhds 0) (nhds (0 : ℂ × ℂ))
    have hcontinuous :=
      (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).continuous.continuousAt
        (x := (0 : Source 2))
    simpa only [ContinuousAt, coordinatePair, map_zero] using hcontinuous
  have hdivisionSource := hcoordinatePair.eventually hdivision
  have hpSum : HasFPowerSeriesAt p.sum p 0 :=
    (p.hasFPowerSeriesOnBall hp.radius_pos).hasFPowerSeriesAt
  have hsum : F =ᶠ[nhds 0] p.sum := by
    filter_upwards [hp.eventually_hasSum_sub,
      hpSum.eventually_hasSum_sub] with z hzF hzSum
    simpa only [sub_zero] using hzF.unique hzSum
  let lead : Source 2 → ℂ := fun z ↦ z 0 ^ (d + 1)
  let coefficientTerm : Fin (d + 1) → Source 2 → ℂ := fun i z ↦
    aScalar (z 1) i * z 0 ^ i.1
  let remainderTerm : Fin (d + 1) → Source 2 → ℂ := fun i z ↦
    z 0 ^ i.1 * R (z 1) i
  let quotient : Source 2 → ℂ := fun z ↦ Q (z 0, z 1)
  have hfun : (F : FunctionGerm 2) =
      ((((lead + ∑ i, coefficientTerm i) * quotient +
        ∑ i, remainderTerm i) : Source 2 → ℂ) : FunctionGerm 2) := by
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hsum, hdivisionSource] with z hzSum hzDivision
    dsimp only [lead, coefficientTerm, remainderTerm, quotient]
    simp only [Pi.add_apply, Pi.mul_apply, Finset.sum_apply]
    rw [hzSum]
    simpa only [coordinatePair,
      ContinuousLinearEquiv.finTwoArrow_apply,
      Germ.planePoint_coordinates,
      Germ.generalDivisionPolynomialValue] using hzDivision
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
  have hhyperplaneCoefficient (i : Fin (d + 1)) :
      (((fun z : Source 2 ↦ aScalar (z 1) i) : Source 2 → ℂ) :
          FunctionGerm 2) =
        ((Germ.hyperplaneExtension 1 (a i) : Germ 2) :
          FunctionGerm 2) := by
    rw [haLift i, Germ.hyperplaneExtension_ofFunction]
    rfl
  have hhyperplaneRemainder (i : Fin (d + 1)) :
      (((fun z : Source 2 ↦ R (z 1) i) : Source 2 → ℂ) :
          FunctionGerm 2) =
        ((Germ.hyperplaneExtension 1 (r i) : Germ 2) :
          FunctionGerm 2) := by
    rw [show r i = Germ.ofFunction
        (fun y : Source 1 ↦ R (y 0) i) (hRSource i) by rfl,
      Germ.hyperplaneExtension_ofFunction]
    rfl
  have hcoefficientTerm (i : Fin (d + 1)) :
      ((coefficientTerm i : Source 2 → ℂ) : FunctionGerm 2) =
        ((Germ.hyperplaneExtension 1 (a i) *
            Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
          FunctionGerm 2) := by
    calc
      ((coefficientTerm i : Source 2 → ℂ) : FunctionGerm 2) =
          ((((fun z : Source 2 ↦ aScalar (z 1) i) *
            fun z : Source 2 ↦ z 0 ^ i.1) : Source 2 → ℂ) :
              FunctionGerm 2) := rfl
      _ = (((fun z : Source 2 ↦ aScalar (z 1) i) : FunctionGerm 2) *
          ((fun z : Source 2 ↦ z 0 ^ i.1) : FunctionGerm 2)) :=
        Filter.Germ.coe_mul (l := nhds (0 : Source 2))
          (fun z : Source 2 ↦ aScalar (z 1) i)
          (fun z : Source 2 ↦ z 0 ^ i.1)
      _ = (((Germ.hyperplaneExtension 1 (a i) : Germ 2) :
            FunctionGerm 2) *
          ((Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
            FunctionGerm 2)) := by
        rw [hhyperplaneCoefficient, hcoordinatePow]
      _ = ((Germ.hyperplaneExtension 1 (a i) *
            Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
          FunctionGerm 2) :=
        ((analyticGermSubring 2).subtype.map_mul
          (Germ.hyperplaneExtension 1 (a i))
          (Germ.coordinate (0 : Fin 2) ^ i.1)).symm
  have hremainderTerm (i : Fin (d + 1)) :
      ((remainderTerm i : Source 2 → ℂ) : FunctionGerm 2) =
        ((Germ.coordinate (0 : Fin 2) ^ i.1 *
            Germ.hyperplaneExtension 1 (r i) : Germ 2) :
          FunctionGerm 2) := by
    calc
      ((remainderTerm i : Source 2 → ℂ) : FunctionGerm 2) =
          ((((fun z : Source 2 ↦ z 0 ^ i.1) *
            fun z : Source 2 ↦ R (z 1) i) : Source 2 → ℂ) :
              FunctionGerm 2) := rfl
      _ = (((fun z : Source 2 ↦ z 0 ^ i.1) : FunctionGerm 2) *
          ((fun z : Source 2 ↦ R (z 1) i) : FunctionGerm 2)) :=
        Filter.Germ.coe_mul (l := nhds (0 : Source 2))
          (fun z : Source 2 ↦ z 0 ^ i.1)
          (fun z : Source 2 ↦ R (z 1) i)
      _ = (((Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
            FunctionGerm 2) *
          ((Germ.hyperplaneExtension 1 (r i) : Germ 2) :
            FunctionGerm 2)) := by
        rw [hcoordinatePow, hhyperplaneRemainder]
      _ = ((Germ.coordinate (0 : Fin 2) ^ i.1 *
            Germ.hyperplaneExtension 1 (r i) : Germ 2) :
          FunctionGerm 2) :=
        ((analyticGermSubring 2).subtype.map_mul
          (Germ.coordinate (0 : Fin 2) ^ i.1)
          (Germ.hyperplaneExtension 1 (r i))).symm
  have hcoefficientTerms :
      (((∑ i, coefficientTerm i) : Source 2 → ℂ) : FunctionGerm 2) =
        ((∑ i : Fin (d + 1),
            Germ.hyperplaneExtension 1 (a i) *
              Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
          FunctionGerm 2) := by
    calc
      (((∑ i, coefficientTerm i) : Source 2 → ℂ) : FunctionGerm 2) =
          ∑ i : Fin (d + 1),
            ((coefficientTerm i : Source 2 → ℂ) : FunctionGerm 2) := by
        simpa only using Germ.coe_sum (nhds (0 : Source 2)) ℂ
          coefficientTerm Finset.univ
      _ = ∑ i : Fin (d + 1),
          ((Germ.hyperplaneExtension 1 (a i) *
              Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
            FunctionGerm 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hcoefficientTerm i
      _ = ((∑ i : Fin (d + 1),
            Germ.hyperplaneExtension 1 (a i) *
              Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
          FunctionGerm 2) :=
        (map_sum (analyticGermSubring 2).subtype
          (fun i : Fin (d + 1) ↦
            Germ.hyperplaneExtension 1 (a i) *
              Germ.coordinate (0 : Fin 2) ^ i.1)
          Finset.univ).symm
  have hremainderTerms :
      (((∑ i, remainderTerm i) : Source 2 → ℂ) : FunctionGerm 2) =
        ((∑ i : Fin (d + 1),
            Germ.coordinate (0 : Fin 2) ^ i.1 *
              Germ.hyperplaneExtension 1 (r i) : Germ 2) :
          FunctionGerm 2) := by
    calc
      (((∑ i, remainderTerm i) : Source 2 → ℂ) : FunctionGerm 2) =
          ∑ i : Fin (d + 1),
            ((remainderTerm i : Source 2 → ℂ) : FunctionGerm 2) := by
        simpa only using Germ.coe_sum (nhds (0 : Source 2)) ℂ
          remainderTerm Finset.univ
      _ = ∑ i : Fin (d + 1),
          ((Germ.coordinate (0 : Fin 2) ^ i.1 *
              Germ.hyperplaneExtension 1 (r i) : Germ 2) :
            FunctionGerm 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hremainderTerm i
      _ = ((∑ i : Fin (d + 1),
            Germ.coordinate (0 : Fin 2) ^ i.1 *
              Germ.hyperplaneExtension 1 (r i) : Germ 2) :
          FunctionGerm 2) :=
        (map_sum (analyticGermSubring 2).subtype
          (fun i : Fin (d + 1) ↦
            Germ.coordinate (0 : Fin 2) ^ i.1 *
              Germ.hyperplaneExtension 1 (r i))
          Finset.univ).symm
  have hpolynomial :
      (((lead + ∑ i, coefficientTerm i) : Source 2 → ℂ) :
          FunctionGerm 2) =
        ((Germ.firstCoordinatePolynomialEvaluation
            (Germ.generalWeierstrassPolynomial d a) : Germ 2) :
          FunctionGerm 2) := by
    rw [Germ.firstCoordinatePolynomialEvaluation_generalWeierstrassPolynomial]
    calc
      (((lead + ∑ i, coefficientTerm i) : Source 2 → ℂ) :
          FunctionGerm 2) =
          ((lead : Source 2 → ℂ) : FunctionGerm 2) +
            (((∑ i, coefficientTerm i) : Source 2 → ℂ) :
              FunctionGerm 2) :=
        Filter.Germ.coe_add (l := nhds (0 : Source 2)) lead
          (∑ i, coefficientTerm i)
      _ = ((Germ.coordinate (0 : Fin 2) ^ (d + 1) : Germ 2) :
            FunctionGerm 2) +
          ((∑ i : Fin (d + 1),
              Germ.hyperplaneExtension 1 (a i) *
                Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
            FunctionGerm 2) := by
        rw [show ((lead : Source 2 → ℂ) : FunctionGerm 2) =
            ((Germ.coordinate (0 : Fin 2) ^ (d + 1) : Germ 2) :
              FunctionGerm 2) by exact hcoordinatePow (d + 1),
          hcoefficientTerms]
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
    _ = ((((lead + ∑ i, coefficientTerm i) * quotient +
          ∑ i, remainderTerm i) : Source 2 → ℂ) :
        FunctionGerm 2) := hfun
    _ = (((lead + ∑ i, coefficientTerm i) * quotient :
          Source 2 → ℂ) : FunctionGerm 2) +
        (((∑ i, remainderTerm i) : Source 2 → ℂ) :
          FunctionGerm 2) :=
      Filter.Germ.coe_add (l := nhds (0 : Source 2))
        ((lead + ∑ i, coefficientTerm i) * quotient)
        (∑ i, remainderTerm i)
    _ = (((lead + ∑ i, coefficientTerm i) : Source 2 → ℂ) :
          FunctionGerm 2) *
        ((quotient : Source 2 → ℂ) : FunctionGerm 2) +
        (((∑ i, remainderTerm i) : Source 2 → ℂ) :
          FunctionGerm 2) := by
      rw [Filter.Germ.coe_mul]
    _ = ((Germ.firstCoordinatePolynomialEvaluation
            (Germ.generalWeierstrassPolynomial d a) : Germ 2) :
          FunctionGerm 2) *
        ((q : Germ 2) : FunctionGerm 2) +
        ((∑ i : Fin (d + 1),
            Germ.coordinate (0 : Fin 2) ^ i.1 *
              Germ.hyperplaneExtension 1 (r i) : Germ 2) :
          FunctionGerm 2) := by
      rw [hpolynomial, hremainderTerms]
      rfl
    _ = ((Germ.firstCoordinatePolynomialEvaluation
            (Germ.generalWeierstrassPolynomial d a) * q +
          ∑ i : Fin (d + 1),
            Germ.coordinate (0 : Fin 2) ^ i.1 *
              Germ.hyperplaneExtension 1 (r i) : Germ 2) :
        FunctionGerm 2) := by
      change (analyticGermSubring 2).subtype
            (Germ.firstCoordinatePolynomialEvaluation
              (Germ.generalWeierstrassPolynomial d a)) *
          (analyticGermSubring 2).subtype q +
          (analyticGermSubring 2).subtype
            (∑ i : Fin (d + 1),
              Germ.coordinate (0 : Fin 2) ^ i.1 *
                Germ.hyperplaneExtension 1 (r i)) =
        (analyticGermSubring 2).subtype
          (Germ.firstCoordinatePolynomialEvaluation
              (Germ.generalWeierstrassPolynomial d a) * q +
            ∑ i : Fin (d + 1),
              Germ.coordinate (0 : Fin 2) ^ i.1 *
                Germ.hyperplaneExtension 1 (r i))
      rw [← (analyticGermSubring 2).subtype.map_mul,
        ← (analyticGermSubring 2).subtype.map_add]

/-- The quotient by a monic analytic Weierstrass polynomial is finite over
the one variable coefficient ring. -/
theorem quotient_generalWeierstrassPolynomial_moduleFinite
    (d : ℕ) (a : Fin (d + 1) → Germ 1)
    (ha : ∀ i, a i ∈ Germ.maximalIdeal 1) :
    letI : Algebra (Germ 1) (Germ 2) :=
      (Germ.hyperplaneExtension 1).toAlgebra
    Module.Finite (Germ 1)
      (Germ 2 ⧸ Ideal.span
        {Germ.firstCoordinatePolynomialEvaluation
          (Germ.generalWeierstrassPolynomial d a)}) := by
  let _ : Algebra (Germ 1) (Germ 2) :=
    (Germ.hyperplaneExtension 1).toAlgebra
  let W : Germ 2 := Germ.firstCoordinatePolynomialEvaluation
    (Germ.generalWeierstrassPolynomial d a)
  let I : Ideal (Germ 2) := Ideal.span {W}
  let v : Fin (d + 1) → Germ 2 ⧸ I := fun i ↦
    Ideal.Quotient.mk I (Germ.coordinate (0 : Fin 2) ^ i.1)
  have hspan : Submodule.span (Germ 1) (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro z hz
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨q, r, hdivision⟩ :=
      Germ.exists_generalWeierstrassDivision d a ha f
    rw [hdivision, map_add, map_mul]
    have hW : Ideal.Quotient.mk I W = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton W)
    change Ideal.Quotient.mk I W * Ideal.Quotient.mk I q +
        Ideal.Quotient.mk I
          (∑ i : Fin (d + 1),
            Germ.coordinate (0 : Fin 2) ^ i.1 *
              Germ.hyperplaneExtension 1 (r i)) ∈ _
    rw [hW, zero_mul, zero_add, map_sum]
    apply Submodule.sum_mem
    intro i hi
    rw [map_mul]
    have hvi : v i ∈ Submodule.span (Germ 1) (Set.range v) :=
      Submodule.subset_span (Set.mem_range_self i)
    have hsmul := Submodule.smul_mem
      (Submodule.span (Germ 1) (Set.range v)) (r i) hvi
    have halgebra : algebraMap (Germ 1) (Germ 2 ⧸ I) (r i) =
        Ideal.Quotient.mk I (Germ.hyperplaneExtension 1 (r i)) := rfl
    rw [Algebra.smul_def, halgebra] at hsmul
    rw [mul_comm]
    change Ideal.Quotient.mk I (Germ.hyperplaneExtension 1 (r i)) *
      v i ∈ Submodule.span (Germ 1) (Set.range v)
    exact hsmul
  refine ⟨?_⟩
  rw [← hspan]
  exact Submodule.fg_span (Set.finite_range v)

/-- A monic polynomial is recovered from its coefficients below its stated
degree. -/
theorem eq_generalWeierstrassPolynomial_of_monic_natDegree
    (d : ℕ) (P : Polynomial (Germ 1))
    (hPMonic : P.Monic) (hPDegree : P.natDegree = d + 1) :
    P = Germ.generalWeierstrassPolynomial d
      (fun i : Fin (d + 1) ↦ P.coeff i.1) := by
  apply Polynomial.ext
  intro k
  by_cases hklt : k < d + 1
  · rw [Germ.generalWeierstrassPolynomial_coeff_of_lt d _ k hklt]
  · by_cases hkeq : k = d + 1
    · subst k
      rw [Germ.generalWeierstrassPolynomial_coeff_degree]
      simpa [hPDegree] using hPMonic.coeff_natDegree
    · have hkgt : d + 1 < k := by omega
      rw [Germ.generalWeierstrassPolynomial_coeff_of_degree_lt d _ k hkgt]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt (p := P) (n := k)
      rw [hPDegree]
      exact hkgt

/-- The quotient by any distinguished monic polynomial of positive degree is
finite over the one variable coefficient ring. -/
theorem quotient_monicPolynomial_moduleFinite
    (d : ℕ) (P : Polynomial (Germ 1))
    (hPMonic : P.Monic) (hPDegree : P.natDegree = d + 1)
    (hPCoeff : ∀ k, k < d + 1 →
      P.coeff k ∈ Germ.maximalIdeal 1) :
    letI : Algebra (Germ 1) (Germ 2) :=
      (Germ.hyperplaneExtension 1).toAlgebra
    Module.Finite (Germ 1)
      (Germ 2 ⧸ Ideal.span
        {Germ.firstCoordinatePolynomialEvaluation P}) := by
  let a : Fin (d + 1) → Germ 1 := fun i ↦ P.coeff i.1
  have ha : ∀ i, a i ∈ Germ.maximalIdeal 1 := by
    intro i
    exact hPCoeff i.1 i.2
  have hP : P = Germ.generalWeierstrassPolynomial d a :=
    Germ.eq_generalWeierstrassPolynomial_of_monic_natDegree
      d P hPMonic hPDegree
  rw [hP]
  exact Germ.quotient_generalWeierstrassPolynomial_moduleFinite d a ha

end Germ

end OnLeConjecture.Analytic
