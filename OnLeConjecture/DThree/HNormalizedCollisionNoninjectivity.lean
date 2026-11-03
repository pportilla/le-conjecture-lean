/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HNormalizedCollisionBranch
public import OnLeConjecture.DThree.HRegularProfileNoninjectivity

/-!
# Noninjectivity from a normalized H collision

The two limiting chart points may differ in either source coordinate.  A
persistent zero of the rescaled difference then contradicts injectivity on
every neighborhood of the origin.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- The rescaled perturbation has a zero in every neighborhood of a
normalized collision. -/
theorem eventually_exists_hWeightedNormalizedZero_mem_nhds
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (data : HNormalizedSourceBranchData a N R)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder
      (0, (data.firstX 0, 1)))
    (hsecond : AnalyticAt ℂ remainder
      (0, (data.secondX, data.secondT)))
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds
      (0, ![data.firstX 0, data.secondX, data.secondT])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          weightedRescaledPerturbation
            (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R))
              remainder (tau, point) = 0 := by
  let initialMap :=
    weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R)
  let Phi := weightedRescaledPerturbation initialMap remainder
  have hPhi : AnalyticAt ℂ Phi
      (0, ![data.firstX 0, data.secondX, data.secondT]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_hQuadratic a R _
    · simpa [residueFirstChartPoint] using hfirst
    · simpa [residueSecondChartPoint] using hsecond
  exact eventually_exists_hCollisionZero_mem_nhds_of_explicit_branch
    Phi a ha data.firstX data.secondPoint data.secondX data.secondT
      data.firstX_analyticAt data.secondPoint_analyticAt
        data.secondPoint_zero data.secondT_ne_zero hPhi
      (hCollisionPlanePart_weightedRescaledPerturbation_zero
        a R remainder data.firstX)
      data.plane_zero
      (fun q : ℂ × (Fin 2 → ℂ) ↦
        hFormEval (data.firstX q.1) 1 R -
          hFormEval (q.2 0) (q.2 1 ^ (2 * a)) R)
      (hCollisionThirdPart_weightedRescaledPerturbation_zero
        a R remainder data.firstX)
      data.order data.unit data.order_pos data.unit_analyticAt
        data.unit_zero_ne data.third_factor U hU

/-- Persistent rescaled zeros based at distinct chart points contradict
injectivity near the origin. -/
theorem not_neighborhood_injective_of_weightedZeros_at_distinct_chart
    (a : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x X T : ℂ) (ha : 0 < a) (hchart : (x, 1) ≠ (X, T))
    (hfirst : HasWeightedRadialExpansionAt a degrees initialMap
      representative remainder (x, 1))
    (hsecond : HasWeightedRadialExpansionAt a degrees initialMap
      representative remainder (X, T))
    (hpersist : ∀ (U : Set (ℂ × (Fin 3 → ℂ))),
      U ∈ nhds (0, ![x, X, T]) →
        ∀ᶠ tau in nhds 0,
          ∃ q : Fin 3 → ℂ,
            (tau, q) ∈ U ∧
              weightedRescaledPerturbation initialMap remainder
                (tau, q) = 0) :
    ¬ ∃ sourceSet ∈ nhds (0 : ℂ × ℂ),
      Set.InjOn representative sourceSet := by
  intro hinjective
  obtain ⟨sourceSet, hsourceSet, hsourceInjective⟩ := hinjective
  let base : Fin 3 → ℂ := ![x, X, T]
  have hfirstLift : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1, residueFirstChartPoint t.2))
      (nhds (0, base)) (nhds (0, (x, 1))) := by
    have hanalytic : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦
          (t.1, residueFirstChartPoint t.2)) (0, base) :=
      analyticAt_fst.prod
        (AnalyticAt.comp (x := (0, base))
          (analyticAt_residueFirstChartPoint base) analyticAt_snd)
    have htendsto := hanalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1, residueFirstChartPoint t.2))
      (nhds (0, base))
      (nhds ((0, base).1, residueFirstChartPoint (0, base).2)) at htendsto
    simpa [base, residueFirstChartPoint] using htendsto
  have hsecondLift : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1, residueSecondChartPoint t.2))
      (nhds (0, base)) (nhds (0, (X, T))) := by
    have hanalytic : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦
          (t.1, residueSecondChartPoint t.2)) (0, base) :=
      analyticAt_fst.prod
        (AnalyticAt.comp (x := (0, base))
          (analyticAt_residueSecondChartPoint base) analyticAt_snd)
    have htendsto := hanalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1, residueSecondChartPoint t.2))
      (nhds (0, base))
      (nhds ((0, base).1, residueSecondChartPoint (0, base).2)) at htendsto
    simpa [base, residueSecondChartPoint] using htendsto
  have hfirstExpansion := hfirstLift.eventually hfirst.expansion
  have hsecondExpansion := hsecondLift.eventually hsecond.expansion
  have hfirstSourceAnalytic : AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a t.1 (residueFirstChartPoint t.2))
      (0, base) := by
    have hparameter : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦ t.1) (0, base) :=
      analyticAt_fst
    have hcoordinate (i : Fin 3) : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 i) (0, base) := by
      simpa [Function.comp_def] using
        (AnalyticAt.comp (x := (0, base))
          ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt base)
            analyticAt_snd)
    change AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1 ^ a * t.2 0, t.1 * 1)) (0, base)
    exact ((hparameter.pow a).mul (hcoordinate 0)).prod
      (hparameter.mul analyticAt_const)
  have hsecondSourceAnalytic : AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a t.1 (residueSecondChartPoint t.2))
      (0, base) := by
    have hparameter : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦ t.1) (0, base) :=
      analyticAt_fst
    have hcoordinate (i : Fin 3) : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 i) (0, base) := by
      simpa [Function.comp_def] using
        (AnalyticAt.comp (x := (0, base))
          ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt base)
            analyticAt_snd)
    change AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1 ^ a * t.2 1, t.1 * t.2 2)) (0, base)
    exact ((hparameter.pow a).mul (hcoordinate 1)).prod
      (hparameter.mul (hcoordinate 2))
  have hfirstSource : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a t.1 (residueFirstChartPoint t.2))
      (nhds (0, base)) (nhds (0 : ℂ × ℂ)) := by
    have htendsto := hfirstSourceAnalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a t.1 (residueFirstChartPoint t.2))
      (nhds (0, base))
      (nhds (weightedRadialSource a (0, base).1
        (residueFirstChartPoint (0, base).2))) at htendsto
    have hvalue : weightedRadialSource a (0, base).1
        (residueFirstChartPoint (0, base).2) = (0 : ℂ × ℂ) := by
      apply Prod.ext
      · simp [base, weightedRadialSource, residueFirstChartPoint,
          zero_pow ha.ne']
      · simp [base, weightedRadialSource, residueFirstChartPoint,
          zero_pow ha.ne']
    rw [hvalue] at htendsto
    exact htendsto
  have hsecondSource : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a t.1 (residueSecondChartPoint t.2))
      (nhds (0, base)) (nhds (0 : ℂ × ℂ)) := by
    have htendsto := hsecondSourceAnalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a t.1 (residueSecondChartPoint t.2))
      (nhds (0, base))
      (nhds (weightedRadialSource a (0, base).1
        (residueSecondChartPoint (0, base).2))) at htendsto
    have hvalue : weightedRadialSource a (0, base).1
        (residueSecondChartPoint (0, base).2) = (0 : ℂ × ℂ) := by
      apply Prod.ext
      · simp [base, weightedRadialSource, residueSecondChartPoint,
          zero_pow ha.ne']
      · simp [base, weightedRadialSource, residueSecondChartPoint,
          zero_pow ha.ne']
    rw [hvalue] at htendsto
    exact htendsto
  have hbaseDifference : (x - X, 1 - T) ≠ (0 : ℂ × ℂ) := by
    intro hzero
    apply hchart
    apply Prod.ext
    · exact sub_eq_zero.mp (congrArg Prod.fst hzero)
    · exact sub_eq_zero.mp (congrArg Prod.snd hzero)
  have hchartDifference : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.2 0 - t.2 1, 1 - t.2 2))
      (nhds (0, base)) (nhds (x - X, 1 - T)) := by
    have hcoordinate (i : Fin 3) : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 i) (0, base) := by
      simpa [Function.comp_def] using
        (AnalyticAt.comp (x := (0, base))
          ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt base)
            analyticAt_snd)
    have hanalytic : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦
          (t.2 0 - t.2 1, 1 - t.2 2)) (0, base) :=
      ((hcoordinate 0).sub (hcoordinate 1)).prod
        (analyticAt_const.sub (hcoordinate 2))
    have htendsto := hanalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.2 0 - t.2 1, 1 - t.2 2))
      (nhds (0, base))
      (nhds ((0, base).2 0 - (0, base).2 1,
        1 - (0, base).2 2)) at htendsto
    simpa [base] using htendsto
  let conditions : ℂ × (Fin 3 → ℂ) → Prop := fun t ↦
      (∀ i,
        representative
            (weightedRadialSource a t.1
              (residueFirstChartPoint t.2)) i =
          t.1 ^ degrees i *
            (initialMap (residueFirstChartPoint t.2) i +
              t.1 * remainder (t.1, residueFirstChartPoint t.2) i)) ∧
      (∀ i,
        representative
            (weightedRadialSource a t.1
              (residueSecondChartPoint t.2)) i =
          t.1 ^ degrees i *
            (initialMap (residueSecondChartPoint t.2) i +
              t.1 * remainder (t.1, residueSecondChartPoint t.2) i)) ∧
      weightedRadialSource a t.1 (residueFirstChartPoint t.2) ∈ sourceSet ∧
      weightedRadialSource a t.1 (residueSecondChartPoint t.2) ∈ sourceSet ∧
      (t.2 0, 1) ≠ (t.2 1, t.2 2)
  have hconditions : ∀ᶠ t in nhds (0, base), conditions t := by
    filter_upwards [hfirstExpansion, hsecondExpansion,
      hfirstSource.eventually hsourceSet, hsecondSource.eventually hsourceSet,
      hchartDifference.eventually_ne hbaseDifference] with
      t hfirstAt hsecondAt hfirstMem hsecondMem hdifference
    refine ⟨hfirstAt, hsecondAt, hfirstMem, hsecondMem, ?_⟩
    intro hequal
    apply hdifference
    apply Prod.ext
    · exact sub_eq_zero.mpr (congrArg Prod.fst hequal)
    · exact sub_eq_zero.mpr (congrArg Prod.snd hequal)
  have hconditionsSet : {t | conditions t} ∈ nhds (0, base) := by
    change ∀ᶠ t in nhds (0, base), conditions t
    exact hconditions
  have hzero := hpersist {t | conditions t}
    (by simpa [base] using hconditionsSet)
  have hall : ∀ᶠ tau in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
      ∃ q : Fin 3 → ℂ,
        conditions (tau, q) ∧
        weightedRescaledPerturbation initialMap remainder (tau, q) = 0 ∧
        tau ≠ 0 := by
    filter_upwards [hzero.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with tau htau htauMem
    obtain ⟨q, hcondition, hzeroAt⟩ := htau
    refine ⟨q, hcondition, hzeroAt, ?_⟩
    simpa using htauMem
  obtain ⟨tau, q, hcondition, hzeroAt, htau⟩ := hall.exists
  obtain ⟨hfirstAt, hsecondAt, hfirstMem, hsecondMem, hqNe⟩ := hcondition
  have hvalues :
      representative
          (weightedRadialSource a tau (residueFirstChartPoint q)) =
        representative
          (weightedRadialSource a tau (residueSecondChartPoint q)) := by
    funext i
    apply sub_eq_zero.mp
    calc
      representative
            (weightedRadialSource a tau (residueFirstChartPoint q)) i -
          representative
            (weightedRadialSource a tau (residueSecondChartPoint q)) i =
        tau ^ degrees i *
          weightedRescaledPerturbation initialMap remainder (tau, q) i :=
        representative_difference_eq_weightedRescaledPerturbation
          a degrees initialMap representative remainder tau q
            hfirstAt hsecondAt i
      _ = 0 := by simp [hzeroAt]
  have hsourcesNe :
      weightedRadialSource a tau (residueFirstChartPoint q) ≠
        weightedRadialSource a tau (residueSecondChartPoint q) := by
    intro hequal
    apply hqNe
    apply Prod.ext
    · have hfirstCoordinate := congrArg Prod.fst hequal
      simp only [weightedRadialSource, residueFirstChartPoint,
        residueSecondChartPoint] at hfirstCoordinate
      exact mul_left_cancel₀ (pow_ne_zero a htau) hfirstCoordinate
    · have hsecondCoordinate := congrArg Prod.snd hequal
      simp only [weightedRadialSource, residueFirstChartPoint,
        residueSecondChartPoint] at hsecondCoordinate
      exact mul_left_cancel₀ htau hsecondCoordinate
  exact hsourcesNe
    (hsourceInjective hfirstMem hsecondMem hvalues)

/-- A normalized H collision excludes injectivity on every neighborhood of
the origin. -/
theorem not_neighborhood_injective_of_hWeightedNormalizedCollision
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (data : HNormalizedSourceBranchData a N R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : HasWeightedRadialExpansionAt a
      (hQuadraticWeightedDegrees a N)
      (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R))
        representative remainder (data.firstX 0, 1))
    (hsecond : HasWeightedRadialExpansionAt a
      (hQuadraticWeightedDegrees a N)
      (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R))
        representative remainder (data.secondX, data.secondT)) :
    ¬ ∃ sourceSet ∈ nhds (0 : ℂ × ℂ),
      Set.InjOn representative sourceSet := by
  apply not_neighborhood_injective_of_weightedZeros_at_distinct_chart
    a (hQuadraticWeightedDegrees a N)
      (weightedPolynomialMap (hQuadraticWeightedPolynomialMap a R))
        representative remainder (data.firstX 0) data.secondX
          data.secondT ha data.chart_points_ne hfirst hsecond
  intro U hU
  exact eventually_exists_hWeightedNormalizedZero_mem_nhds
    a N ha R data remainder hfirst.remainder_analyticAt
      hsecond.remainder_analyticAt U hU

/-- Weighted order tails exclude an injective representative at a normalized
H collision. -/
theorem hNormalizedWeightedOrderTails_not_hasInjectiveRepresentative
    (a N : ℕ) (ha : 0 < a)
    (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous hFormWeight N)
    (data : HNormalizedSourceBranchData a N R)
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
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
      a ha (hQuadraticWeightedDegrees a N)
        (hQuadraticWeightedPolynomialMap a R)
          (hQuadraticWeightedPolynomialMap_isWeightedHomogeneous a N R hR)
            representative hanalytic htail
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  exact not_neighborhood_injective_of_hWeightedNormalizedCollision
    a N ha R data representative remainder
      (hexpansion (data.firstX 0, 1))
      (hexpansion (data.secondX, data.secondT))

end OnLeConjecture.DThree
