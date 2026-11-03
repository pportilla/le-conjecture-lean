/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EInvariantRegularPersistence
public import OnLeConjecture.DThree.WeightedOrderExpansion

/-!
# Noninjectivity from a regular invariant E collision

A persistent zero of the rescaled difference yields equal values of the
original representative at distinct source points.  The two source points
are distinguished by their first coordinates.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Persistent rescaled zeros based at two chart points with distinct first
coordinates contradict injectivity near the origin. -/
theorem not_neighborhood_injective_of_weightedZeros_at_distinct_first
    (a : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x X T : ℂ) (ha : 0 < a) (hxX : x ≠ X)
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
    ¬ ∃ s ∈ nhds (0 : ℂ × ℂ), Set.InjOn representative s := by
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
  have hfirstDifference : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 0 - t.2 1)
      (nhds (0, base)) (nhds (x - X)) := by
    have hanalytic : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 0 - t.2 1)
        (0, base) := by
      have hcoordinate (i : Fin 3) : AnalyticAt ℂ
          (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 i) (0, base) := by
        simpa [Function.comp_def] using
          (AnalyticAt.comp (x := (0, base))
            ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt base)
              analyticAt_snd)
      exact (hcoordinate 0).sub (hcoordinate 1)
    have htendsto := hanalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 0 - t.2 1)
      (nhds (0, base)) (nhds ((0, base).2 0 - (0, base).2 1)) at htendsto
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
      t.2 0 ≠ t.2 1
  have hconditions : ∀ᶠ t in nhds (0, base), conditions t := by
    filter_upwards [hfirstExpansion, hsecondExpansion,
      hfirstSource.eventually hsourceSet, hsecondSource.eventually hsourceSet,
      hfirstDifference.eventually_ne (sub_ne_zero.mpr hxX)] with
      t hfirstAt hsecondAt hfirstMem hsecondMem hdifference
    exact ⟨hfirstAt, hsecondAt, hfirstMem, hsecondMem,
      sub_ne_zero.mp hdifference⟩
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
    have hfirstCoordinate := congrArg Prod.fst hequal
    simp only [weightedRadialSource, residueFirstChartPoint,
      residueSecondChartPoint] at hfirstCoordinate
    have hqEqual : q 0 = q 1 := by
      exact mul_left_cancel₀ (pow_ne_zero a htau) hfirstCoordinate
    exact hqNe hqEqual
  exact hsourcesNe
    (hsourceInjective hfirstMem hsecondMem hvalues)

/-- A regular invariant `E` collision excludes injectivity of the original
representative on every neighborhood of the origin. -/
theorem not_neighborhood_injective_of_eWeightedInvariantRegularCollision
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ) (n N : ℕ)
    (z s g : ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : HasWeightedRadialExpansionAt 1 (eInvariantDegrees N)
      (weightedPolynomialMap (eInvariantPolynomialMap R))
        representative remainder (s * z, 1))
    (hsecond : HasWeightedRadialExpansionAt 1 (eInvariantDegrees N)
      (weightedPolynomialMap (eInvariantPolynomialMap R))
        representative remainder (s, g))
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (hhomogeneous : EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (hp : ePairDehomogenize (eThetaPolynomial ℂ c) ≠ 0)
    (hzRoot :
      (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z)
    (hzOne : z ≠ 1)
    (hs : s ^ 3 * eResidualW z 1 = 1)
    (hg : g ^ 3 = s ^ 3 * eResidualW 1 z)
    (hW : eResidualW 1 z ≠ 0) :
    ¬ ∃ sourceSet ∈ nhds (0 : ℂ × ℂ),
      Set.InjOn representative sourceSet := by
  have hsNe : s ≠ 0 := by
    intro hsZero
    simp [hsZero] at hs
  have hdistinct : s * z ≠ s := by
    intro hequal
    apply hzOne
    apply mul_left_cancel₀ hsNe
    simpa using hequal
  apply not_neighborhood_injective_of_weightedZeros_at_distinct_first
    1 (eInvariantDegrees N)
      (weightedPolynomialMap (eInvariantPolynomialMap R))
        representative remainder (s * z) s g (by simp) hdistinct
          hfirst hsecond
  intro U hU
  exact eventually_exists_eWeightedInvariantRegularZero_mem_nhds
    Rzero R c n z s g remainder hfirst.remainder_analyticAt
      hsecond.remainder_analyticAt hdescent hdecomposition hhomogeneous hp
        hzRoot hzOne hs hg hW U hU

/-- A regular invariant `E` collision excludes an injective representative
of the corresponding pointed map germ. -/
theorem eWeightedInvariantRegularCollision_not_hasInjectiveRepresentative
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ) (n N : ℕ)
    (z s g : ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (hfirst : HasWeightedRadialExpansionAt 1 (eInvariantDegrees N)
      (weightedPolynomialMap (eInvariantPolynomialMap R))
        representative remainder (s * z, 1))
    (hsecond : HasWeightedRadialExpansionAt 1 (eInvariantDegrees N)
      (weightedPolynomialMap (eInvariantPolynomialMap R))
        representative remainder (s, g))
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (hhomogeneous : EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (hp : ePairDehomogenize (eThetaPolynomial ℂ c) ≠ 0)
    (hzRoot :
      (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z)
    (hzOne : z ≠ 1)
    (hs : s ^ 3 * eResidualW z 1 = 1)
    (hg : g ^ 3 = s ^ 3 * eResidualW 1 z)
    (hW : eResidualW 1 z ≠ 0) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  exact not_neighborhood_injective_of_eWeightedInvariantRegularCollision
    Rzero R c n N z s g representative remainder hfirst hsecond
      hdescent hdecomposition hhomogeneous hp hzRoot hzOne hs hg hW

end OnLeConjecture.DThree
