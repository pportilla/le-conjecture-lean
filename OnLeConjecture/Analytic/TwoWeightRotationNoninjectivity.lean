/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TwoWeightRadialExpansion
public import OnLeConjecture.Analytic.Noninjectivity
public import OnLeConjecture.DThree.WeightedResidueRescaling

/-!
# Noninjectivity from persistent rotation zeros with two source weights

Persistent zeros in every chart neighborhood give actual distinct source
points in every neighborhood of the origin. No continuous choice of zeros
is assumed.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.DThree

/-- Persistent rescaled collisions between distinct chart points contradict
injectivity near the origin. Separation may occur in either coordinate. -/
theorem not_neighborhood_injective_of_twoWeightSeparatedChartZeros
    (a b : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x X zeta : ℂ) (ha : 0 < a) (hb : 0 < b) (hseparate : x ≠ X ∨ zeta ≠ 1)
    (hfirst : HasTwoWeightRadialExpansionAt a b degrees initialMap
      representative remainder (x, 1))
    (hsecond : HasTwoWeightRadialExpansionAt a b degrees initialMap
      representative remainder (X, zeta))
    (hpersist : ∀ (U : Set (ℂ × (Fin 3 → ℂ))),
      U ∈ nhds (0, ![x, X, zeta]) →
        ∀ᶠ tau in nhds 0,
          ∃ q : Fin 3 → ℂ,
            (tau, q) ∈ U ∧
              weightedRescaledPerturbation initialMap remainder
                (tau, q) = 0) :
    ¬ ∃ s ∈ nhds (0 : ℂ × ℂ), Set.InjOn representative s := by
  intro hinjective
  obtain ⟨s, hs, hsInjective⟩ := hinjective
  let base : Fin 3 → ℂ := ![x, X, zeta]
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
    have ht := hanalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1, residueFirstChartPoint t.2))
      (nhds (0, base))
      (nhds ((0, base).1, residueFirstChartPoint (0, base).2)) at ht
    simpa [base, residueFirstChartPoint] using ht
  have hsecondLift : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1, residueSecondChartPoint t.2))
      (nhds (0, base)) (nhds (0, (X, zeta))) := by
    have hanalytic : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦
          (t.1, residueSecondChartPoint t.2)) (0, base) :=
      analyticAt_fst.prod
        (AnalyticAt.comp (x := (0, base))
          (analyticAt_residueSecondChartPoint base) analyticAt_snd)
    have ht := hanalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1, residueSecondChartPoint t.2))
      (nhds (0, base))
      (nhds ((0, base).1, residueSecondChartPoint (0, base).2)) at ht
    simpa [base, residueSecondChartPoint] using ht
  have hfirstExpansion := hfirstLift.eventually hfirst.expansion
  have hsecondExpansion := hsecondLift.eventually hsecond.expansion
  have hfirstSourceAnalytic : AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        twoWeightRadialSource a b t.1 (residueFirstChartPoint t.2))
      (0, base) := by
    have hparameter : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦ t.1) (0, base) :=
      analyticAt_fst
    have hcoordinate (i : Fin 3) : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 i) (0, base) :=
      by
        simpa [Function.comp_def] using
          (AnalyticAt.comp (x := (0, base))
            ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt base)
              analyticAt_snd)
    change AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1 ^ a * t.2 0, t.1 ^ b * 1)) (0, base)
    exact ((hparameter.pow a).mul (hcoordinate 0)).prod
      ((hparameter.pow b).mul analyticAt_const)
  have hsecondSourceAnalytic : AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        twoWeightRadialSource a b t.1 (residueSecondChartPoint t.2))
      (0, base) := by
    have hparameter : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦ t.1) (0, base) :=
      analyticAt_fst
    have hcoordinate (i : Fin 3) : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 i) (0, base) :=
      by
        simpa [Function.comp_def] using
          (AnalyticAt.comp (x := (0, base))
            ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt base)
              analyticAt_snd)
    change AnalyticAt ℂ
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        (t.1 ^ a * t.2 1, t.1 ^ b * t.2 2)) (0, base)
    exact ((hparameter.pow a).mul (hcoordinate 1)).prod
      ((hparameter.pow b).mul (hcoordinate 2))
  have hfirstSource : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        twoWeightRadialSource a b t.1 (residueFirstChartPoint t.2))
      (nhds (0, base)) (nhds (0 : ℂ × ℂ)) := by
    have ht := hfirstSourceAnalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        twoWeightRadialSource a b t.1 (residueFirstChartPoint t.2))
      (nhds (0, base))
      (nhds (twoWeightRadialSource a b (0, base).1
        (residueFirstChartPoint (0, base).2))) at ht
    have hvalue : twoWeightRadialSource a b (0, base).1
        (residueFirstChartPoint (0, base).2) = (0 : ℂ × ℂ) := by
      apply Prod.ext
      · simp [base, twoWeightRadialSource, residueFirstChartPoint,
          zero_pow ha.ne', zero_pow hb.ne']
      · simp [base, twoWeightRadialSource, residueFirstChartPoint,
          zero_pow ha.ne', zero_pow hb.ne']
    rw [hvalue] at ht
    exact ht
  have hsecondSource : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        twoWeightRadialSource a b t.1 (residueSecondChartPoint t.2))
      (nhds (0, base)) (nhds (0 : ℂ × ℂ)) := by
    have ht := hsecondSourceAnalytic.continuousAt
    change Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦
        twoWeightRadialSource a b t.1 (residueSecondChartPoint t.2))
      (nhds (0, base))
      (nhds (twoWeightRadialSource a b (0, base).1
        (residueSecondChartPoint (0, base).2))) at ht
    have hvalue : twoWeightRadialSource a b (0, base).1
        (residueSecondChartPoint (0, base).2) = (0 : ℂ × ℂ) := by
      apply Prod.ext
      · simp [base, twoWeightRadialSource, residueSecondChartPoint,
          zero_pow ha.ne', zero_pow hb.ne']
      · simp [base, twoWeightRadialSource, residueSecondChartPoint,
          zero_pow ha.ne', zero_pow hb.ne']
    rw [hvalue] at ht
    exact ht
  have hcoordinate (i : Fin 3) : Tendsto
      (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 i)
      (nhds (0, base)) (nhds (base i)) := by
    have hanalytic : AnalyticAt ℂ
        (fun t : ℂ × (Fin 3 → ℂ) ↦ t.2 i) (0, base) := by
      simpa [Function.comp_def] using
        (AnalyticAt.comp (x := (0, base))
          ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt
            base) analyticAt_snd)
    exact hanalytic.continuousAt
  have hseparated : ∀ᶠ t : ℂ × (Fin 3 → ℂ) in nhds (0, base),
      t.2 0 ≠ t.2 1 ∨ t.2 2 ≠ 1 := by
    rcases hseparate with hxX | hzeta
    · have hdiff := ((hcoordinate 0).sub (hcoordinate 1)).eventually_ne
        (show base 0 - base 1 ≠ 0 by simpa [base, sub_eq_zero] using hxX)
      filter_upwards [hdiff] with t ht
      exact Or.inl (sub_ne_zero.mp ht)
    · have hz := (hcoordinate 2).eventually_ne (by simpa [base] using hzeta)
      filter_upwards [hz] with t ht
      exact Or.inr ht
  let conditions : ℂ × (Fin 3 → ℂ) → Prop := fun t ↦
      (∀ i,
        representative
            (twoWeightRadialSource a b t.1
              (residueFirstChartPoint t.2)) i =
          t.1 ^ degrees i *
            (initialMap (residueFirstChartPoint t.2) i +
              t.1 * remainder (t.1, residueFirstChartPoint t.2) i)) ∧
      (∀ i,
        representative
            (twoWeightRadialSource a b t.1
              (residueSecondChartPoint t.2)) i =
          t.1 ^ degrees i *
            (initialMap (residueSecondChartPoint t.2) i +
              t.1 * remainder (t.1, residueSecondChartPoint t.2) i)) ∧
      twoWeightRadialSource a b t.1 (residueFirstChartPoint t.2) ∈ s ∧
      twoWeightRadialSource a b t.1 (residueSecondChartPoint t.2) ∈ s ∧
      (t.2 0 ≠ t.2 1 ∨ t.2 2 ≠ 1)
  have hconditions : ∀ᶠ t in nhds (0, base), conditions t := by
    filter_upwards [hfirstExpansion, hsecondExpansion,
      hfirstSource.eventually hs, hsecondSource.eventually hs,
      hseparated] with
      t hfirstAt hsecondAt hfirstMem hsecondMem hthirdNe
    exact ⟨hfirstAt, hsecondAt, hfirstMem, hsecondMem, hthirdNe⟩
  have hconditionsSet : {t | conditions t} ∈ nhds (0, base) := by
    change ∀ᶠ t in nhds (0, base), conditions t
    exact hconditions
  have hzero := hpersist {t | conditions t} (by simpa [base] using hconditionsSet)
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
          (twoWeightRadialSource a b tau (residueFirstChartPoint q)) =
        representative
          (twoWeightRadialSource a b tau (residueSecondChartPoint q)) := by
    funext i
    apply sub_eq_zero.mp
    calc
      representative
            (twoWeightRadialSource a b tau (residueFirstChartPoint q)) i -
          representative
            (twoWeightRadialSource a b tau (residueSecondChartPoint q)) i =
        tau ^ degrees i *
          weightedRescaledPerturbation initialMap remainder (tau, q) i :=
        by
          rw [hfirstAt i, hsecondAt i]
          simp only [weightedRescaledPerturbation, weightedInitialDifference,
            weightedChartRemainderDifference, Pi.add_apply, Pi.sub_apply,
            Pi.smul_apply, smul_eq_mul]
          ring
      _ = 0 := by simp [hzeroAt]
  have hsourcesNe :
      twoWeightRadialSource a b tau (residueFirstChartPoint q) ≠
        twoWeightRadialSource a b tau (residueSecondChartPoint q) := by
    intro hequal
    rcases hqNe with hqFirst | hqSecond
    · have hfirstCoordinate := congrArg Prod.fst hequal
      simp only [twoWeightRadialSource, residueFirstChartPoint,
        residueSecondChartPoint] at hfirstCoordinate
      exact hqFirst (mul_left_cancel₀ (pow_ne_zero a htau) hfirstCoordinate)
    · have hsecondCoordinate := congrArg Prod.snd hequal
      simp only [twoWeightRadialSource, residueFirstChartPoint,
        residueSecondChartPoint] at hsecondCoordinate
      have hqOne : q 2 = 1 := by
        apply mul_left_cancel₀ (pow_ne_zero b htau)
        simpa [mul_comm] using hsecondCoordinate.symm
      exact hqSecond hqOne
  exact hsourcesNe (hsInjective hfirstMem hsecondMem hvalues)


/-- Different second coordinates suffice to separate the two chart points. -/
theorem not_neighborhood_injective_of_twoWeightChartZeros
    (a b : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x X zeta : ℂ) (ha : 0 < a) (hb : 0 < b) (hzeta : zeta ≠ 1)
    (hfirst : HasTwoWeightRadialExpansionAt a b degrees initialMap
      representative remainder (x, 1))
    (hsecond : HasTwoWeightRadialExpansionAt a b degrees initialMap
      representative remainder (X, zeta))
    (hpersist : ∀ (U : Set (ℂ × (Fin 3 → ℂ))),
      U ∈ nhds (0, ![x, X, zeta]) →
        ∀ᶠ tau in nhds 0,
          ∃ q : Fin 3 → ℂ,
            (tau, q) ∈ U ∧
              weightedRescaledPerturbation initialMap remainder
                (tau, q) = 0) :
    ¬ ∃ s ∈ nhds (0 : ℂ × ℂ), Set.InjOn representative s :=
  not_neighborhood_injective_of_twoWeightSeparatedChartZeros
    a b degrees initialMap representative remainder x X zeta
    ha hb (Or.inr hzeta) hfirst hsecond hpersist


/-- The rotation specialization has the same first coordinate in both
limiting chart points. -/
theorem not_neighborhood_injective_of_twoWeightRotationZeros
    (a b : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x zeta : ℂ) (ha : 0 < a) (hb : 0 < b) (hzeta : zeta ≠ 1)
    (hfirst : HasTwoWeightRadialExpansionAt a b degrees initialMap
      representative remainder (x, 1))
    (hsecond : HasTwoWeightRadialExpansionAt a b degrees initialMap
      representative remainder (x, zeta))
    (hpersist : ∀ (U : Set (ℂ × (Fin 3 → ℂ))),
      U ∈ nhds (0, ![x, x, zeta]) →
        ∀ᶠ tau in nhds 0,
          ∃ q : Fin 3 → ℂ,
            (tau, q) ∈ U ∧
              weightedRescaledPerturbation initialMap remainder
                (tau, q) = 0) :
    ¬ ∃ s ∈ nhds (0 : ℂ × ℂ), Set.InjOn representative s :=
  not_neighborhood_injective_of_twoWeightChartZeros
    a b degrees initialMap representative remainder x x zeta
    ha hb hzeta hfirst hsecond hpersist

end OnLeConjecture.Analytic
