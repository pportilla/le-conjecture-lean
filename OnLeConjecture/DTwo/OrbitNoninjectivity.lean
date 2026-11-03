/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitCollisionPersistence

/-!
# Noninjectivity from the quadratic orbit collision

Persistent zeros of the rescaled pair difference give distinct source
points with equal representative values in every neighborhood of the origin.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open OnLeConjecture.DThree

/-- Persistent zeros at a distinct limiting pair exclude injectivity on a
neighborhood of the origin. -/
theorem not_neighborhood_injective_of_orbitPairRescaledZeros
    (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (pair : (ℂ × ℂ) × (ℂ × ℂ))
    (hpair : pair.1 ≠ pair.2)
    (hfirst : HasWeightedRadialExpansionAt 1 degrees initialMap
      representative remainder pair.1)
    (hsecond : HasWeightedRadialExpansionAt 1 degrees initialMap
      representative remainder pair.2)
    (hpersist : ∀ U : Set
        (ℂ × ((ℂ × ℂ) × (ℂ × ℂ))),
      U ∈ nhds (0, pair) →
        ∀ᶠ tau in nhds 0,
          ∃ q : (ℂ × ℂ) × (ℂ × ℂ),
            (tau, q) ∈ U ∧
              orbitPairRescaledPerturbation initialMap remainder
                (tau, q) = 0) :
    ¬ ∃ s ∈ nhds (0 : ℂ × ℂ), Set.InjOn representative s := by
  rintro ⟨s, hs, hsInjective⟩
  let base : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) :=
    (0, pair)
  have hfirstLift : Tendsto
      (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        (t.1, t.2.1))
      (nhds base) (nhds (0, pair.1)) := by
    have htau : Tendsto
        (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦ t.1)
        (nhds base) (nhds 0) := by
      simpa [base] using continuous_fst.tendsto base
    have hpoint : Tendsto
        (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦ t.2.1)
        (nhds base) (nhds pair.1) := by
      exact (continuous_fst.tendsto pair).comp
        (continuous_snd.tendsto base)
    exact htau.prodMk_nhds hpoint
  have hsecondLift : Tendsto
      (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        (t.1, t.2.2))
      (nhds base) (nhds (0, pair.2)) := by
    have htau : Tendsto
        (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦ t.1)
        (nhds base) (nhds 0) := by
      simpa [base] using continuous_fst.tendsto base
    have hpoint : Tendsto
        (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦ t.2.2)
        (nhds base) (nhds pair.2) := by
      exact (continuous_snd.tendsto pair).comp
        (continuous_snd.tendsto base)
    exact htau.prodMk_nhds hpoint
  have hfirstExpansion := hfirstLift.eventually hfirst.expansion
  have hsecondExpansion := hsecondLift.eventually hsecond.expansion
  have hfirstSourceAnalytic : AnalyticAt ℂ
      (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        weightedRadialSource 1 t.1 t.2.1) base := by
    have htau : AnalyticAt ℂ
        (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦ t.1) base :=
      analyticAt_fst
    have hpoint : AnalyticAt ℂ
        (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦ t.2.1) base :=
      analyticAt_fst.fun_comp analyticAt_snd
    have hx : AnalyticAt ℂ
        (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦ t.2.1.1) base :=
      analyticAt_fst.fun_comp hpoint
    have hy : AnalyticAt ℂ
        (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦ t.2.1.2) base :=
      analyticAt_snd.fun_comp hpoint
    change AnalyticAt ℂ
      (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        (t.1 ^ 1 * t.2.1.1, t.1 * t.2.1.2)) base
    exact ((htau.pow 1).mul hx).prod (htau.mul hy)
  have hsecondSourceAnalytic : AnalyticAt ℂ
      (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        weightedRadialSource 1 t.1 t.2.2) base := by
    have htau : AnalyticAt ℂ
        (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦ t.1) base :=
      analyticAt_fst
    have hpoint : AnalyticAt ℂ
        (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦ t.2.2) base :=
      analyticAt_snd.fun_comp analyticAt_snd
    have hx : AnalyticAt ℂ
        (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦ t.2.2.1) base :=
      analyticAt_fst.fun_comp hpoint
    have hy : AnalyticAt ℂ
        (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦ t.2.2.2) base :=
      analyticAt_snd.fun_comp hpoint
    change AnalyticAt ℂ
      (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        (t.1 ^ 1 * t.2.2.1, t.1 * t.2.2.2)) base
    exact ((htau.pow 1).mul hx).prod (htau.mul hy)
  have hfirstSource : Tendsto
      (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        weightedRadialSource 1 t.1 t.2.1)
      (nhds base) (nhds (0 : ℂ × ℂ)) := by
    have ht := hfirstSourceAnalytic.continuousAt
    change Tendsto
      (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        weightedRadialSource 1 t.1 t.2.1)
      (nhds base)
      (nhds (weightedRadialSource 1 base.1 base.2.1)) at ht
    have hvalue : weightedRadialSource 1 base.1 base.2.1 =
        (0 : ℂ × ℂ) := by
      apply Prod.ext <;> simp [base, weightedRadialSource]
    rw [hvalue] at ht
    exact ht
  have hsecondSource : Tendsto
      (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        weightedRadialSource 1 t.1 t.2.2)
      (nhds base) (nhds (0 : ℂ × ℂ)) := by
    have ht := hsecondSourceAnalytic.continuousAt
    change Tendsto
      (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        weightedRadialSource 1 t.1 t.2.2)
      (nhds base)
      (nhds (weightedRadialSource 1 base.1 base.2.2)) at ht
    have hvalue : weightedRadialSource 1 base.1 base.2.2 =
        (0 : ℂ × ℂ) := by
      apply Prod.ext <;> simp [base, weightedRadialSource]
    rw [hvalue] at ht
    exact ht
  have hpairProjection : Tendsto
      (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦ t.2)
      (nhds base) (nhds pair) := by
    have ht := continuous_snd.tendsto base
    change Tendsto
      (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦ t.2)
      (nhds base) (nhds base.2) at ht
    simpa [base] using ht
  have hneighborhood :
      {q : (ℂ × ℂ) × (ℂ × ℂ) | q.1 ≠ q.2} ∈
        nhds pair :=
    isOpen_ne_fun continuous_fst continuous_snd |>.mem_nhds hpair
  have hpairsNe : ∀ᶠ t in nhds base, t.2.1 ≠ t.2.2 :=
    hpairProjection.eventually hneighborhood
  let conditions :
      ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) → Prop := fun t ↦
    (∀ i,
      representative (weightedRadialSource 1 t.1 t.2.1) i =
        t.1 ^ degrees i *
          (initialMap t.2.1 i + t.1 * remainder (t.1, t.2.1) i)) ∧
    (∀ i,
      representative (weightedRadialSource 1 t.1 t.2.2) i =
        t.1 ^ degrees i *
          (initialMap t.2.2 i + t.1 * remainder (t.1, t.2.2) i)) ∧
    weightedRadialSource 1 t.1 t.2.1 ∈ s ∧
    weightedRadialSource 1 t.1 t.2.2 ∈ s ∧
    t.2.1 ≠ t.2.2
  have hconditions : ∀ᶠ t in nhds base, conditions t := by
    filter_upwards [hfirstExpansion, hsecondExpansion,
      hfirstSource.eventually hs, hsecondSource.eventually hs,
      hpairsNe] with t hfirstAt hsecondAt hfirstMem hsecondMem hne
    exact ⟨hfirstAt, hsecondAt, hfirstMem, hsecondMem, hne⟩
  have hconditionsSet : {t | conditions t} ∈ nhds base := by
    change ∀ᶠ t in nhds base, conditions t
    exact hconditions
  have hzero := hpersist {t | conditions t}
    (by simpa [base] using hconditionsSet)
  have hall : ∀ᶠ tau in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
      ∃ q : (ℂ × ℂ) × (ℂ × ℂ),
        conditions (tau, q) ∧
        orbitPairRescaledPerturbation initialMap remainder (tau, q) = 0 ∧
        tau ≠ 0 := by
    filter_upwards [hzero.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with tau htau htauMem
    obtain ⟨q, hcondition, hzeroAt⟩ := htau
    refine ⟨q, hcondition, hzeroAt, ?_⟩
    simpa using htauMem
  obtain ⟨tau, q, hcondition, hzeroAt, htau⟩ := hall.exists
  obtain ⟨hfirstAt, hsecondAt, hfirstMem, hsecondMem, hqNe⟩ :=
    hcondition
  have hvalues :
      representative (weightedRadialSource 1 tau q.1) =
        representative (weightedRadialSource 1 tau q.2) := by
    funext i
    apply sub_eq_zero.mp
    calc
      representative (weightedRadialSource 1 tau q.1) i -
          representative (weightedRadialSource 1 tau q.2) i =
        tau ^ degrees i *
          orbitPairRescaledPerturbation initialMap remainder
            (tau, q) i :=
        representative_difference_eq_orbitPairRescaledPerturbation
          degrees initialMap representative remainder tau q
            hfirstAt hsecondAt i
      _ = 0 := by simp [hzeroAt]
  have hsourcesNe :
      weightedRadialSource 1 tau q.1 ≠
        weightedRadialSource 1 tau q.2 := by
    intro hequal
    apply hqNe
    apply Prod.ext
    · have h := congrArg Prod.fst hequal
      simp only [weightedRadialSource, pow_one] at h
      exact mul_left_cancel₀ htau h
    · have h := congrArg Prod.snd hequal
      simp only [weightedRadialSource] at h
      exact mul_left_cancel₀ htau h
  exact hsourcesNe (hsInjective hfirstMem hsecondMem hvalues)

/-- The finite chart collision excludes injectivity on every neighborhood
of the origin. -/
theorem not_neighborhood_injective_of_orbitFiniteChartCollision
    {delta : ℂ} (hdelta : delta ^ 2 = 3)
    {R : OrbitSourceForm} {r : ℕ}
    (data : OrbitFiniteChartCollisionData delta R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : HasWeightedRadialExpansionAt 1 (orbitInitialDegrees r)
      (weightedPolynomialMap (orbitInitialPolynomialMap R))
      representative remainder
        (orbitFiniteChartPair delta data.parameter).1)
    (hsecond : HasWeightedRadialExpansionAt 1 (orbitInitialDegrees r)
      (weightedPolynomialMap (orbitInitialPolynomialMap R))
      representative remainder
        (orbitFiniteChartPair delta data.parameter).2) :
    ¬ ∃ s ∈ nhds (0 : ℂ × ℂ), Set.InjOn representative s := by
  apply not_neighborhood_injective_of_orbitPairRescaledZeros
    (orbitInitialDegrees r)
    (weightedPolynomialMap (orbitInitialPolynomialMap R))
      representative remainder
        (orbitFiniteChartPair delta data.parameter)
          data.first_ne_second hfirst hsecond
  intro U hU
  exact eventually_exists_orbitPairRescaledZero_mem_nhds
    hdelta data remainder hfirst.remainder_analyticAt
      hsecond.remainder_analyticAt U hU

/-- The finite chart collision excludes an injective representative of the
associated pointed map germ. -/
theorem orbitFiniteChartCollision_not_hasInjectiveRepresentative
    {delta : ℂ} (hdelta : delta ^ 2 = 3)
    {R : OrbitSourceForm} {r : ℕ}
    (data : OrbitFiniteChartCollisionData delta R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (hfirst : HasWeightedRadialExpansionAt 1 (orbitInitialDegrees r)
      (weightedPolynomialMap (orbitInitialPolynomialMap R))
      representative remainder
        (orbitFiniteChartPair delta data.parameter).1)
    (hsecond : HasWeightedRadialExpansionAt 1 (orbitInitialDegrees r)
      (weightedPolynomialMap (orbitInitialPolynomialMap R))
      representative remainder
        (orbitFiniteChartPair delta data.parameter).2) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  exact not_neighborhood_injective_of_orbitFiniteChartCollision
    hdelta data representative remainder hfirst hsecond

/-- An algebraic isolation certificate and weighted order tails exclude an
injective representative. -/
theorem orbitWeightedOrderTails_not_hasInjectiveRepresentative
    {delta : ℂ} (hdelta : delta ^ 2 = 3)
    {R : OrbitSourceForm} {r : ℕ}
    (hR : R.IsHomogeneous r)
    (hcertificate : OrbitAlgebraicIsolationCertificate delta R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (orbitInitialPolynomialMap R i) ∈
        Germ.weightedOrderIdeal 1 (orbitInitialDegrees r i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨data⟩ := exists_orbitFiniteChartCollisionData
    hdelta hR hcertificate
  obtain ⟨remainder, hexpansion⟩ :=
    exists_orbitWeightedRadialExpansion hR representative hanalytic htail
  exact orbitFiniteChartCollision_not_hasInjectiveRepresentative
    hdelta data representative remainder hanalytic hzero
      (hexpansion (orbitFiniteChartPair delta data.parameter).1)
      (hexpansion (orbitFiniteChartPair delta data.parameter).2)

/-- The hypotheses of the quadratic orbit lemma and weighted order tails
exclude an injective representative. -/
theorem orbitHomogeneousWeightedOrderTails_not_hasInjectiveRepresentative
    {R : OrbitSourceForm} {r : ℕ}
    (hR : R.IsHomogeneous r) (hr : 4 ≤ r)
    (hdivides : orbitPolynomialLambda ℂ ^ 4 ∣ R)
    (hnotBase : R ∉ Set.range (orbitBaseToSource ℂ))
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (orbitInitialPolynomialMap R i) ∈
        Germ.weightedOrderIdeal 1 (orbitInitialDegrees r i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨-, delta, hdelta, hcertificate⟩ :=
    hasOrbitCollision_and_exists_certificate hR hr hdivides hnotBase
  exact orbitWeightedOrderTails_not_hasInjectiveRepresentative
    hdelta hR hcertificate representative hanalytic hzero htail

end OnLeConjecture.DTwo
