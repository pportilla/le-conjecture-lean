/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitNoninjectivity

/-!
# Persistent collisions of arbitrary weighted source pairs

Both source points may vary without normalizing a source coordinate to one.
The first radial weight is any positive integer. Thus this criterion also
applies to pairs obtained by finite ramification of an orbit collision.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic DThree

/-- Radial expansion converts the representative difference into the
rescaled pair perturbation. -/
theorem representative_difference_eq_weightedPairRescaledPerturbation
    (a : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (tau : ℂ) (pair : (ℂ × ℂ) × (ℂ × ℂ))
    (hfirst : ∀ i,
      representative (weightedRadialSource a tau pair.1) i =
        tau ^ degrees i *
          (initialMap pair.1 i + tau * remainder (tau, pair.1) i))
    (hsecond : ∀ i,
      representative (weightedRadialSource a tau pair.2) i =
        tau ^ degrees i *
          (initialMap pair.2 i + tau * remainder (tau, pair.2) i)) :
    ∀ i,
      representative (weightedRadialSource a tau pair.1) i -
          representative (weightedRadialSource a tau pair.2) i =
        tau ^ degrees i *
          orbitPairRescaledPerturbation initialMap remainder (tau, pair) i := by
  intro i
  rw [hfirst i, hsecond i]
  simp only [orbitPairRescaledPerturbation, orbitPairInitialDifference,
    orbitPairRemainderDifference, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring


/-- Persistent zeros at a distinct limiting pair exclude injectivity on a
neighborhood of the origin. -/
theorem not_neighborhood_injective_of_weightedPairRescaledZeros
    (a : ℕ) (ha : 0 < a) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (pair : (ℂ × ℂ) × (ℂ × ℂ))
    (hpair : pair.1 ≠ pair.2)
    (hfirst : HasWeightedRadialExpansionAt a degrees initialMap
      representative remainder pair.1)
    (hsecond : HasWeightedRadialExpansionAt a degrees initialMap
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
        weightedRadialSource a t.1 t.2.1) base := by
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
        (t.1 ^ a * t.2.1.1, t.1 * t.2.1.2)) base
    exact ((htau.pow a).mul hx).prod (htau.mul hy)
  have hsecondSourceAnalytic : AnalyticAt ℂ
      (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        weightedRadialSource a t.1 t.2.2) base := by
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
        (t.1 ^ a * t.2.2.1, t.1 * t.2.2.2)) base
    exact ((htau.pow a).mul hx).prod (htau.mul hy)
  have hfirstSource : Tendsto
      (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        weightedRadialSource a t.1 t.2.1)
      (nhds base) (nhds (0 : ℂ × ℂ)) := by
    have ht := hfirstSourceAnalytic.continuousAt
    change Tendsto
      (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        weightedRadialSource a t.1 t.2.1)
      (nhds base)
      (nhds (weightedRadialSource a base.1 base.2.1)) at ht
    have hvalue : weightedRadialSource a base.1 base.2.1 =
        (0 : ℂ × ℂ) := by
      apply Prod.ext <;> simp [base, weightedRadialSource, zero_pow ha.ne']
    rw [hvalue] at ht
    exact ht
  have hsecondSource : Tendsto
      (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        weightedRadialSource a t.1 t.2.2)
      (nhds base) (nhds (0 : ℂ × ℂ)) := by
    have ht := hsecondSourceAnalytic.continuousAt
    change Tendsto
      (fun t : ℂ × ((ℂ × ℂ) × (ℂ × ℂ)) ↦
        weightedRadialSource a t.1 t.2.2)
      (nhds base)
      (nhds (weightedRadialSource a base.1 base.2.2)) at ht
    have hvalue : weightedRadialSource a base.1 base.2.2 =
        (0 : ℂ × ℂ) := by
      apply Prod.ext <;> simp [base, weightedRadialSource, zero_pow ha.ne']
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
      representative (weightedRadialSource a t.1 t.2.1) i =
        t.1 ^ degrees i *
          (initialMap t.2.1 i + t.1 * remainder (t.1, t.2.1) i)) ∧
    (∀ i,
      representative (weightedRadialSource a t.1 t.2.2) i =
        t.1 ^ degrees i *
          (initialMap t.2.2 i + t.1 * remainder (t.1, t.2.2) i)) ∧
    weightedRadialSource a t.1 t.2.1 ∈ s ∧
    weightedRadialSource a t.1 t.2.2 ∈ s ∧
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
      representative (weightedRadialSource a tau q.1) =
        representative (weightedRadialSource a tau q.2) := by
    funext i
    apply sub_eq_zero.mp
    calc
      representative (weightedRadialSource a tau q.1) i -
          representative (weightedRadialSource a tau q.2) i =
        tau ^ degrees i *
          orbitPairRescaledPerturbation initialMap remainder
            (tau, q) i :=
        representative_difference_eq_weightedPairRescaledPerturbation
          a degrees initialMap representative remainder tau q
            hfirstAt hsecondAt i
      _ = 0 := by simp [hzeroAt]
  have hsourcesNe :
      weightedRadialSource a tau q.1 ≠
        weightedRadialSource a tau q.2 := by
    intro hequal
    apply hqNe
    apply Prod.ext
    · have h := congrArg Prod.fst hequal
      simp only [weightedRadialSource] at h
      exact mul_left_cancel₀ (pow_ne_zero a htau) h
    · have h := congrArg Prod.snd hequal
      simp only [weightedRadialSource] at h
      exact mul_left_cancel₀ htau h
  exact hsourcesNe (hsInjective hfirstMem hsecondMem hvalues)


end OnLeConjecture.DTwo

