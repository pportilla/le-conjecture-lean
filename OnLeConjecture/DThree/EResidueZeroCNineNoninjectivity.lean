/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EResidueZeroCNinePersistence

/-!
# C9 noninjectivity after a power substitution

Persistent zeros in the powered C9 chart give equal representative values at
distinct weighted radial source points. The hard C9 collision therefore
excludes an injective representative for every positive source weight.
-/

public section

noncomputable section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Radial expansions with source weight `a` identify the representative
difference with the C9 rescaled perturbation. -/
theorem representative_difference_eq_eCNineXChartRescaledPerturbation_weighted
    (a : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (tau : ℂ) (q : Fin 3 → ℂ)
    (hfirst : ∀ i,
      representative
          (weightedRadialSource a tau (eCNineXChartFirstPoint q)) i =
        tau ^ degrees i *
          (initialMap (eCNineXChartFirstPoint q) i +
            tau * remainder (tau, eCNineXChartFirstPoint q) i))
    (hsecond : ∀ i,
      representative
          (weightedRadialSource a tau (eCNineXChartSecondPoint q)) i =
        tau ^ degrees i *
          (initialMap (eCNineXChartSecondPoint q) i +
            tau * remainder (tau, eCNineXChartSecondPoint q) i)) :
    ∀ i,
      representative
          (weightedRadialSource a tau (eCNineXChartFirstPoint q)) i -
        representative
          (weightedRadialSource a tau (eCNineXChartSecondPoint q)) i =
      tau ^ degrees i *
        eCNineXChartRescaledPerturbation initialMap remainder (tau, q) i := by
  intro i
  rw [hfirst i, hsecond i]
  simp only [eCNineXChartRescaledPerturbation,
    eCNineXChartInitialDifference, eCNineXChartRemainderDifference,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Persistent C9 zeros contradict injectivity for every positive source
weight. -/
theorem not_neighborhood_injective_of_eCNineWeightedZeros_of_weight
    (a : ℕ) (ha : 0 < a) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (eta z Theta : ℂ) (hz : z ≠ 1)
    (hfirst : HasWeightedRadialExpansionAt a degrees initialMap
      representative remainder (1, eta))
    (hsecond : HasWeightedRadialExpansionAt a degrees initialMap
      representative remainder (z, Theta))
    (hpersist : ∀ (U : Set (ℂ × (Fin 3 → ℂ))),
      U ∈ nhds (0, ![eta, z, Theta]) →
        ∀ᶠ tau in nhds 0,
          ∃ q : Fin 3 → ℂ,
            (tau, q) ∈ U ∧
              eCNineXChartRescaledPerturbation initialMap remainder
                (tau, q) = 0) :
    ¬ ∃ sourceSet ∈ nhds (0 : ℂ × ℂ),
      Set.InjOn representative sourceSet := by
  intro hinjective
  obtain ⟨sourceSet, hsourceSet, hsourceInjective⟩ := hinjective
  let base : Fin 3 → ℂ := ![eta, z, Theta]
  have hfirstLift : Tendsto
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        (s.1, eCNineXChartFirstPoint s.2))
      (nhds (0, base)) (nhds (0, (1, eta))) := by
    have hpoint : AnalyticAt ℂ
        (fun s : ℂ × (Fin 3 → ℂ) ↦
          eCNineXChartFirstPoint s.2) (0, base) := by
      exact (analyticAt_eCNineXChartFirstPoint base).comp_of_eq
        (analyticAt_snd : AnalyticAt ℂ
          (fun s : ℂ × (Fin 3 → ℂ) ↦ s.2) (0, base)) rfl
    have ht := (analyticAt_fst.prod hpoint).continuousAt.tendsto
    simpa [base, eCNineXChartFirstPoint] using ht
  have hsecondLift : Tendsto
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        (s.1, eCNineXChartSecondPoint s.2))
      (nhds (0, base)) (nhds (0, (z, Theta))) := by
    have hpoint : AnalyticAt ℂ
        (fun s : ℂ × (Fin 3 → ℂ) ↦
          eCNineXChartSecondPoint s.2) (0, base) := by
      exact (analyticAt_eCNineXChartSecondPoint base).comp_of_eq
        (analyticAt_snd : AnalyticAt ℂ
          (fun s : ℂ × (Fin 3 → ℂ) ↦ s.2) (0, base)) rfl
    have ht := (analyticAt_fst.prod hpoint).continuousAt.tendsto
    simpa [base, eCNineXChartSecondPoint] using ht
  have hfirstExpansion := hfirstLift.eventually hfirst.expansion
  have hsecondExpansion := hsecondLift.eventually hsecond.expansion
  have hcoordinate (i : Fin 3) : AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) ↦ s.2 i) (0, base) := by
    simpa [Function.comp_def] using
      (AnalyticAt.comp (x := (0, base))
        ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt base)
          analyticAt_snd)
  have hfirstSourceAnalytic : AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a s.1 (eCNineXChartFirstPoint s.2))
      (0, base) := by
    change AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        (s.1 ^ a * 1, s.1 * s.2 0)) (0, base)
    exact ((analyticAt_fst.pow a).mul analyticAt_const).prod
      (analyticAt_fst.mul (hcoordinate 0))
  have hsecondSourceAnalytic : AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a s.1 (eCNineXChartSecondPoint s.2))
      (0, base) := by
    change AnalyticAt ℂ
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        (s.1 ^ a * s.2 1, s.1 * s.2 2)) (0, base)
    exact ((analyticAt_fst.pow a).mul (hcoordinate 1)).prod
      (analyticAt_fst.mul (hcoordinate 2))
  have hfirstSource : Tendsto
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a s.1 (eCNineXChartFirstPoint s.2))
      (nhds (0, base)) (nhds (0 : ℂ × ℂ)) := by
    have ht := hfirstSourceAnalytic.continuousAt.tendsto
    change Tendsto
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a s.1 (eCNineXChartFirstPoint s.2))
      (nhds (0, base)) (nhds ((0, 0) : ℂ × ℂ))
    simpa [base, weightedRadialSource, eCNineXChartFirstPoint,
      zero_pow ha.ne'] using ht
  have hsecondSource : Tendsto
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a s.1 (eCNineXChartSecondPoint s.2))
      (nhds (0, base)) (nhds (0 : ℂ × ℂ)) := by
    have ht := hsecondSourceAnalytic.continuousAt.tendsto
    change Tendsto
      (fun s : ℂ × (Fin 3 → ℂ) ↦
        weightedRadialSource a s.1 (eCNineXChartSecondPoint s.2))
      (nhds (0, base)) (nhds ((0, 0) : ℂ × ℂ))
    simpa [base, weightedRadialSource, eCNineXChartSecondPoint,
      zero_pow ha.ne'] using ht
  have hdirectionTendsto : Tendsto
      (fun s : ℂ × (Fin 3 → ℂ) ↦ s.2 1)
      (nhds (0, base)) (nhds z) := by
    have ht := (hcoordinate 1).continuousAt.tendsto
    simpa [base] using ht
  let conditions : ℂ × (Fin 3 → ℂ) → Prop := fun s ↦
      (∀ i,
        representative
            (weightedRadialSource a s.1
              (eCNineXChartFirstPoint s.2)) i =
          s.1 ^ degrees i *
            (initialMap (eCNineXChartFirstPoint s.2) i +
              s.1 * remainder (s.1, eCNineXChartFirstPoint s.2) i)) ∧
      (∀ i,
        representative
            (weightedRadialSource a s.1
              (eCNineXChartSecondPoint s.2)) i =
          s.1 ^ degrees i *
            (initialMap (eCNineXChartSecondPoint s.2) i +
              s.1 * remainder (s.1, eCNineXChartSecondPoint s.2) i)) ∧
      weightedRadialSource a s.1 (eCNineXChartFirstPoint s.2) ∈
        sourceSet ∧
      weightedRadialSource a s.1 (eCNineXChartSecondPoint s.2) ∈
        sourceSet ∧
      s.2 1 ≠ 1
  have hconditions : ∀ᶠ s in nhds (0, base), conditions s := by
    filter_upwards [hfirstExpansion, hsecondExpansion,
      hfirstSource.eventually hsourceSet,
      hsecondSource.eventually hsourceSet,
      hdirectionTendsto.eventually_ne hz] with
      s hfirstAt hsecondAt hfirstMem hsecondMem hsDirection
    exact ⟨hfirstAt, hsecondAt, hfirstMem, hsecondMem, hsDirection⟩
  have hconditionsSet : {s | conditions s} ∈ nhds (0, base) := hconditions
  have hzero := hpersist {s | conditions s}
    (by simpa [base] using hconditionsSet)
  have hall : ∀ᶠ tau in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
      ∃ q : Fin 3 → ℂ,
        conditions (tau, q) ∧
        eCNineXChartRescaledPerturbation initialMap remainder (tau, q) = 0 ∧
        tau ≠ 0 := by
    filter_upwards [hzero.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with tau htau htauMem
    obtain ⟨q, hcondition, hzeroAt⟩ := htau
    refine ⟨q, hcondition, hzeroAt, ?_⟩
    simpa using htauMem
  obtain ⟨tau, q, hcondition, hzeroAt, htau⟩ := hall.exists
  obtain ⟨hfirstAt, hsecondAt, hfirstMem, hsecondMem, hqDirection⟩ :=
    hcondition
  have hvalues :
      representative
          (weightedRadialSource a tau (eCNineXChartFirstPoint q)) =
        representative
          (weightedRadialSource a tau (eCNineXChartSecondPoint q)) := by
    funext i
    apply sub_eq_zero.mp
    calc
      representative
            (weightedRadialSource a tau (eCNineXChartFirstPoint q)) i -
          representative
            (weightedRadialSource a tau (eCNineXChartSecondPoint q)) i =
        tau ^ degrees i *
          eCNineXChartRescaledPerturbation initialMap remainder
            (tau, q) i :=
          representative_difference_eq_eCNineXChartRescaledPerturbation_weighted
            a degrees initialMap representative remainder tau q
              hfirstAt hsecondAt i
      _ = 0 := by simp [hzeroAt]
  have hsourcesNe :
      weightedRadialSource a tau (eCNineXChartFirstPoint q) ≠
        weightedRadialSource a tau (eCNineXChartSecondPoint q) := by
    intro hequal
    have hfirstCoordinate := congrArg Prod.fst hequal
    have htauPower : tau ^ a ≠ 0 := pow_ne_zero a htau
    simp only [weightedRadialSource, eCNineXChartFirstPoint,
      eCNineXChartSecondPoint, mul_one] at hfirstCoordinate
    have hqOne : q 1 = 1 := by
      apply mul_left_cancel₀ htauPower
      simpa using hfirstCoordinate.symm
    exact hqDirection hqOne
  exact hsourcesNe
    (hsourceInjective hfirstMem hsecondMem hvalues)

/-- A lifted affine C9 collision excludes an injective representative at
every positive source weight. -/
theorem eResidueZeroCNineCollision_not_hasInjectiveRepresentative
    (a : ℕ) (ha : 0 < a) (R : Form ℂ) (N : ℕ)
    (t z T eta Theta : ℂ) (heta : eta ^ a = t)
    (hTheta : Theta ^ a = T)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (hnorm : eCNineUnitDifferenceNorm R ≠ 0)
    (hequations : ECNineEquations 1 t z T)
    (hz : z ≠ 1)
    (hcollision : eCNineXChartInitialDifference
      (eResidueZeroInitialMap a R) ![eta, z, Theta] = 0)
    (hfirst : HasWeightedRadialExpansionAt a (eResidueZeroDegrees a N)
      (eResidueZeroInitialMap a R) representative remainder (1, eta))
    (hsecond : HasWeightedRadialExpansionAt a (eResidueZeroDegrees a N)
      (eResidueZeroInitialMap a R) representative remainder (z, Theta)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  apply not_neighborhood_injective_of_eCNineWeightedZeros_of_weight
    a ha (eResidueZeroDegrees a N) (eResidueZeroInitialMap a R)
      representative remainder eta z Theta hz hfirst hsecond
  intro U hU
  exact eventually_exists_eResidueZeroCNineZero_mem_nhds
    a ha R t z T eta Theta heta hTheta remainder hnorm hequations hz
      hfirst.remainder_analyticAt hsecond.remainder_analyticAt
        hcollision U hU

/-- Weighted order tails above a substituted hard C9 initial form exclude an
injective representative. -/
theorem eCNineHardResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
    {omega : ℂ} (a : ℕ) (ha : 0 < a)
    (homega : IsPrimitiveRoot omega 3)
    (Rzero : ESourceRing ℂ) (coefficient : ℂ) (N : ℕ)
    (hhomogeneous :
      (eSourceCubeSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N).IsHomogeneous N)
    (hc : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (eResidueZeroPolynomialMap a
              (eSourceCubeSubstitutionForm Rzero +
                MvPolynomial.C coefficient * formT ^ N) i) ∈
        Germ.weightedOrderIdeal a
          (eResidueZeroDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  let hardForm := eSourceCubeSubstitutionForm Rzero +
    MvPolynomial.C coefficient * formT ^ N
  have hnorm : eCNineUnitDifferenceNorm hardForm ≠ 0 :=
    eCNineUnitDifferenceNorm_ne_zero homega hardForm Rzero coefficient N
      rfl hc hnotdiv
  obtain ⟨z, t, T, hequations, hdistinct, hordinaryCollision⟩ :=
    eCNineHardNorm_gives_initial_collision homega Rzero coefficient N
      hhomogeneous hc hnotdiv
  have hz : z ≠ 1 :=
    eCNine_direction_ne_one_of_distinct hequations hdistinct
  obtain ⟨eta, heta⟩ := IsAlgClosed.exists_pow_nat_eq t ha
  obtain ⟨Theta, hTheta⟩ := IsAlgClosed.exists_pow_nat_eq T ha
  have hcollision : eCNineXChartInitialDifference
      (eResidueZeroInitialMap a hardForm) ![eta, z, Theta] = 0 := by
    rw [eCNineXChartInitialDifference_eResidueZeroInitialMap]
    apply sub_eq_zero.mpr
    simpa [eCNinePowerChart, eCNineXChartFirstPoint,
      eCNineXChartSecondPoint, heta, hTheta] using hordinaryCollision
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
      a ha (eResidueZeroDegrees a N) (eResidueZeroPolynomialMap a hardForm)
        (eResidueZeroPolynomialMap_isWeightedHomogeneous
          a N hardForm hhomogeneous) representative hanalytic (by
            intro i
            simpa [hardForm] using htail i)
  exact eResidueZeroCNineCollision_not_hasInjectiveRepresentative
    a ha hardForm N t z T eta Theta heta hTheta representative remainder
      hanalytic hzero hnorm hequations hz hcollision
        (by simpa [eResidueZeroInitialMap] using hexpansion (1, eta))
        (by simpa [eResidueZeroInitialMap] using hexpansion (z, Theta))

end OnLeConjecture.DThree
